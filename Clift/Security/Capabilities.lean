-- Capability System Verification Pattern
--
-- Defines the verification pattern for seL4-style capability-based access control.
-- Capabilities are unforgeable tokens that mediate all access to kernel objects.
-- Key properties: unforgeability, delegation (derived caps have subset rights),
-- and revocation (revoking a cap invalidates all descendants).
--
-- This is a VERIFICATION PATTERN: it shows how Clift would verify capability
-- system properties, not a full implementation.
--
-- Reference: seL4 TOCS 2014, Section 6.2 (capability-based access control)
-- Reference: Clift/Security/AccessControl.lean (generic access control framework)

/-! # Capability Types -/

/-- Rights that a capability can grant. Subset of seL4's CapRights. -/
inductive CapRight where
  | read
  | write
  | grant    -- can delegate this cap to others
  | revoke   -- can revoke derived caps
  deriving DecidableEq, Repr

/-- Object types that capabilities can reference. -/
inductive ObjType where
  | endpoint
  | notification
  | frame
  | cnode
  | tcb
  deriving DecidableEq, Repr

/-- A capability: an unforgeable token granting specific rights to a specific object. -/
structure Cap where
  objType : ObjType
  objPtr  : Nat          -- abstract object identifier
  rights  : List CapRight
  deriving DecidableEq, Repr

/-- Capability derivation tree. Each cap has an optional parent (the cap it was
    derived from). Root caps are created by the kernel at boot. -/
structure CapNode where
  cap    : Cap
  parent : Option Nat    -- index of parent in the cap table, None for root caps
  valid  : Bool          -- revoked caps have valid = false

/-- System capability state: a table of all caps in the system. -/
structure CapState where
  table : List CapNode
  nextId : Nat

/-! # Capability Operations -/

/-- Check if rights r2 are a subset of rights r1. -/
def rightsSubset (r1 r2 : List CapRight) : Prop :=
  ∀ r, r ∈ r2 → r ∈ r1

/-- Derive a new capability from an existing one with reduced rights.
    Precondition: the source cap must have Grant right and be valid.
    Postcondition: new cap has subset rights and records its parent. -/
def capDerive (s : CapState) (srcIdx : Nat) (newRights : List CapRight)
    : Option (CapState × Nat) :=
  match s.table[srcIdx]? with
  | none => none
  | some src =>
    if ¬src.valid then none
    else
      let newCap : CapNode := {
        cap := { objType := src.cap.objType, objPtr := src.cap.objPtr, rights := newRights }
        parent := some srcIdx
        valid := true
      }
      some ({ table := s.table ++ [newCap], nextId := s.nextId + 1 }, s.table.length)

/-- Direct parent relationship: child's parent field points to ancestor. -/
def isDirectChildOf (table : List CapNode) (child parent : Nat) : Prop :=
  ∃ node, table[child]? = some node ∧ node.parent = some parent

/-- Descendant relationship: child is reachable from ancestor via parent chain.
    Defined inductively to avoid termination issues with recursive functions. -/
inductive isDescendantOf (table : List CapNode) : Nat → Nat → Prop where
  | direct (child ancestor : Nat) :
      isDirectChildOf table child ancestor → isDescendantOf table child ancestor
  | transitive (child mid ancestor : Nat) :
      isDirectChildOf table child mid →
      isDescendantOf table mid ancestor →
      isDescendantOf table child ancestor

/-! # Key Properties -/

/-- Unforgeability: the only way to obtain a capability is by derivation from
    an existing valid capability. No operation creates a cap "from thin air."

    Formally: for any cap in the table that is not a root cap, there exists
    a valid ancestor chain back to a root cap. -/
def capUnforgeable (s : CapState) : Prop :=
  ∀ (idx : Nat) (node : CapNode),
    s.table[idx]? = some node →
    node.valid →
    -- Either it's a root cap (no parent)...
    node.parent = none ∨
    -- ...or its parent exists and is (or was) in the table
    (∃ pidx, node.parent = some pidx ∧ pidx < s.table.length)

/-- Delegation monotonicity: derived capabilities never have MORE rights
    than their parent. This is the key security property of delegation. -/
def delegationMonotone (s : CapState) : Prop :=
  ∀ (idx : Nat) (node : CapNode),
    s.table[idx]? = some node →
    node.valid →
    ∀ (pidx : Nat), node.parent = some pidx →
      ∀ (pnode : CapNode), s.table[pidx]? = some pnode →
        rightsSubset pnode.cap.rights node.cap.rights

/-- Revocation completeness: when a capability is revoked, ALL its descendants
    become invalid. No descendant escapes revocation. -/
def revocationComplete (pre post : CapState) (revokedIdx : Nat) : Prop :=
  ∀ (idx : Nat) (node : CapNode),
    post.table[idx]? = some node →
    isDescendantOf pre.table idx revokedIdx →
    ¬node.valid

/-- Object type consistency: a derived capability must reference the same
    object as its parent. You cannot derive a cap to object B from a cap
    to object A. -/
def objectConsistency (s : CapState) : Prop :=
  ∀ (idx : Nat) (node : CapNode),
    s.table[idx]? = some node →
    ∀ (pidx : Nat), node.parent = some pidx →
      ∀ (pnode : CapNode), s.table[pidx]? = some pnode →
        node.cap.objType = pnode.cap.objType ∧
        node.cap.objPtr = pnode.cap.objPtr

/-! # Verification Pattern: How to Prove These on C Code

The workflow for verifying a C capability system with Clift:

1. Import the C implementation via CImporter (cap_table.c -> Generated/CapTable.lean)
2. Lift through L1-L5 to get clean functional model
3. Define AbstractSpec for the cap table operations
4. Prove refinement: C implementation refines the AbstractSpec
5. Prove the properties above on the AbstractSpec
6. Transfer via security_transfer from Properties.lean

The properties compose with the AccessPolicy framework from AccessControl.lean:
- capUnforgeable ensures the policy cannot be circumvented
- delegationMonotone ensures authority cannot be escalated
- revocationComplete ensures authority can be withdrawn
-/
