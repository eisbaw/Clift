-- Authority Confinement Verification Pattern
--
-- Defines the verification pattern for authority confinement: no operation
-- can create or escalate authority beyond what the caller already holds.
-- This is THE property that makes capability systems secure, distinct from
-- both access control (policy checking) and noninterference (information flow).
--
-- This is a VERIFICATION PATTERN, not a full implementation.
--
-- Reference: seL4 TOCS 2014, Section 6.4 (authority confinement)
-- Reference: Dennis & Van Horn, "Programming Semantics for Multiprogrammed
--            Computations", 1966 (original capability concept)

/-! # Authority Model -/

/-- A subject (thread, process, domain) that can hold authority. -/
structure Subject where
  id : Nat
  deriving DecidableEq, Repr

/-- A capability token representing authority over an object with specific rights. -/
structure CapToken where
  objectId : Nat
  rights   : List Nat    -- abstract right identifiers
  deriving DecidableEq, Repr

/-- The authority of a subject: the set of capabilities it holds or can reach
    through delegation chains. -/
def Authority := Subject → List CapToken

/-- Authority ordering: subject A has at least as much authority as subject B
    if every capability reachable by B is also reachable by A. -/
def authorityLeq (auth : Authority) (a b : Subject) : Prop :=
  ∀ cap, cap ∈ auth b → cap ∈ auth a

/-! # System Operations -/

/-- An operation performed by a subject. -/
structure SysOp where
  actor   : Subject
  opType  : Nat       -- abstract operation identifier

/-- System state: who holds what authority. -/
structure AuthState where
  authority : Authority
  grantable : Subject → List CapToken   -- which caps can be granted to others

/-- Compute the authority of a subject in a given state. -/
def authorityOf (s : AuthState) (subj : Subject) : List CapToken :=
  s.authority subj

/-! # Key Properties -/

/-- Authority confinement: after any operation, no subject has MORE authority
    than was reachable in the system before the operation.

    Formally: for any operation that transforms state s to s', and any subject,
    every capability the subject holds in s' was already reachable from some
    subject in s. No new authority is created from nothing. -/
def confinement (pre post : AuthState) (op : SysOp) : Prop :=
  ∀ (subj : Subject) (cap : CapToken),
    cap ∈ authorityOf post subj →
    -- The cap was already somewhere in the system
    ∃ (src : Subject), cap ∈ authorityOf pre src

/-- Monotonicity: an operation by subject A cannot give subject B more authority
    than A itself has. You cannot grant what you don't have. -/
def monotonicity (pre post : AuthState) (op : SysOp) : Prop :=
  ∀ (subj : Subject) (cap : CapToken),
    cap ∈ authorityOf post subj →
    cap ∉ authorityOf pre subj →
    -- If subj gained a new cap, the actor must have had it and it must be grantable
    cap ∈ authorityOf pre op.actor ∧
    cap ∈ pre.grantable op.actor

/-- No authority leak: authority is only transferred when the actor explicitly
    performs a Grant operation. Ordinary operations (read, write, invoke)
    do not leak authority. -/
def noAuthorityLeak (pre post : AuthState) (op : SysOp) (isGrant : Bool) : Prop :=
  isGrant = false →
  ∀ (subj : Subject) (cap : CapToken),
    cap ∈ authorityOf post subj →
    cap ∈ authorityOf pre subj

/-- Authority diminishment: revoking a capability reduces authority.
    After revocation, the revoked cap is no longer reachable by anyone
    in the revocation's subtree. -/
def diminishment (pre post : AuthState) (revokedCap : CapToken)
    (affectedSubjects : List Subject) : Prop :=
  ∀ (subj : Subject),
    subj ∈ affectedSubjects →
    revokedCap ∉ authorityOf post subj

/-- Composition with access policy: if the access policy says subject S
    cannot access object O, then S does not hold any capability for O.
    This connects authority confinement to the AccessControl framework. -/
def authorityMatchesPolicy (s : AuthState)
    (policyDenied : Subject → Nat → Prop) : Prop :=
  ∀ (subj : Subject) (objId : Nat),
    policyDenied subj objId →
    ∀ (cap : CapToken), cap ∈ authorityOf s subj → cap.objectId ≠ objId

/-! # Verification Pattern

To verify authority confinement in C code with Clift:

1. Import capability management C code (cap table, CNode operations)
2. Define AbstractSpec with operations: invoke, grant, revoke, copy, mint
3. For each operation, prove confinement:
   - invoke: does not create new caps
   - grant: only transfers caps the actor holds
   - revoke: removes caps from the subtree
   - copy: duplicates existing caps (no new authority)
   - mint: creates a cap with SUBSET rights of an existing cap
4. Prove monotonicity: each operation respects the authority ordering
5. Prove noAuthorityLeak: non-grant operations preserve authority distribution
6. Compose with AccessControl.lean to show the full security chain:
   policy -> enforcement -> confinement -> no escalation

This property is what distinguishes a capability system from a simple ACL:
capabilities are not just checked, they are provably confined.
-/
