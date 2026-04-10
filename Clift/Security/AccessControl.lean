-- Access Control Model: Subjects, Objects, Permissions, Policies
--
-- seL4 uses capability-based access control. This module provides a general
-- access control framework that can express capabilities, RBAC, or MLS.
--
-- The key abstraction: an AccessPolicy maps (Subject, Object) pairs to
-- sets of allowed Permissions. A system enforces the policy if every
-- operation checks permissions before acting.
--
-- Design choices:
-- 1. Generic over Subject, Object, Permission types (not hardcoded to
--    capabilities or roles).
-- 2. policy_enforced connects to AbstractSpec: every operation in the spec
--    respects the access policy.
-- 3. The example demonstrates a two-partition system where partitions
--    can only access their own ring buffer.
--
-- Reference: seL4 TOCS 2014, Section 6.2 (access control)
-- Reference: Clift/Security/Properties.lean (integrity uses authorization)

import Clift.Lifting.AbstractSpec

/-! # Access Control Primitives -/

/-- A permission describes what kind of access is allowed.
    This is generic; concrete systems instantiate with their own permissions. -/
class PermissionType (P : Type) where
  decEq : DecidableEq P

/-- An access policy maps (subject, object) pairs to a set of allowed permissions.

    Example: in seL4, a subject is a thread, an object is a kernel object
    (endpoint, frame, CNode), and permissions come from the capability.

    The policy is the INTENDED access control matrix. The enforcement theorem
    proves the C code actually checks this. -/
structure AccessPolicy (Subject Object Permission : Type) where
  /-- Whether subject s has permission p on object o -/
  allowed : Subject → Object → Permission → Prop

namespace AccessPolicy

variable {Subject Object Permission : Type}

/-- A subject has no access to an object if no permission is allowed. -/
def noAccess (pol : AccessPolicy Subject Object Permission)
    (s : Subject) (o : Object) : Prop :=
  ∀ p, ¬ pol.allowed s o p

/-- Two subjects are isolated if neither can access the other's objects. -/
def isolated (pol : AccessPolicy Subject Object Permission)
    (s₁ s₂ : Subject) (objects₁ objects₂ : Object → Prop) : Prop :=
  (∀ o, objects₂ o → pol.noAccess s₁ o) ∧
  (∀ o, objects₁ o → pol.noAccess s₂ o)

end AccessPolicy

/-! # Policy Enforcement -/

/-- An abstract spec enforces an access policy if:
    for every operation, the operation can only modify objects that the
    executing subject has write permission on, and can only read objects
    that the subject has read permission on.

    This is parameterized by:
    - `executor`: which subject executes each operation
    - `accessed`: which objects an operation accesses and with what permission
    - The spec only allows an operation when the policy permits it -/
structure PolicyEnforcement (S : Type) (Op : Type)
    (Subject Object Permission : Type) where
  /-- The abstract specification being enforced -/
  spec : AbstractSpec S Op
  /-- The access policy to enforce -/
  policy : AccessPolicy Subject Object Permission
  /-- Which subject executes each operation -/
  executor : Op → Subject
  /-- Which (object, permission) pairs each operation requires -/
  requires : Op → List (Object × Permission)
  /-- Enforcement: every required permission is allowed by the policy -/
  enforced : ∀ (op : Op),
    (spec.opSpec op).pre = fun s =>
      (∀ pair ∈ requires op,
        policy.allowed (executor op) pair.1 pair.2) ∧
      -- plus any functional preconditions
      spec.inv s

/-- Simplified enforcement check: an operation is permitted iff all its
    required permissions are granted by the policy. This is the runtime
    check that the C code must implement. -/
def operationPermitted {Subject Object Permission : Type}
    (pol : AccessPolicy Subject Object Permission)
    (subj : Subject) (reqs : List (Object × Permission)) : Prop :=
  ∀ pair ∈ reqs, pol.allowed subj pair.1 pair.2

/-- If an operation is not permitted, the abstract spec's precondition
    should be False (the operation should fail/be denied). -/
def policyDeniesUnauthorized {S : Type} {Op : Type}
    {Subject Object Permission : Type}
    (spec : AbstractSpec S Op)
    (pol : AccessPolicy Subject Object Permission)
    (executor : Op → Subject)
    (requires : Op → List (Object × Permission)) : Prop :=
  ∀ (op : Op),
    ¬ operationPermitted pol (executor op) (requires op) →
    ∀ s, spec.inv s → ¬ (spec.opSpec op).pre s

/-! # Example: Two-Partition Ring Buffer System -/

namespace TwoPartitionExample

/-- Two partitions (subjects). -/
inductive Partition where
  | partA
  | partB
  deriving DecidableEq

/-- Objects: each partition has its own ring buffer. -/
inductive Buffer where
  | bufA  -- partition A's buffer
  | bufB  -- partition B's buffer
  deriving DecidableEq

/-- Permissions. -/
inductive Perm where
  | read
  | write
  deriving DecidableEq

instance : PermissionType Perm where
  decEq := inferInstance

/-- Access policy: each partition can only access its own buffer. -/
def twoPartPolicy : AccessPolicy Partition Buffer Perm where
  allowed := fun subj obj _ =>
    match subj, obj with
    | .partA, .bufA => True
    | .partB, .bufB => True
    | _, _ => False

/-- Partition A cannot access buffer B. -/
theorem partA_no_bufB : twoPartPolicy.noAccess .partA .bufB := by
  intro p; exact id

/-- Partition B cannot access buffer A. -/
theorem partB_no_bufA : twoPartPolicy.noAccess .partB .bufA := by
  intro p; exact id

/-- The two partitions are isolated. -/
theorem partitions_isolated :
    twoPartPolicy.isolated .partA .partB
      (fun o => o = .bufA) (fun o => o = .bufB) := by
  constructor
  · intro o h_b; subst h_b; exact partA_no_bufB
  · intro o h_a; subst h_a; exact partB_no_bufA

/-- Abstract state: two independent queues. -/
structure TwoQueueState where
  queueA : List Nat
  queueB : List Nat
  capacityA : Nat
  capacityB : Nat

/-- Operations: push/pop/size on each buffer, tagged with the executing partition. -/
inductive TwoQueueOp where
  | pushA (val : Nat)   -- partition A pushes to buffer A
  | popA                -- partition A pops from buffer A
  | sizeA               -- partition A reads size of buffer A
  | pushB (val : Nat)   -- partition B pushes to buffer B
  | popB                -- partition B pops from buffer B
  | sizeB               -- partition B reads size of buffer B

/-- Which partition executes each operation. -/
def twoQueueExecutor : TwoQueueOp → Partition
  | .pushA _ | .popA | .sizeA => .partA
  | .pushB _ | .popB | .sizeB => .partB

/-- Which permissions each operation requires. -/
def twoQueueRequires : TwoQueueOp → List (Buffer × Perm)
  | .pushA _ => [(.bufA, .write)]
  | .popA    => [(.bufA, .write)]
  | .sizeA   => [(.bufA, .read)]
  | .pushB _ => [(.bufB, .write)]
  | .popB    => [(.bufB, .write)]
  | .sizeB   => [(.bufB, .read)]

/-- All operations in this system are permitted by the policy. -/
theorem all_ops_permitted :
    ∀ (op : TwoQueueOp),
      operationPermitted twoPartPolicy (twoQueueExecutor op) (twoQueueRequires op) := by
  intro op
  cases op <;> intro pair h_mem <;> simp [twoQueueRequires] at h_mem <;>
    subst h_mem <;> trivial

/-- Abstract spec for the two-queue system. -/
def twoQueueSpec : AbstractSpec TwoQueueState TwoQueueOp where
  init := fun s => s.queueA = [] ∧ s.queueB = [] ∧ s.capacityA > 0 ∧ s.capacityB > 0
  opSpec := fun op => match op with
    | .pushA val => {
        pre := fun s => s.queueA.length < s.capacityA
        post := fun s s' => s'.queueA = s.queueA ++ [val] ∧ s'.queueB = s.queueB ∧
                            s'.capacityA = s.capacityA ∧ s'.capacityB = s.capacityB
      }
    | .popA => {
        pre := fun s => s.queueA ≠ []
        post := fun s s' =>
          ∃ v rest, s.queueA = v :: rest ∧ s'.queueA = rest ∧ s'.queueB = s.queueB ∧
          s'.capacityA = s.capacityA ∧ s'.capacityB = s.capacityB
      }
    | .sizeA => {
        pre := fun _ => True
        post := fun s s' => s' = s
      }
    | .pushB val => {
        pre := fun s => s.queueB.length < s.capacityB
        post := fun s s' => s'.queueB = s.queueB ++ [val] ∧ s'.queueA = s.queueA ∧
                            s'.capacityA = s.capacityA ∧ s'.capacityB = s.capacityB
      }
    | .popB => {
        pre := fun s => s.queueB ≠ []
        post := fun s s' =>
          ∃ v rest, s.queueB = v :: rest ∧ s'.queueB = rest ∧ s'.queueA = s.queueA ∧
          s'.capacityA = s.capacityA ∧ s'.capacityB = s.capacityB
      }
    | .sizeB => {
        pre := fun _ => True
        post := fun s s' => s' = s
      }
  inv := fun s =>
    s.queueA.length ≤ s.capacityA ∧ s.queueB.length ≤ s.capacityB ∧
    s.capacityA > 0 ∧ s.capacityB > 0

/-- Partition A's operations don't modify partition B's queue.
    This is a concrete security property proved on the abstract spec. -/
theorem partA_doesnt_touch_B (op : TwoQueueOp) (s s' : TwoQueueState)
    (_h_inv : twoQueueSpec.inv s)
    (_h_pre : (twoQueueSpec.opSpec op).pre s)
    (h_post : (twoQueueSpec.opSpec op).post s s')
    (h_exec : twoQueueExecutor op = .partA) :
    s'.queueB = s.queueB := by
  cases op with
  | pushA val => exact h_post.2.1
  | popA =>
    obtain ⟨_, _, _, _, h_qb, _, _⟩ := h_post
    exact h_qb
  | sizeA => exact congrArg TwoQueueState.queueB h_post
  | pushB _ => simp [twoQueueExecutor] at h_exec
  | popB => simp [twoQueueExecutor] at h_exec
  | sizeB => simp [twoQueueExecutor] at h_exec

/-- Partition B's operations don't modify partition A's queue. -/
theorem partB_doesnt_touch_A (op : TwoQueueOp) (s s' : TwoQueueState)
    (_h_inv : twoQueueSpec.inv s)
    (_h_pre : (twoQueueSpec.opSpec op).pre s)
    (h_post : (twoQueueSpec.opSpec op).post s s')
    (h_exec : twoQueueExecutor op = .partB) :
    s'.queueA = s.queueA := by
  cases op with
  | pushB val => exact h_post.2.1
  | popB =>
    obtain ⟨_, _, _, _, h_qa, _, _⟩ := h_post
    exact h_qa
  | sizeB => exact congrArg TwoQueueState.queueA h_post
  | pushA _ => simp [twoQueueExecutor] at h_exec
  | popA => simp [twoQueueExecutor] at h_exec
  | sizeA => simp [twoQueueExecutor] at h_exec

end TwoPartitionExample

/-! # Documentation

## Access Control Models

This framework supports multiple access control paradigms:

### Capability-Based (seL4 style)
- Subject = Thread ID
- Object = Kernel object (endpoint, frame, CNode, etc.)
- Permission = Capabilities held by the thread
- Policy = Capability derivation tree

### Role-Based (RBAC)
- Subject = Role (admin, user, auditor)
- Object = Resource (file, queue, device)
- Permission = Actions allowed per role

### Mandatory (MLS/Bell-LaPadula)
- Subject = Security clearance level
- Object = Classification level
- Permission = Read/Write with "no read up, no write down"

The framework is generic enough for all three. Concrete systems choose
their types and instantiate the AccessPolicy.

## Workflow

1. Define Subject, Object, Permission types
2. Define the AccessPolicy (who can do what to what)
3. Define which subject executes each operation
4. Define which permissions each operation requires
5. Prove all operations are within policy (or that the spec denies unauthorized ops)
6. Use integrity/confidentiality theorems from Properties.lean
-/
