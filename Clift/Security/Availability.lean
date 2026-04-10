-- Availability Verification Pattern
--
-- Defines the verification pattern for availability: proving that no
-- unauthorized application can deny service by exhausting kernel resources.
-- This is one of seL4's three security pillars (integrity, confidentiality,
-- availability).
--
-- The existing availability definition in Properties.lean is a generic predicate.
-- This module provides the concrete resource model and proof patterns.
--
-- This is a VERIFICATION PATTERN, not a full implementation.
--
-- Reference: seL4 TOCS 2014, Section 6.5 (availability)

/-! # Resource Model -/

/-- Domain identifier (partition, process group). -/
structure DomainId where
  val : Nat
  deriving DecidableEq, Repr

/-- Resource types that can be exhausted. -/
inductive ResourceType where
  | memory       -- kernel heap / object allocation
  | cpuTime      -- processor time slices
  | endpoints    -- IPC endpoints
  | notifications -- notification objects
  | capSlots     -- capability table entries
  deriving DecidableEq, Repr

/-- Resource budget: how much of each resource a domain is allowed to use. -/
structure ResourceBudget where
  memory       : Nat    -- bytes
  cpuTime      : Nat    -- time slices per scheduling period
  endpoints    : Nat    -- max concurrent endpoints
  notifications : Nat   -- max concurrent notifications
  capSlots     : Nat    -- max capability slots

/-- Current resource usage for a domain. -/
structure ResourceUsage where
  memory       : Nat
  cpuTime      : Nat
  endpoints    : Nat
  notifications : Nat
  capSlots     : Nat

/-- System resource state: per-domain budgets and usage. -/
structure ResourceState where
  budgets : DomainId → ResourceBudget
  usage   : DomainId → ResourceUsage

/-! # Resource Accounting Operations -/

/-- Compute total usage of a specific resource type for a domain. -/
def resourceUsage (s : ResourceState) (d : DomainId) (r : ResourceType) : Nat :=
  match r with
  | .memory        => (s.usage d).memory
  | .cpuTime       => (s.usage d).cpuTime
  | .endpoints     => (s.usage d).endpoints
  | .notifications => (s.usage d).notifications
  | .capSlots      => (s.usage d).capSlots

/-- Get the budget for a specific resource type. -/
def resourceBudget (s : ResourceState) (d : DomainId) (r : ResourceType) : Nat :=
  match r with
  | .memory        => (s.budgets d).memory
  | .cpuTime       => (s.budgets d).cpuTime
  | .endpoints     => (s.budgets d).endpoints
  | .notifications => (s.budgets d).notifications
  | .capSlots      => (s.budgets d).capSlots

/-! # Key Properties -/

/-- Availability guarantee: for every domain, resource usage never exceeds
    the allocated budget. This is the core availability property. -/
def availabilityGuarantee (s : ResourceState) : Prop :=
  ∀ (d : DomainId) (r : ResourceType),
    resourceUsage s d r ≤ resourceBudget s d r

/-- Cross-domain isolation: operations by domain A do not increase domain B's
    resource usage. Each domain's resources are accounted independently. -/
def crossDomainIsolation (pre post : ResourceState) (actor : DomainId) : Prop :=
  ∀ (d : DomainId) (r : ResourceType),
    d ≠ actor →
    resourceUsage post d r ≤ resourceUsage pre d r

/-- Bounded resource consumption: each operation consumes at most a bounded
    amount of resources. This prevents a single operation from exhausting
    the entire budget. -/
def boundedConsumption (pre post : ResourceState) (actor : DomainId)
    (maxDelta : ResourceType → Nat) : Prop :=
  ∀ (r : ResourceType),
    resourceUsage post actor r ≤ resourceUsage pre actor r + maxDelta r

/-- Budget preservation: operations never increase budgets.
    Budgets are set at system configuration time and don't change at runtime.
    (seL4 uses static partition scheduling for this.) -/
def budgetPreserved (pre post : ResourceState) : Prop :=
  ∀ (d : DomainId) (r : ResourceType),
    resourceBudget post d r = resourceBudget pre d r

/-- Resource freeing: when resources are released, the usage decreases.
    This ensures that a domain can reclaim its budget by freeing objects. -/
def resourceFreeable (pre post : ResourceState) (actor : DomainId)
    (freed : ResourceType → Nat) : Prop :=
  ∀ (r : ResourceType),
    resourceUsage post actor r + freed r = resourceUsage pre actor r

/-- Availability transfer: connects to the generic availability predicate
    in Properties.lean. Given our concrete resource model, show it satisfies
    the abstract availability property shape. -/
def availabilityConnectsToFramework
    (s : ResourceState)
    (h : availabilityGuarantee s) : Prop :=
  -- For every domain, usage ≤ budget (which is exactly what Properties.availability states)
  ∀ (d : DomainId) (r : ResourceType),
    resourceUsage s d r ≤ resourceBudget s d r

/-! # Verification Pattern

To verify availability in C kernel code with Clift:

1. Import resource management C code (object allocator, scheduler, cap table)
2. Define AbstractSpec with operations:
   - allocate(domain, resourceType) -> object
   - free(domain, object)
   - scheduleTick(domain)
3. For each operation, prove:
   a. availabilityGuarantee is preserved (usage stays within budget)
   b. crossDomainIsolation: other domains' usage is unaffected
   c. boundedConsumption: single-operation delta is bounded
4. Prove budgetPreserved: no runtime operation changes budgets
5. Prove resourceFreeable: freeing objects recovers budget

seL4's approach to availability:
- Static partition scheduling: CPU time is divided into fixed-length domains
- Untyped memory: all kernel memory comes from typed objects derived from
  untyped memory caps. Each domain's memory is bounded by its untyped caps.
- The kernel itself uses O(1) memory for operations (no unbounded allocation)

The key insight: availability follows from resource accounting + the property
that each kernel operation has bounded resource consumption. The kernel never
allocates memory on behalf of a user without deducting from that user's budget.
-/
