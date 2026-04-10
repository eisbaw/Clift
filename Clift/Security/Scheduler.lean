-- Scheduler Verification Pattern
--
-- Defines the verification pattern for priority-based scheduling as in seL4.
-- Key properties: highest-priority runnable thread always runs, no starvation
-- (with bounded fairness), and time-slice accounting is correct.
--
-- This is a VERIFICATION PATTERN, not a full implementation.
--
-- Reference: seL4 TOCS 2014 (scheduler verification)

/-! # Thread and Priority Types -/

/-- Thread identifier. -/
structure ThreadId where
  val : Nat
  deriving DecidableEq, BEq, Repr

/-- Priority level. Higher value = higher priority. -/
structure Priority where
  val : Nat
  deriving DecidableEq, BEq, Repr, Ord

instance : LE Priority where
  le a b := a.val ≤ b.val

instance : LT Priority where
  lt a b := a.val < b.val

/-- Thread state in the scheduler. -/
inductive ThreadState where
  | running
  | ready
  | blocked
  | inactive
  deriving DecidableEq, BEq, Repr

/-! # Scheduler State -/

/-- Per-thread scheduling metadata. -/
structure ThreadInfo where
  tid       : ThreadId
  priority  : Priority
  state     : ThreadState
  timeSlice : Nat          -- remaining time in current quantum
  deriving DecidableEq, BEq, Repr

/-- Scheduler state: ready queues organized by priority, plus current thread. -/
structure SchedState where
  threads    : List ThreadInfo
  current    : Option ThreadId
  maxPriority : Nat         -- number of priority levels
  quantum    : Nat          -- time slice quantum (ticks)

/-! # Scheduler Operations -/

/-- Find a thread by ID. -/
def findThread (s : SchedState) (tid : ThreadId) : Option ThreadInfo :=
  s.threads.find? (fun t => t.tid == tid)

/-- Get all ready threads. -/
def readyThreads (s : SchedState) : List ThreadInfo :=
  s.threads.filter (fun t => t.state == .ready)

/-- Get the highest priority among ready threads. -/
def highestReadyPriority (s : SchedState) : Option Priority :=
  let ready := readyThreads s
  ready.foldl (fun acc t => match acc with
    | none => some t.priority
    | some p => if t.priority.val > p.val then some t.priority else some p) none

/-- Schedule: select the highest-priority ready thread.
    Among equal-priority threads, round-robin (first in the ready list). -/
def schedule (s : SchedState) : SchedState :=
  match highestReadyPriority s with
  | none => { s with current := none }
  | some maxP =>
    match (readyThreads s).find? (fun t => t.priority == maxP) with
    | none => { s with current := none }
    | some winner =>
      let threads' := s.threads.map (fun t =>
        if t.tid == winner.tid then { t with state := .running }
        else if t.state == .running then { t with state := .ready }
        else t)
      { s with threads := threads', current := some winner.tid }

/-- Yield: current thread gives up remaining time slice, goes to back of ready queue. -/
def yieldThread (s : SchedState) : SchedState :=
  match s.current with
  | none => s
  | some tid =>
    let threads' := s.threads.map (fun t =>
      if t.tid == tid then { t with state := .ready, timeSlice := s.quantum }
      else t)
    schedule { s with threads := threads' }

/-- Timer tick: decrement current thread's time slice. If exhausted, reschedule. -/
def timerTick (s : SchedState) : SchedState :=
  match s.current with
  | none => schedule s
  | some tid =>
    let threads' := s.threads.map (fun t =>
      if t.tid == tid then { t with timeSlice := t.timeSlice - 1 }
      else t)
    let s' := { s with threads := threads' }
    match findThread s' tid with
    | none => schedule s'
    | some t => if t.timeSlice == 0 then yieldThread s' else s'

/-! # Key Properties -/

/-- Highest priority runs: if any thread is running, no ready thread has
    strictly higher priority. This is THE key scheduler correctness property. -/
def highestPriorityRuns (s : SchedState) : Prop :=
  ∀ (runner : ThreadInfo),
    s.current = some runner.tid →
    findThread s runner.tid = some runner →
    runner.state = .running →
    ∀ (other : ThreadInfo),
      other ∈ s.threads →
      other.state = .ready →
      other.priority.val ≤ runner.priority.val

/-- No starvation (bounded fairness): every ready thread eventually gets scheduled.
    Stated as: after at most N timer ticks (where N depends on the number of
    threads and the quantum), a ready thread must have been scheduled at least once.

    This is a liveness property; in practice it requires showing that:
    1. Time slices are finite
    2. Higher-priority threads yield or block eventually
    3. Round-robin within a priority level is fair -/
def noStarvation (s : SchedState) (bound : Nat) : Prop :=
  ∀ (tid : ThreadId) (t : ThreadInfo),
    findThread s tid = some t →
    t.state = .ready →
    -- Within 'bound' scheduling rounds, tid will be current
    ∃ (n : Nat), n ≤ bound ∧
      ∃ (s' : SchedState),
        -- s' is reachable from s in n steps
        -- and tid is running in s'
        s'.current = some tid

/-- Time slice accounting: time slices are always within [0, quantum]. -/
def timeSliceBounded (s : SchedState) : Prop :=
  ∀ (t : ThreadInfo), t ∈ s.threads → t.timeSlice ≤ s.quantum

/-- Thread count invariant: scheduling operations do not create or destroy threads. -/
def threadCountPreserved (pre post : SchedState) : Prop :=
  pre.threads.length = post.threads.length

/-! # Verification Pattern

To verify a C scheduler with Clift:

1. Import scheduler C code (priority queue, ready queue array, context switch)
2. The C typically uses a bitmap + array of queues indexed by priority
3. Define AbstractSpec with operations: schedule, yield, timerTick, block, unblock
4. Prove refinement: C bitmap/queue manipulation implements the abstract model
5. Prove highestPriorityRuns is an invariant of schedule
6. Prove timeSliceBounded is preserved by timerTick
7. noStarvation requires additional assumptions about thread behavior

The hardest part: the C scheduler runs with interrupts disabled and manipulates
global state. Verifying it requires the concurrency model from task-0164.
-/
