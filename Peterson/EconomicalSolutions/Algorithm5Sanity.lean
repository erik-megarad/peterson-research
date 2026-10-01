import Peterson.EconomicalSolutions.Algorithm5Invariant

namespace EconomicalSolutions.Algorithm5

/-- One explicit inhabitant. All proofs above quantify over every configuration. -/
def ascendingConfig (n : Nat) (positive : 0 < n) : Config n where
  tournament := Algorithm2.ascendingConfig n positive
  order := fun p => (List.finRange n).filter (fun q => q != p)
  nodup := by intro p; exact List.Nodup.filter _ (List.nodup_finRange _)
  complete := by intro p q; simp

/-- The full atomic sample at a real or padded tournament leaf. Projection
commutes with sampling, so reusing Algorithm 2 creates no field-read split. -/
def visible {n : Nat} (s : State n) (j : Algorithm2.Leaf n) : Value :=
  if h : j.val < n then (s ⟨j.val, h⟩).value else dead

theorem visible_projection {n : Nat} (s : State n) (j : Algorithm2.Leaf n) :
    (visible s j).tournament = Algorithm2.visible (project s) j := by
  simp only [visible, Algorithm2.visible]
  split <;> rfl

/-- Actual peer and own reads, including whole-value reads whose unused
component is discarded. Metadata does not add an execution step or state. -/
def sample {n : Nat} (s : State n) : Command n → Option Value
  | .run p => match (s p).pc with
      | .request | .acquire => match (s p).tournamentPC with
          | .scan _ _ (j :: _) => some (visible s j)
          | .self2 _ | .waitSelf _ _ => some (s p).value
          | _ => none
      | .capacity (q :: _) _ | .choose (q :: _) _ | .absent (q :: _) _ => some (s q).value
      | .test | .prepare _ => some (s p).value
      | _ => none
  | _ => none

theorem queue_read_whole {n : Nat} (s : State n) (p q : Proc n) (rest : List (Proc n))
    (k : Int) (pc : (s p).pc = .absent (q :: rest) k) :
    sample s (.run p) = some (s q).value := by simp [sample, pc]

/-- An arbitrary cached write executes, even in an invented unreachable
state with a colliding peer. Safety is therefore not hidden in a guard. -/
theorem decrement_has_no_priority_guard {n : Nat} (cfg : Config n) (s : State n)
    (p : Proc n) (v : Int) (pc : (s p).pc = .decrement v) :
    next cfg s (.run p) = some (setLocal s p
      { s p with pc := .test, value := ⟨Algorithm2.dead, v⟩ }) := by
  simp [next, ordinary, pc]

theorem enqueue_has_no_range_guard {n : Nat} (cfg : Config n) (s : State n)
    (p : Proc n) (v : Int) (pc : (s p).pc = .enqueue v) :
    next cfg s (.run p) = some (setLocal s p
      { s p with pc := .complete, value := ⟨(s p).value.tournament, v⟩ }) := by
  simp [next, ordinary, pc]

theorem failure_discards_cached_write {n : Nat} (cfg : Config n) (s : State n)
    (p : Proc n) (v : Int) (pc : (s p).pc = .decrement v) :
    next cfg s (.fail p) = some (setLocal s p ⟨.down, .down, dead⟩) ∧
    next cfg (setLocal s p ⟨.down, .down, dead⟩) (.run p) = none ∧
    next cfg (setLocal s p ⟨.down, .down, dead⟩) (.restart p) =
      some (setLocal (setLocal s p ⟨.down, .down, dead⟩) p ⟨.idle, .idle, dead⟩) := by
  simp [next, ordinary, pc]

def singletonRun (steps : Nat) : Option (State 1) :=
  (List.replicate steps (Algorithm2.Command.run (0 : Proc 1))).foldl
    (fun current command => current.bind (fun s => next (ascendingConfig 1 (by decide)) s command))
    (some (initial 1))

def singletonView (steps : Nat) : Option (PC 1 × Algorithm2.PC 1 × Value) :=
  (singletonRun steps).map fun s => ((s 0).pc, (s 0).tournamentPC, (s 0).value)

/-- Outer request precedes tournament request, and singleton ownership is
private even when its visible tournament field remains dead. -/
theorem singleton_request_and_ownership :
    singletonView 1 = some (.request, .idle, dead) ∧
    singletonView 2 = some (.acquire, .enter, dead) ∧
    singletonView 3 = some (.capacity [] (-1), .cs, dead) := by decide

/-- Enqueue, local completion, tournament release, zero-test, outer entry,
outer completion and normal release remain separately delayable. -/
theorem singleton_passage :
    singletonView 5 = some (.enqueue 0, .cs, dead) ∧
    singletonView 6 = some (.complete, .cs, ⟨Algorithm2.dead, 0⟩) ∧
    singletonView 7 = some (.depart, .release, ⟨Algorithm2.dead, 0⟩) ∧
    singletonView 8 = some (.test, .idle, ⟨Algorithm2.dead, 0⟩) ∧
    singletonView 10 = some (.cs, .idle, ⟨Algorithm2.dead, 0⟩) ∧
    singletonView 11 = some (.release, .idle, ⟨Algorithm2.dead, 0⟩) ∧
    singletonView 12 = some (.idle, .idle, dead) := by decide

def twoRun (commands : List (Command 2)) : Option (State 2) :=
  commands.foldl
    (fun current command => current.bind (fun s => next (ascendingConfig 2 (by decide)) s command))
    (some (initial 2))

def twoView (commands : List (Command 2)) : Option (PC 2 × Int × PC 2 × Int) :=
  (twoRun commands).map fun s => ((s 0).pc, priority s 0, (s 1).pc, priority s 1)

def contention : List (Command 2) :=
  List.replicate 22 (.run 0) ++ List.replicate 22 (.run 1)

/-- A real two-process execution queues a second requester behind a delayed
critical occupant. Reset, restart and delay do not resurrect an old episode;
a completed absence scan authorizes a separate delayed decrement. -/
theorem two_process_failure_and_delay :
    twoView contention = some (.cs, 0, .absent [0] 1, 1) ∧
    twoView (contention ++ [.fail 0] ++ List.replicate 3 (.run 1)) =
      some (.down, -1, .decrement 0, 1) ∧
    twoView (contention ++ [.fail 0] ++ List.replicate 3 (.run 1) ++
      [.restart 0, .run 0, .stutter] ++ List.replicate 3 (.run 1)) =
      some (.request, -1, .cs, 0) := by decide

end EconomicalSolutions.Algorithm5

#print axioms EconomicalSolutions.Algorithm5.visible_projection
#print axioms EconomicalSolutions.Algorithm5.queue_read_whole
#print axioms EconomicalSolutions.Algorithm5.decrement_has_no_priority_guard
#print axioms EconomicalSolutions.Algorithm5.enqueue_has_no_range_guard
#print axioms EconomicalSolutions.Algorithm5.failure_discards_cached_write
#print axioms EconomicalSolutions.Algorithm5.singleton_request_and_ownership
#print axioms EconomicalSolutions.Algorithm5.singleton_passage

#print axioms EconomicalSolutions.Algorithm5.two_process_failure_and_delay
