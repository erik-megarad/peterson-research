import Peterson.EconomicalSolutions.Algorithm1Certificate

/-! The finite table is an inductive invariant, not a bound on execution length.
This module connects its checked closure to arbitrary repeated executions. -/
namespace EconomicalSolutions.Algorithm1

theorem allLocals_complete (l : Local) : l ∈ allLocals := by
  rcases l with ⟨pc, q⟩
  cases pc <;> cases q
  all_goals first | decide | (rename_i v; cases v <;> decide)

theorem allCommands_complete (c : Command) : c ∈ allCommands := by
  cases c
  all_goals first | decide | (rename_i p; cases p <;> decide)

theorem every_state_checked (s : State) : checkState s = true := by
  have row := List.all_eq_true.mp certificate_checked s.p0 (allLocals_complete s.p0)
  exact List.all_eq_true.mp row s.p1 (allLocals_complete s.p1)

theorem invariant_initial : Invariant initial := by rfl

theorem invariant_safe {s : State} (h : Invariant s) : MutualExclusion s := by
  have checked := every_state_checked s
  simp [checkState, Invariant] at h checked
  simp only [h, Bool.true_eq_false, false_or] at checked
  intro both
  rcases checked.1 with h0 | h1
  · exact h0 both.1
  · exact h1 both.2

theorem invariant_next {s t : State} {c : Command}
    (h : Invariant s) (edge : next s c = some t) : Invariant t := by
  have checked := every_state_checked s
  have h' : invariantB s = true := h
  simp only [checkState, h', Bool.not_true, Bool.false_or, Bool.and_eq_true] at checked
  have closed := List.all_eq_true.mp checked.2 c (allCommands_complete c)
  simpa [edge, Invariant] using closed

theorem invariant_step {s t : State} {a : Label}
    (h : Invariant s) (edge : lts.Tr s a t) : Invariant t := by
  obtain ⟨c, edge, _⟩ := edge
  exact invariant_next h edge

theorem reachable_invariant {s : State} (h : Reachable s) : Invariant s := by
  induction h with
  | initial => exact invariant_initial
  | step _ edge ih => exact invariant_step ih edge

/-- Theorem 3-2: arbitrary finite executions with unrestricted failures,
restarts, repeated requests, stale reads, and delays. No fairness premise. -/
theorem mutual_exclusion {s : State} (h : Reachable s) : MutualExclusion s :=
  invariant_safe (reachable_invariant h)

theorem path_invariant {s t : State} {trace : List Label}
    (path : lts.MTr s trace t) (h : Invariant s) : Invariant t := by
  induction path with
  | refl => exact h
  | stepL edge _ ih => exact ih (invariant_step h edge)

/-- The same unbounded finite-execution result stated directly using CSLib paths. -/
theorem finite_execution_mutual_exclusion {s : State} {trace : List Label}
    (path : lts.MTr initial trace s) : MutualExclusion s :=
  invariant_safe (path_invariant path invariant_initial)

end EconomicalSolutions.Algorithm1

#print axioms EconomicalSolutions.Algorithm1.mutual_exclusion
#print axioms EconomicalSolutions.Algorithm1.finite_execution_mutual_exclusion
