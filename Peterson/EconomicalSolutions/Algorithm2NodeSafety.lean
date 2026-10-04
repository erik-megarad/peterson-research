module

public import Peterson.EconomicalSolutions.Algorithm2NodeCertificate

@[expose] public section

/-! Retained-winner exclusion for arbitrary node traces. This is conditional
on having a node trace; no concrete tournament simulation is asserted here. -/
namespace EconomicalSolutions.Algorithm2.Node

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

theorem invariant_exclusion {s : State} (h : Invariant s) : Exclusion s := by
  have checked := every_state_checked s
  simp [checkState, Invariant] at h checked
  simp only [h, Bool.true_eq_false, false_or] at checked
  intro both
  rcases checked.1 with h0 | h1
  · exact h0 both.1
  · exact h1 both.2

theorem invariant_next {s : State} (h : Invariant s) (c : Command) :
    Invariant (next s c) := by
  have checked := every_state_checked s
  have h' : invariantB s = true := h
  simp only [checkState, h', Bool.not_true, Bool.false_or, Bool.and_eq_true] at checked
  exact List.all_eq_true.mp checked.2 c (allCommands_complete c)

theorem reachable_invariant {s : State} (h : Reachable s) : Invariant s := by
  induction h with
  | initial => exact invariant_initial
  | step c _ ih => exact invariant_next ih c

/-- Both roles cannot retain a node win, even while one is delayed before
higher publication, or after it advances above this node. Resets/replacements
are unbounded; failure must discard that role's pending cache. -/
theorem retained_winner_exclusion {s : State} (h : Reachable s) : Exclusion s :=
  invariant_exclusion (reachable_invariant h)

/-- Direct interface for a future finite concrete-history refinement. The
initial and node-transition premises are explicit unproved bridge obligations. -/
theorem trace_retained_winner_exclusion (states : Nat → State)
    (commands : Nat → Command) (finish : Nat)
    (start : states 0 = initial)
    (steps : ∀ t, t < finish → states (t + 1) = next (states t) (commands t)) :
    Exclusion (states finish) := by
  apply retained_winner_exclusion
  have reach : ∀ t, t ≤ finish → Reachable (states t) := by
    intro t
    induction t with
    | zero => intro _; rw [start]; exact .initial
    | succ t ih =>
      intro bound
      rw [steps t (by omega)]
      exact .step (commands t) (ih (by omega))
  exact reach finish (by omega)

end EconomicalSolutions.Algorithm2.Node

#print axioms EconomicalSolutions.Algorithm2.Node.retained_winner_exclusion
#print axioms EconomicalSolutions.Algorithm2.Node.trace_retained_winner_exclusion
