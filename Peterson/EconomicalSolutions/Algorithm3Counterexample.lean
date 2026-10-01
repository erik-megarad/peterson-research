import Peterson.EconomicalSolutions.Algorithm3Certificate

/-! Kernel-checked fair non-ticking execution for the complete proceedings
Algorithm 3. Four positions, 32 initial transitions, then 21 transitions forever.
This proves a negative result for the frozen target, not for Algorithms 6/7. -/
namespace EconomicalSolutions.Algorithm3.Counterexample
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Pointwise equality avoids requiring decidable equality of functions. -/
def Edge (s : State 4) (c : Command 4) (t : State 4) : Prop :=
  match next s c with
  | none => False
  | some u => ∀ p, u p = t p
instance (s : State 4) (c : Command 4) (t : State 4) : Decidable (Edge s c t) := by
  unfold Edge
  split <;> infer_instance

theorem edge_next {s t : State 4} {c : Command 4} (h : Edge s c t) :
    next s c = some t := by
  unfold Edge at h
  split at h
  · contradiction
  · rename_i u he
    exact he.trans (congrArg some (funext h))

theorem stem_initial : stemState 0 = initial 4 := funext (by decide)

theorem stem_step (k : Fin 32) :
    next (stemState k) (stemCommand k) = some
      (if h : k.val + 1 < 32 then stemState ⟨k.val + 1, h⟩ else cycleState 0) := by
  apply edge_next
  have h : ∀ k : Fin 32, Edge (stemState k) (stemCommand k)
      (if h : k.val + 1 < 32 then stemState ⟨k.val + 1, h⟩ else cycleState 0) := by decide
  exact h k

theorem cycle_step (k : Fin 21) :
    next (cycleState k) (cycleCommand k) =
      some (cycleState ⟨(k.val + 1) % 21, Nat.mod_lt _ (by decide)⟩) := by
  apply edge_next
  have h : ∀ k : Fin 21, Edge (cycleState k) (cycleCommand k)
      (cycleState ⟨(k.val + 1) % 21, Nat.mod_lt _ (by decide)⟩) := by decide
  exact h k

/-- Complete state (registers, controls, cursors, flags and used caches) repeats. -/
def state (t : Nat) : State 4 :=
  if h : t < 32 then stemState ⟨t, h⟩ else
    cycleState ⟨(t - 32) % 21, Nat.mod_lt _ (by decide)⟩
def command (t : Nat) : Command 4 :=
  if h : t < 32 then stemCommand ⟨t, h⟩ else
    cycleCommand ⟨(t - 32) % 21, Nat.mod_lt _ (by decide)⟩
def event (t : Nat) : Label 4 := label (state t) (command t)

@[simp] theorem state_after (k : Nat) :
    state (32 + k) = cycleState ⟨k % 21, Nat.mod_lt _ (by decide)⟩ := by
  simp [state]
@[simp] theorem command_after (k : Nat) :
    command (32 + k) = cycleCommand ⟨k % 21, Nat.mod_lt _ (by decide)⟩ := by
  simp [command]
@[simp] theorem event_after (k : Nat) : event (32 + k) =
    label (cycleState ⟨k % 21, Nat.mod_lt _ (by decide)⟩)
      (cycleCommand ⟨k % 21, Nat.mod_lt _ (by decide)⟩) := by
  simp [event]

theorem execution_step (t : Nat) : next (state t) (command t) = some (state (t + 1)) := by
  by_cases h : t < 32
  · have ht := stem_step ⟨t, h⟩
    by_cases hn : t + 1 < 32
    · simpa [state, command, h, hn] using ht
    · have he : t = 31 := by omega
      subst t
      simpa [state, command] using ht
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 32 ≤ t)
    rw [Nat.add_assoc, state_after, state_after, command_after, cycle_step]
    congr 2
    apply Fin.ext
    simp [Nat.add_mod]

theorem execution : Execution state event :=
  ⟨stem_initial, fun t => ⟨command t, execution_step t, rfl⟩⟩

/-- Each position performs an ordinary instruction in each cycle. This is
stronger than the requested instruction-or-abort scheduling obligation. -/
theorem ordinary_present : ∀ p : Fin 4, ∃ k : Fin 21,
    Ordinary (label (cycleState k) (cycleCommand k)) p := by decide

theorem every_position_runs (p : Fin 4) (t : Nat) :
    ∃ u, t ≤ u ∧ Ordinary (event u) p := by
  obtain ⟨k, hk⟩ := ordinary_present p
  refine ⟨32 + (21 * t + k.val), by omega, ?_⟩
  rw [event_after]
  convert hk using 1
  congr 2 <;> apply Fin.ext <;> simp [Nat.add_mod, Nat.mod_eq_of_lt k.isLt]

/-- Covers every active occurrence in the stem as well as the infinite tail.
Starts, restarts and stutters do not discharge any obligation. -/
theorem instruction_scheduled : InstructionScheduled state event := by
  intro p t _
  obtain ⟨u, hu, ho⟩ := every_position_runs p t
  exact ⟨u, hu, Or.inl ho⟩

theorem cycle_survivors : ∀ k : Fin 21, ∀ p : Fin 4, p ≠ 0 →
    Active (cycleState k p) ∧ label (cycleState k) (cycleCommand k) ≠ .fail p := by decide

theorem cycle_no_ticks : ∀ k : Fin 21, ∀ p : Fin 4,
    label (cycleState k) (cycleCommand k) ≠ .tick p := by decide

/-- P1, P2 and P3 keep the same active episode forever after the prefix. -/
theorem survivors (p : Fin 4) (hp : p ≠ 0) : SurvivesFrom state event p 32 := by
  intro t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  simpa only [state_after, event_after] using
    cycle_survivors ⟨k % 21, Nat.mod_lt _ (by decide)⟩ p hp

theorem no_ticks_after (t : Nat) (ht : 32 ≤ t) (p : Fin 4) : event t ≠ .tick p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  simpa only [event_after] using cycle_no_ticks ⟨k % 21, Nat.mod_lt _ (by decide)⟩ p

/-- This exact infinite fair witness has three non-failing stuck episodes. -/
theorem fair_non_ticking_lasso :
    Execution state event ∧ InstructionScheduled state event ∧
    (∀ p : Fin 4, p ≠ 0 → SurvivesFrom state event p 32) ∧
    (∀ t, 32 ≤ t → ∀ p, event t ≠ .tick p) :=
  ⟨execution, instruction_scheduled, survivors, no_ticks_after⟩

/-- The source-specific positive first-outcome target is false at n=4. -/
theorem not_universal_next_outcome : ¬ UniversalNextOutcome 4 := by
  intro h
  have live := (survivors 1 (by decide) 32 (by omega)).1
  obtain ⟨u, hu, _, ho⟩ := h state event execution instruction_scheduled 1 32 live
  rcases ho with tick | failed
  · exact no_ticks_after u hu 1 tick
  · exact (survivors 1 (by decide) u hu).2 failed

/-- Even the proposed repeated-ticking conclusion for surviving episodes fails. -/
theorem not_universal_repeated_ticks : ¬ UniversalRepeatedTicks 4 := by
  intro h
  obtain ⟨u, hu, tick⟩ := h state event execution instruction_scheduled 1 32
    (survivors 1 (by decide)) 32 (by omega)
  exact no_ticks_after u hu 1 tick

#print axioms fair_non_ticking_lasso
#print axioms not_universal_next_outcome
#print axioms not_universal_repeated_ticks

end EconomicalSolutions.Algorithm3.Counterexample
