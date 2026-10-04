module

public import Peterson.EconomicalSolutions.Algorithm2

@[expose] public section

namespace EconomicalSolutions.Algorithm2

/-- The chosen height is precisely the least padding exponent. -/
theorem height_le_iff (n h : Nat) : height n ≤ h ↔ n ≤ 2 ^ h :=
  Nat.clog_le_iff_le_pow (by decide)

theorem real_fits_padding (n : Nat) : n ≤ capacity n :=
  Nat.le_pow_clog (by decide) n

/-- Ascending order is one inhabitant, not a restriction on the target. -/
def ascendingConfig (n : Nat) (positive : 0 < n) : Config n where
  positive := positive
  order := fun p k => (List.finRange (capacity n)).filter
    (fun j => decide (j.val / 2 ^ k = p.val / 2 ^ k ∧ bit j.val k ≠ bit p.val k))
  nodup := by intros; exact List.Nodup.filter _ (List.nodup_finRange _)
  complete := by intros; simp [Opponent]

theorem singleton_height : height 1 = 0 := by simp [height]

theorem dummy_dead {n : Nat} (s : State n) (j : Leaf n) (dummy : n ≤ j.val) :
    visible s j = dead := by simp [visible, show ¬ j.val < n by omega]

/-- Every command is either a global stutter or replaces exactly one real
process's complete local state. No reachability or ownership premise is used. -/
theorem next_locality {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    (step : next cfg s c = some t) :
    t = s ∨ ∃ p l, t = setLocal s p l := by
  cases c with
  | stutter => exact Or.inl (Option.some.inj step.symm)
  | run p =>
    simp only [next] at step
    cases h : ordinary cfg p s with
    | none => simp [h] at step
    | some l => exact Or.inr ⟨p, l, by simpa [h] using step.symm⟩
  | fail p =>
    simp only [next] at step
    split at step
    · simp at step
    · exact Or.inr ⟨p, ⟨.down, dead⟩, Option.some.inj step.symm⟩
  | restart p =>
    simp only [next] at step
    split at step
    · exact Or.inr ⟨p, ⟨.idle, dead⟩, Option.some.inj step.symm⟩
    · simp at step

theorem visible_setLocal_other {n : Nat} (s : State n) (p : Proc n) (l : Local n)
    (j : Leaf n) (other : j.val ≠ p.val) :
    visible (setLocal s p l) j = visible s j := by
  unfold visible
  split
  · simp [setLocal, show (⟨j.val, by assumption⟩ : Proc n) ≠ p by
      intro same; exact other (congrArg Fin.val same)]
  · rfl

/-- This discharges the scan bridge's atomicity premise directly from the
actual source interpreter, including failure reset and dummy padding. -/
theorem next_singleChange {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    (step : next cfg s c = some t) : ScanBridge.SingleChange (visible s) (visible t) := by
  obtain same | ⟨p, l, rfl⟩ := next_locality step
  · subst t; intro i j hi; exact (hi rfl).elim
  · intro i j hi hj
    have changed (a : Leaf n) (ha : visible s a ≠ visible (setLocal s p l) a) :
        a.val = p.val := by
      by_contra different
      exact ha (visible_setLocal_other s p l a different).symm
    exact Fin.ext ((changed i hi).trans (changed j hj).symm)

theorem lts_singleChange {n : Nat} {cfg : Config n} {s t : State n} {a : Label n}
    (step : (lts cfg).Tr s a t) : ScanBridge.SingleChange (visible s) (visible t) := by
  obtain ⟨c, hc, _⟩ := step
  exact next_singleChange hc

/-- A reported read returns the entire pair in the exact pre-state. -/
theorem scanRead_sample {n : Nat} {s : State n} {c : Command n}
    {p : Proc n} {j : Leaf n} {v : Value} (read : scanRead s c = some (p, j, v)) :
    v = visible s j := by
  cases c <;> simp only [scanRead] at read
  case run actor =>
    split at read
    · simp only [Option.some.injEq, Prod.mk.injEq] at read
      rcases read with ⟨_, same, value⟩
      subst j
      exact value.symm
    · simp at read
  all_goals contradiction

/-- A low scan read consumes exactly one cursor element and performs no write.
An empty suffix returns dead on its next private instruction, allowing delay. -/
theorem scan_low_step {n : Nat} (cfg : Config n) (s : State n) (p : Proc n)
    (c : Continuation) (k : Nat) (j : Leaf n) (rest : List (Leaf n))
    (pc : (s p).pc = .scan c k (j :: rest)) (low : (visible s j).level < k) :
    next cfg s (.run p) = some (setLocal s p { s p with pc := .scan c k rest }) := by
  simp [next, ordinary, pc, show ¬ k ≤ (visible s j).level by omega]

/-- A qualifying read ends at its actual first qualifying sample; it never
reads a suffix, combines fields, or replaces that sample by a maximum. -/
theorem scan_high_step {n : Nat} (cfg : Config n) (s : State n) (p : Proc n)
    (c : Continuation) (k : Nat) (j : Leaf n) (rest : List (Leaf n))
    (pc : (s p).pc = .scan c k (j :: rest)) (high : k ≤ (visible s j).level) :
    next cfg s (.run p) = some (setLocal s p { s p with pc := resume cfg p c k (visible s j) }) := by
  simp [next, ordinary, pc, high]

/-- Read times in an actual command-indexed execution name pre-states. This
supplies exact samples to ScanBridge.Read; grouping one invocation and proving
its dead-return coverage is a subsequent history/ownership obligation. -/
theorem execution_read_sample {n : Nat} {trace : Nat → State n} {commands : Nat → Command n}
    {time : Nat} {p : Proc n} {j : Leaf n} {v : Value}
    (read : scanRead (trace time) (commands time) = some (p, j, v)) :
    v = visible (trace time) j := scanRead_sample read

end EconomicalSolutions.Algorithm2

#print axioms EconomicalSolutions.Algorithm2.height_le_iff
#print axioms EconomicalSolutions.Algorithm2.real_fits_padding
#print axioms EconomicalSolutions.Algorithm2.next_singleChange
#print axioms EconomicalSolutions.Algorithm2.lts_singleChange
#print axioms EconomicalSolutions.Algorithm2.scanRead_sample
#print axioms EconomicalSolutions.Algorithm2.scan_low_step
#print axioms EconomicalSolutions.Algorithm2.scan_high_step
