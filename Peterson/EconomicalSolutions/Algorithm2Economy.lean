module

public import Peterson.EconomicalSolutions.Algorithm2WellFormed
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod

@[expose] public section

/-! The finite covering alphabet of Algorithm 2's one visible register. The
raw `Value` and the interpreter remain unchanged. -/
namespace EconomicalSolutions.Algorithm2

/-- The dead value and both flags at each positive tournament level. -/
def InAlphabet (n : Nat) (v : Value) : Prop :=
  v = dead ∨ (1 ≤ v.level ∧ v.level ≤ height n)

def Alphabet (n : Nat) := {v : Value // InAlphabet n v}

def alphabetEquiv (n : Nat) : Alphabet n ≃ Option (Fin (height n) × Bool) where
  toFun v := if h : v.val.level = 0 then none else
    some (⟨v.val.level - 1, by
      rcases v.property with hd | ⟨_, hb⟩
      · exact False.elim (h (by simp [hd, dead, ScanBridge.dead]))
      · omega⟩, v.val.flag)
  invFun
    | none => ⟨dead, Or.inl rfl⟩
    | some (k, b) => ⟨⟨k.val + 1, b⟩, Or.inr (by simp; omega)⟩
  left_inv := by
    rintro ⟨⟨k, b⟩, hv⟩
    cases k with
    | zero =>
      apply Subtype.ext
      rcases hv with hd | ⟨hk, _⟩
      · simp [hd, dead, ScanBridge.dead]
      · simp at hk
    | succ k =>
      apply Subtype.ext
      simp
  right_inv := by
    rintro (_ | ⟨k, b⟩)
    · rfl
    · simp

noncomputable instance (n : Nat) : Fintype (Alphabet n) :=
  Fintype.ofEquiv _ (alphabetEquiv n).symm

/-- This is the exact size of the selected cover, not an assertion that every
member of the cover occurs in an execution. -/
theorem alphabet_card (n : Nat) : Fintype.card (Alphabet n) = 1 + 2 * height n := by
  rw [Fintype.card_congr (alphabetEquiv n)]
  simp [Nat.mul_comm]
  omega

theorem alphabetEquiv_lossless (n : Nat) (v : Alphabet n) :
    (alphabetEquiv n).symm (alphabetEquiv n v) = v :=
  (alphabetEquiv n).left_inv v

theorem reachable_register {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) (p : Proc n) : InAlphabet n (s p).q := by
  rcases reachable_wellFormed reach p with ⟨bound, zero, _⟩
  by_cases hz : (s p).q.level = 0
  · exact Or.inl (zero hz)
  · exact Or.inr ⟨by omega, bound⟩

theorem initial_register (n : Nat) (p : Proc n) :
    InAlphabet n ((initial n p).q) := Or.inl rfl

/-- Real scan reads are covered by reachable registers; dummy leaves read dead. -/
theorem reachable_read {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) (j : Leaf n) : InAlphabet n (visible s j) := by
  unfold visible
  split
  · rename_i real
    exact reachable_register reach ⟨j.val, real⟩
  · exact Or.inl rfl

/-- Every successful instruction, including either cached write, remains in
the cover when executed from a reachable state. -/
theorem reachable_next_register {n : Nat} {cfg : Config n} {s t : State n}
    (reach : Reachable cfg s) (c : Command n)
    (step : next cfg s c = some t) (p : Proc n) : InAlphabet n (t p).q :=
  reachable_register (.step reach ⟨c, step, rfl⟩) p

/-- The cached first assignment publishes the exact cached whole value. -/
theorem ordinary_write1 {n : Nat} (cfg : Config n) (p : Proc n)
    (s : State n) (k : Nat) (v : Value)
    (hpc : (s p).pc = .write1 k v) :
    ordinary cfg p s = some ⟨scan cfg p .second k, v⟩ := by
  simp [ordinary, hpc]

/-- The cached second assignment also publishes the exact cached whole value. -/
theorem ordinary_write2 {n : Nat} (cfg : Config n) (p : Proc n)
    (s : State n) (k : Nat) (v : Value)
    (hpc : (s p).pc = .write2 k v) :
    ordinary cfg p s = some ⟨scan cfg p .wait k, v⟩ := by
  simp [ordinary, hpc]

/-- Equal actor-local state and equal visible registers give the same ordinary
instruction result; peer program counters and caches are private. -/
theorem ordinary_visible {n : Nat} (cfg : Config n) (s t : State n)
    (p : Proc n) (hlocal : s p = t p)
    (hvisible : ∀ q, (s q).q = (t q).q) :
    ordinary cfg p s = ordinary cfg p t := by
  have read_eq (j : Leaf n) : visible s j = visible t j := by
    unfold visible
    split
    · rename_i real
      exact hvisible ⟨j.val, real⟩
    · rfl
  unfold ordinary
  rw [hlocal]
  cases (t p).pc <;> simp [read_eq]

theorem setLocal_other_register {n : Nat} (s : State n) (p q : Proc n)
    (l : Local n) (hne : q ≠ p) : (setLocal s p l q).q = (s q).q := by
  simp [setLocal, hne]

theorem next_other_register {n : Nat} (cfg : Config n) (s t : State n)
    (c : Command n) (p q : Proc n) (step : next cfg s c = some t)
    (hactor : c = .run p ∨ c = .fail p ∨ c = .restart p)
    (hne : q ≠ p) : (t q).q = (s q).q := by
  rcases hactor with rfl | rfl | rfl
  · simp only [next] at step
    cases ho : ordinary cfg p s with
    | none => simp [ho] at step
    | some l =>
      have ht : t = setLocal s p l := by simpa [ho] using step.symm
      simpa [ht] using setLocal_other_register s p q l hne
  · simp only [next] at step
    split at step
    · simp at step
    · rw [← Option.some.inj step]
      exact setLocal_other_register s p q ⟨.down, dead⟩ hne
  · simp only [next] at step
    split at step
    · rw [← Option.some.inj step]
      exact setLocal_other_register s p q ⟨.idle, dead⟩ hne
    · simp at step

end EconomicalSolutions.Algorithm2

#print axioms EconomicalSolutions.Algorithm2.alphabetEquiv
#print axioms EconomicalSolutions.Algorithm2.alphabet_card
#print axioms EconomicalSolutions.Algorithm2.alphabetEquiv_lossless
#print axioms EconomicalSolutions.Algorithm2.reachable_register
#print axioms EconomicalSolutions.Algorithm2.initial_register
#print axioms EconomicalSolutions.Algorithm2.reachable_read
#print axioms EconomicalSolutions.Algorithm2.reachable_next_register
#print axioms EconomicalSolutions.Algorithm2.ordinary_write1
#print axioms EconomicalSolutions.Algorithm2.ordinary_write2
#print axioms EconomicalSolutions.Algorithm2.ordinary_visible
#print axioms EconomicalSolutions.Algorithm2.next_other_register
