module

public import Peterson.EconomicalSolutions.Algorithm5Invariant
public import Peterson.EconomicalSolutions.Algorithm2Economy
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum

@[expose] public section

set_option linter.unnecessarySimpa false
set_option linter.deprecated false

/-! A finite cover of Algorithm 5's whole visible register. The interpreter's
unbounded integer priority and its compound tournament value are unchanged. -/
namespace EconomicalSolutions.Algorithm5

def RootValue (n : Nat) (v : Algorithm2.Value) : Prop :=
  v = Algorithm2.dead ∨ (0 < Algorithm2.height n ∧ v.level = Algorithm2.height n)

def RootAlphabet (n : Nat) := {v : Algorithm2.Value // RootValue n v}

def InAlphabet (n : Nat) (v : Value) : Prop :=
  (Algorithm2.InAlphabet n v.tournament ∧ v.priority = -1) ∨
    (RootValue n v.tournament ∧ 0 ≤ v.priority ∧ v.priority < n)

def Alphabet (n : Nat) := {v : Value // InAlphabet n v}

private theorem root_in_tournament {n : Nat} {v : Algorithm2.Value}
    (h : RootValue n v) : Algorithm2.InAlphabet n v := by
  rcases h with hd | ⟨hp, hl⟩
  · exact Or.inl hd
  · exact Or.inr ⟨by omega, hl.le⟩

def alphabetEquiv (n : Nat) :
    Alphabet n ≃ Algorithm2.Alphabet n ⊕ (RootAlphabet n × Fin n) where
  toFun v := if h : v.val.priority = -1 then
      Sum.inl ⟨v.val.tournament, by
        rcases v.property with ⟨ht, _⟩ | ⟨hr, lo, _⟩
        · exact ht
        · exact root_in_tournament hr⟩
    else Sum.inr (⟨v.val.tournament, by
      rcases v.property with ⟨_, hm⟩ | ⟨hr, _, _⟩
      · exact False.elim (h hm)
      · exact hr⟩,
      ⟨v.val.priority.toNat, by
        rcases v.property with ⟨_, hm⟩ | ⟨_, lo, hi⟩
        · exact False.elim (h hm)
        · omega⟩)
  invFun
    | .inl v => ⟨⟨v.val, -1⟩, Or.inl ⟨v.property, rfl⟩⟩
    | .inr (v, q) => ⟨⟨v.val, q.val⟩, Or.inr ⟨v.property,
        by simp,
        by simpa using q.isLt⟩⟩
  left_inv := by
    rintro ⟨⟨v, q⟩, hv⟩
    by_cases h : q = -1
    · apply Subtype.ext
      simp [h]
    · rcases hv with ⟨_, hm⟩ | ⟨_, lo, hi⟩
      · exact False.elim (h hm)
      · apply Subtype.ext
        simp [h, Int.toNat_of_nonneg lo]
  right_inv := by
    rintro (v | ⟨v, q⟩)
    · rfl
    · have h : (q.val : Int) ≠ -1 := by omega
      simp only [dif_neg h, Sum.inr.injEq]
      apply Prod.ext
      · apply Subtype.ext; rfl
      · apply Fin.ext; simp

def rootEquiv (n : Nat) (pos : 0 < Algorithm2.height n) :
    RootAlphabet n ≃ Option Bool where
  toFun v := if v.val = Algorithm2.dead then none else some v.val.flag
  invFun
    | none => ⟨Algorithm2.dead, Or.inl rfl⟩
    | some b => ⟨⟨Algorithm2.height n, b⟩, Or.inr ⟨pos, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨level, flag⟩, hv⟩
    apply Subtype.ext
    rcases hv with hd | ⟨_, hl⟩
    · simp [hd]
    · have hlevel : level = Algorithm2.height n := hl
      subst level
      have ne : ({ level := Algorithm2.height n, flag := flag } : Algorithm2.Value) ≠
          Algorithm2.dead := by
        simp [Algorithm2.dead, Algorithm2.ScanBridge.dead, pos.ne']
      simp [ne]
  right_inv := by
    rintro (_ | b)
    · rfl
    · have ne : ({ level := Algorithm2.height n, flag := b } : Algorithm2.Value) ≠
          Algorithm2.dead := by
        simp [Algorithm2.dead, Algorithm2.ScanBridge.dead, pos.ne']
      simp [ne]

def rootZeroEquiv (n : Nat) (hz : Algorithm2.height n = 0) :
    RootAlphabet n ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨Algorithm2.dead, Or.inl rfl⟩
  left_inv := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    rcases hv with hd | ⟨hp, _⟩
    · exact hd.symm
    · omega
  right_inv := by intro x; cases x; rfl

noncomputable instance (n : Nat) : Fintype (RootAlphabet n) := by
  by_cases hp : 0 < Algorithm2.height n
  · exact Fintype.ofEquiv _ (rootEquiv n hp).symm
  · have hzero : Algorithm2.height n = 0 := by omega
    exact Fintype.ofEquiv _ (rootZeroEquiv n hzero).symm

noncomputable instance (n : Nat) : Fintype (Alphabet n) :=
  Fintype.ofEquiv _ (alphabetEquiv n).symm

theorem root_card (n : Nat) :
    Fintype.card (RootAlphabet n) = if Algorithm2.height n = 0 then 1 else 3 := by
  by_cases hz : Algorithm2.height n = 0
  · simp only [hz, ite_true]
    rw [Fintype.card_congr (rootZeroEquiv n hz)]
    simp
  · have hp : 0 < Algorithm2.height n := by omega
    rw [Fintype.card_congr (rootEquiv n hp)]
    simp [hz]

theorem alphabet_card (n : Nat) :
    Fintype.card (Alphabet n) =
      1 + 2 * Algorithm2.height n +
        (if Algorithm2.height n = 0 then 1 else 3) * n := by
  rw [Fintype.card_congr (alphabetEquiv n)]
  simp [Algorithm2.alphabet_card, root_card]

theorem alphabet_card_ge_two (n : Nat) (hn : 2 ≤ n) :
    Fintype.card (Alphabet n) = 1 + 2 * Algorithm2.height n + 3 * n := by
  have hh : 0 < Algorithm2.height n := by
    by_contra h
    have hz : Algorithm2.height n = 0 := by omega
    have hle : n ≤ 1 := by
      have := (Algorithm2.height_le_iff n 0).mp (by omega : Algorithm2.height n ≤ 0)
      simpa using this
    omega
  have hne : Algorithm2.height n ≠ 0 := by omega
  simpa [hne] using alphabet_card n

theorem alphabet_card_singleton : Fintype.card (Alphabet 1) = 2 := by
  simpa [Algorithm2.singleton_height] using alphabet_card 1

theorem alphabetEquiv_lossless (n : Nat) (v : Alphabet n) :
    (alphabetEquiv n).symm (alphabetEquiv n v) = v :=
  (alphabetEquiv n).left_inv v

theorem reachable_register {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) (p : Proc n) : InAlphabet n (s p).value := by
  have proj := reachable_projection reach
  have tour := Algorithm2.reachable_register proj.2 p
  have facts := (reachable_invariant reach).facts p
  have bounds := (priority_bounds reach) p
  by_cases hm : (s p).value.priority = -1
  · exact Or.inl ⟨tour, hm⟩
  · right
    have lo : 0 ≤ (s p).value.priority := by dsimp [priority] at bounds; omega
    refine ⟨?_, lo, by simpa [priority] using bounds.2⟩
    cases hp : (s p).pc with
    | complete | depart =>
      have stage : Algorithm2.StageWF ((project s) p) :=
        (Algorithm2.reachable_wellFormed proj.2 p).2.2
      have link := proj.1 p
      simp only [Linked, hp] at link
      simp only [project, Algorithm2.StageWF, link] at stage
      by_cases hz : Algorithm2.height n = 0
      · left
        have lv : ((project s) p).q.level = 0 := by
          have bound := (Algorithm2.reachable_wellFormed proj.2 p).1
          omega
        exact (Algorithm2.reachable_wellFormed proj.2 p).2.1 lv
      · exact Or.inr ⟨by omega, stage⟩
    | _ =>
      have link := proj.1 p
      have dead : (s p).value.tournament = Algorithm2.dead := by
        simp_all [Linked, QueueFacts, priority]
      exact Or.inl dead

theorem initial_register (n : Nat) (p : Proc n) :
    InAlphabet n ((initial n p).value) := Or.inl ⟨Or.inl rfl, rfl⟩

theorem reachable_read {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) (p : Proc n) : InAlphabet n (s p).value :=
  reachable_register reach p

theorem reachable_next_register {n : Nat} {cfg : Config n} {s t : State n}
    (reach : Reachable cfg s) (c : Command n)
    (step : next cfg s c = some t) (p : Proc n) : InAlphabet n (t p).value :=
  reachable_register (.step reach ⟨c, step, rfl⟩) p

theorem ordinary_enqueue {n : Nat} (cfg : Config n) (s : State n)
    (p : Proc n) (v : Int) (h : (s p).pc = .enqueue v) :
    ordinary cfg s p = some ⟨.complete, (s p).tournamentPC,
      ⟨(s p).value.tournament, v⟩⟩ := by
  simp [ordinary, h]

theorem ordinary_depart {n : Nat} (cfg : Config n) (s : State n)
    (p : Proc n) (h : (s p).pc = .depart) :
    ordinary cfg s p = some ⟨.test, .idle,
      ⟨Algorithm2.dead, (s p).value.priority⟩⟩ := by
  simp [ordinary, h]

theorem ordinary_visible {n : Nat} (cfg : Config n) (s t : State n)
    (p : Proc n) (hlocal : s p = t p)
    (hvisible : ∀ q, (s q).value = (t q).value) :
    ordinary cfg s p = ordinary cfg t p := by
  have hp : project s p = project t p := by simp [project, hlocal]
  have hv : ∀ q, ((project s) q).q = ((project t) q).q := by
    intro q
    exact congrArg Value.tournament (hvisible q)
  have ht : tournamentInstruction cfg s p = tournamentInstruction cfg t p := by
    simp only [tournamentInstruction, Algorithm2.ordinary_visible cfg.tournament (project s) (project t)
      p hp hv, hlocal]
  unfold ordinary
  rw [hlocal]
  cases (t p).pc <;> simp [hvisible, ht]

theorem next_other_register {n : Nat} (cfg : Config n) (s t : State n)
    (c : Command n) (p q : Proc n) (step : next cfg s c = some t)
    (hactor : c = .run p ∨ c = .fail p ∨ c = .restart p)
    (hne : q ≠ p) : (t q).value = (s q).value := by
  rcases hactor with rfl | rfl | rfl
  · simp only [next] at step
    cases ho : ordinary cfg s p with
    | none => simp [ho] at step
    | some l =>
      have ht : t = setLocal s p l := by simpa [ho] using step.symm
      simpa [ht, setLocal, hne]
  · simp only [next] at step
    split at step
    · simp at step
    · rw [← Option.some.inj step]
      simp [setLocal, hne]
  · simp only [next] at step
    split at step
    · rw [← Option.some.inj step]
      simp [setLocal, hne]
    · simp at step

end EconomicalSolutions.Algorithm5

#print axioms EconomicalSolutions.Algorithm5.alphabetEquiv
#print axioms EconomicalSolutions.Algorithm5.root_card
#print axioms EconomicalSolutions.Algorithm5.alphabet_card
#print axioms EconomicalSolutions.Algorithm5.alphabet_card_ge_two
#print axioms EconomicalSolutions.Algorithm5.alphabet_card_singleton
#print axioms EconomicalSolutions.Algorithm5.alphabetEquiv_lossless
#print axioms EconomicalSolutions.Algorithm5.reachable_register
#print axioms EconomicalSolutions.Algorithm5.initial_register
#print axioms EconomicalSolutions.Algorithm5.reachable_read
#print axioms EconomicalSolutions.Algorithm5.reachable_next_register
#print axioms EconomicalSolutions.Algorithm5.ordinary_enqueue
#print axioms EconomicalSolutions.Algorithm5.ordinary_depart
#print axioms EconomicalSolutions.Algorithm5.ordinary_visible
#print axioms EconomicalSolutions.Algorithm5.next_other_register
