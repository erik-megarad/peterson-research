module

public import Peterson.EconomicalSolutions.Algorithm6Cohort
public import Peterson.EconomicalSolutions.Algorithm2Economy
public import Mathlib.Data.Fintype.Sum

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! A finite cover of Algorithm 6's whole product register. The tournament
component remains present during upper-clock publication. -/
namespace EconomicalSolutions.Algorithm6

def UpperRootValue (n : Nat) (v : Algorithm2.Value) : Prop :=
  v.level = Algorithm2.height n ∧
    (Algorithm2.height n = 0 → v = Algorithm2.dead)

def UpperRootAlphabet (n : Nat) := {v : Algorithm2.Value // UpperRootValue n v}

def upperRootZeroEquiv (n : Nat) (hz : Algorithm2.height n = 0) :
    UpperRootAlphabet n ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨Algorithm2.dead, by simp [UpperRootValue, hz, Algorithm2.dead, Algorithm2.ScanBridge.dead]⟩
  left_inv := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    exact (hv.2 hz).symm
  right_inv := by intro x; cases x; rfl

def upperRootPosEquiv (n : Nat) (hp : 0 < Algorithm2.height n) :
    UpperRootAlphabet n ≃ Bool where
  toFun v := v.val.flag
  invFun b := ⟨⟨Algorithm2.height n, b⟩, by simp [UpperRootValue, hp.ne']⟩
  left_inv := by
    rintro ⟨⟨level, flag⟩, hv⟩
    apply Subtype.ext
    have hl : level = Algorithm2.height n := hv.1
    subst level
    rfl
  right_inv := by intro b; rfl

noncomputable instance (n : Nat) : Fintype (UpperRootAlphabet n) := by
  by_cases hp : 0 < Algorithm2.height n
  · exact Fintype.ofEquiv _ (upperRootPosEquiv n hp).symm
  · exact Fintype.ofEquiv _ (upperRootZeroEquiv n (by omega)).symm

theorem upperRoot_card (n : Nat) :
    Fintype.card (UpperRootAlphabet n) =
      if Algorithm2.height n = 0 then 1 else 2 := by
  by_cases hz : Algorithm2.height n = 0
  · rw [Fintype.card_congr (upperRootZeroEquiv n hz)]
    simp [hz]
  · rw [Fintype.card_congr (upperRootPosEquiv n (by omega))]
    simp [hz]

def InAlphabet (n : Nat) (v : Value) : Prop :=
  (Algorithm2.InAlphabet n v.tournament ∧ v.clock = .off) ∨
  (UpperRootValue n v.tournament ∧ ∃ b, v.clock = .upper b) ∨
  (v.tournament = Algorithm2.dead ∧
    ((∃ b, v.clock = .lower b) ∨ v.clock = .cs))

def Alphabet (n : Nat) := {v : Value // InAlphabet n v}

def alphabetEquiv (n : Nat) :
    Alphabet n ≃ Algorithm2.Alphabet n ⊕
      ((UpperRootAlphabet n × Bool) ⊕ Option Bool) where
  toFun v :=
    match h : v.val.clock with
    | .off => .inl ⟨v.val.tournament, by
        rcases v.property with ⟨ht, _⟩ | ⟨_, b, hb⟩ | ⟨_, hb⟩
        · exact ht
        · simp [h] at hb
        · rcases hb with ⟨b, hb⟩ | hb <;> simp [h] at hb⟩
    | .upper b => .inr (.inl (⟨v.val.tournament, by
        rcases v.property with ⟨_, hb⟩ | ⟨hr, _, _⟩ | ⟨_, hb⟩
        · simp [h] at hb
        · exact hr
        · rcases hb with ⟨b, hb⟩ | hb <;> simp [h] at hb⟩, b))
    | .lower b => .inr (.inr (some b))
    | .cs => .inr (.inr none)
  invFun
    | .inl v => ⟨⟨v.val, .off⟩, Or.inl ⟨v.property, rfl⟩⟩
    | .inr (.inl (v, b)) => ⟨⟨v.val, .upper b⟩, Or.inr (Or.inl ⟨v.property, b, rfl⟩)⟩
    | .inr (.inr (some b)) => ⟨⟨Algorithm2.dead, .lower b⟩,
        Or.inr (Or.inr ⟨rfl, Or.inl ⟨b, rfl⟩⟩)⟩
    | .inr (.inr none) => ⟨⟨Algorithm2.dead, .cs⟩,
        Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩)⟩
  left_inv := by
    rintro ⟨⟨v, tag⟩, hv⟩
    cases tag with
    | off => rfl
    | upper b => rfl
    | lower b =>
      apply Subtype.ext
      rcases hv with ⟨_, hb⟩ | ⟨_, _, hb⟩ | ⟨hd, _⟩
      · contradiction
      · cases hb
      · have hd' : v = Algorithm2.dead := hd
        cases hd'
        rfl
    | cs =>
      apply Subtype.ext
      rcases hv with ⟨_, hb⟩ | ⟨_, _, hb⟩ | ⟨hd, _⟩
      · contradiction
      · cases hb
      · have hd' : v = Algorithm2.dead := hd
        cases hd'
        rfl
  right_inv := by
    intro v
    cases v with
    | inl v => rfl
    | inr w =>
      cases w with
      | inl pair => cases pair; rfl
      | inr b => cases b <;> rfl

noncomputable instance (n : Nat) : Fintype (Alphabet n) :=
  Fintype.ofEquiv _ (alphabetEquiv n).symm

theorem alphabet_card (n : Nat) :
    Fintype.card (Alphabet n) = 1 + 2 * Algorithm2.height n +
      2 * (if Algorithm2.height n = 0 then 1 else 2) + 3 := by
  rw [Fintype.card_congr (alphabetEquiv n)]
  simp [Algorithm2.alphabet_card, upperRoot_card]
  omega

theorem alphabet_card_ge_two (n : Nat) (hn : 2 ≤ n) :
    Fintype.card (Alphabet n) = 1 + 2 * Algorithm2.height n + 7 := by
  have hh : 0 < Algorithm2.height n := by
    by_contra h
    have hz : Algorithm2.height n = 0 := by omega
    have hle : n ≤ 1 := by
      have := (Algorithm2.height_le_iff n 0).mp (by omega : Algorithm2.height n ≤ 0)
      simpa using this
    omega
  simpa [show Algorithm2.height n ≠ 0 by omega] using alphabet_card n

theorem alphabet_card_singleton : Fintype.card (Alphabet 1) = 6 := by
  simpa [Algorithm2.singleton_height] using alphabet_card 1

theorem alphabetEquiv_lossless (n : Nat) (v : Alphabet n) :
    (alphabetEquiv n).symm (alphabetEquiv n v) = v :=
  (alphabetEquiv n).left_inv v

/-- Held tournament controls retain exactly the root level. At height zero,
the existing well-formedness theorem identifies that value as dead. -/
theorem holding_upperRoot {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) (p : Proc n) (held : Holding (s p).pc) :
    UpperRootValue n (s p).value.tournament := by
  have proj := reachable_projection reach
  have wf := Algorithm2.reachable_wellFormed proj.2 p
  have link := proj.1 p
  have root : (s p).tournamentPC = .cs ∨ (s p).tournamentPC = .release := by
    cases hp : (s p).pc <;> simp_all [Holding, Linked]
  have level : (s p).value.tournament.level = Algorithm2.height n := by
    rcases root with hc | hr
    · simpa [project, Algorithm2.LocalWF, Algorithm2.StageWF, hc] using wf.2.2
    · simpa [project, Algorithm2.LocalWF, Algorithm2.StageWF, hr] using wf.2.2
  exact ⟨level, by
    intro hz
    exact wf.2.1 (by simpa [project] using level.trans hz)⟩

/-- Lower-clock and critical-section tags occur only after the tournament
component has been released. This is derived from the concrete invariant. -/
theorem reachable_lower_cs_dead {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) (p : Proc n)
    (tag : (∃ b, (s p).value.clock = .lower b) ∨ (s p).value.clock = .cs) :
    (s p).value.tournament = Algorithm2.dead := by
  have facts := (reachable_invariant reach).localFacts p
  have link := (reachable_projection reach).1 p
  have vis : visible (s p).value.clock = true := by
    rcases tag with ⟨b, hb⟩ | hb <;> simp [hb, visible]
  cases hp : (s p).pc <;>
    simp_all [LocalFacts, Linked]

theorem reachable_register {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) (p : Proc n) : InAlphabet n (s p).value := by
  have proj := (reachable_projection reach).2
  have tour := Algorithm2.reachable_register proj p
  cases h : (s p).value.clock with
  | off => exact Or.inl ⟨tour, h⟩
  | upper b =>
    exact Or.inr (Or.inl ⟨holding_upperRoot reach p
      (reachable_upper_owner reach p (by simp [UpperOwnerFacts, IsUpper, h])), b, h⟩)
  | lower b =>
    exact Or.inr (Or.inr ⟨reachable_lower_cs_dead reach p (Or.inl ⟨b, h⟩),
      Or.inl ⟨b, h⟩⟩)
  | cs =>
    exact Or.inr (Or.inr ⟨reachable_lower_cs_dead reach p (Or.inr h), Or.inr h⟩)

theorem initial_register (n : Nat) (p : Proc n) :
    InAlphabet n ((initial n p).value) := Or.inl ⟨Or.inl rfl, rfl⟩

theorem reachable_read {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) (p : Proc n) : InAlphabet n (s p).value :=
  reachable_register reach p

theorem reachable_next_register {n : Nat} {cfg : Config n} {s t : State n}
    (reach : Reachable cfg s) (c : Command n)
    (step : next cfg s c = some t) (p : Proc n) : InAlphabet n (t p).value :=
  reachable_register (.step reach ⟨c, step, rfl⟩) p

theorem ordinary_off {n : Nat} (cfg : Config n) (s : State n)
    (p : Proc n) (h : (s p).pc = .off) :
    ordinary cfg s p = some {s p with
      pc := .lowerJoin (startJoin p false),
      value := ⟨(s p).value.tournament, .off⟩} := by
  simp [ordinary, h]

/-- The upper clock publishes its cached bit in the same whole register as
the retained tournament component. -/
theorem ordinary_upperJoin {n : Nat} (cfg : Config n) (s : State n)
    (p : Proc n) (pc : Algorithm3.PC) (c : Algorithm3.Local)
    (hpc : (s p).pc = .upperJoin pc)
    (hc : clockInstruction s p true pc = some c) :
    ordinary cfg s p = some {s p with
      pc := if c.pc = .attempt then .upperTick 0 .attempt else .upperJoin c.pc,
      value := ⟨(s p).value.tournament, clockTag true c.q⟩} := by
  simp [ordinary, hpc, hc]

theorem ordinary_upperTick {n : Nat} (cfg : Config n) (s : State n)
    (p : Proc n) (count : Nat) (pc : Algorithm3.PC) (c : Algorithm3.Local)
    (out : Local n)
    (hpc : (s p).pc = .upperTick count pc)
    (hc : clockInstruction s p true pc = some c)
    (ho : ordinary cfg s p = some out) :
    out.value = ⟨(s p).value.tournament, clockTag true c.q⟩ := by
  simp only [ordinary, hpc, hc, Option.map_some, Option.some.injEq] at ho
  subst out
  rfl

theorem ordinary_enqueue {n : Nat} (cfg : Config n) (s : State n)
    (p : Proc n) (b : Bool) (h : (s p).pc = .enqueue b) :
    ordinary cfg s p = some {s p with
      pc := .maintain (cfg.order p), tournamentPC := .idle,
      value := ⟨Algorithm2.dead, .lower b⟩} := by
  simp [ordinary, h]

theorem ordinary_publish {n : Nat} (cfg : Config n) (s : State n)
    (p : Proc n) (h : (s p).pc = .publish) :
    ordinary cfg s p = some ⟨.enter, (s p).tournamentPC,
      ⟨Algorithm2.dead, .cs⟩, (s p).behind⟩ := by
  simp [ordinary, h]

theorem ordinary_lowerTick {n : Nat} (cfg : Config n) (s : State n)
    (p : Proc n) (pc : Algorithm3.PC) (c : Algorithm3.Local)
    (hpc : (s p).pc = .lowerTick pc)
    (hc : clockInstruction s p false pc = some c) :
    ordinary cfg s p = some {s p with
      pc := if c.pc = .attempt then .test else .lowerTick c.pc,
      value := ⟨(s p).value.tournament, clockTag false c.q⟩} := by
  simp [ordinary, hpc, hc]

theorem clockValue_visible {n : Nat} (s t : State n)
    (h : ∀ q, (s q).value = (t q).value) (j : Fin (2*n)) :
    clockValue s j = clockValue t j := by
  unfold clockValue
  split
  · rename_i hj
    simp [h ⟨j.val, hj⟩]
  · rename_i hj
    simp [h ⟨j.val - n, by omega⟩]

theorem clockInstruction_visible {n : Nat} (s t : State n) (p : Proc n)
    (upper : Bool) (pc : Algorithm3.PC)
    (h : ∀ q, (s q).value = (t q).value) :
    clockInstruction s p upper pc = clockInstruction t p upper pc := by
  simp only [clockInstruction, clockValue_visible s t h]

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
  have hc (upper : Bool) (pc : Algorithm3.PC) :
      clockInstruction s p upper pc = clockInstruction t p upper pc :=
    clockInstruction_visible s t p upper pc hvisible
  unfold ordinary
  rw [hlocal]
  cases (t p).pc <;> simp [hvisible, ht, hc]

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

end EconomicalSolutions.Algorithm6

#print axioms EconomicalSolutions.Algorithm6.upperRoot_card
#print axioms EconomicalSolutions.Algorithm6.alphabetEquiv
#print axioms EconomicalSolutions.Algorithm6.alphabet_card
#print axioms EconomicalSolutions.Algorithm6.alphabet_card_ge_two
#print axioms EconomicalSolutions.Algorithm6.alphabet_card_singleton
#print axioms EconomicalSolutions.Algorithm6.alphabetEquiv_lossless
#print axioms EconomicalSolutions.Algorithm6.holding_upperRoot
#print axioms EconomicalSolutions.Algorithm6.reachable_lower_cs_dead
#print axioms EconomicalSolutions.Algorithm6.reachable_register
#print axioms EconomicalSolutions.Algorithm6.initial_register
#print axioms EconomicalSolutions.Algorithm6.reachable_read
#print axioms EconomicalSolutions.Algorithm6.reachable_next_register
#print axioms EconomicalSolutions.Algorithm6.ordinary_off
#print axioms EconomicalSolutions.Algorithm6.ordinary_upperJoin
#print axioms EconomicalSolutions.Algorithm6.ordinary_upperTick
#print axioms EconomicalSolutions.Algorithm6.ordinary_enqueue
#print axioms EconomicalSolutions.Algorithm6.ordinary_publish
#print axioms EconomicalSolutions.Algorithm6.ordinary_lowerTick
#print axioms EconomicalSolutions.Algorithm6.clockValue_visible
#print axioms EconomicalSolutions.Algorithm6.clockInstruction_visible
#print axioms EconomicalSolutions.Algorithm6.ordinary_visible
#print axioms EconomicalSolutions.Algorithm6.next_other_register
