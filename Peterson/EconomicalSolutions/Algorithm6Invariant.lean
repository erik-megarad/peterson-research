module

public import Peterson.EconomicalSolutions.Algorithm6Projection

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
namespace EconomicalSolutions.Algorithm6

/-- A clock instruction cannot erase an occupied position. This is a direct
fact about the proceedings code, with no liveness or scan-history premise. -/
theorem clock_occupied {m : Nat} {s : Algorithm3.State m} {i : Fin m}
    {b : Bool} {c : Algorithm3.Local} (own : (s i).q = some b)
    (h : Algorithm3.ordinary s i = some c) : ∃ v, c.q = some v := by
  cases hp : (s i).pc
  all_goals simp only [Algorithm3.ordinary, hp, own, Option.bind_some] at h
  all_goals repeat (split at h)
  all_goals simp_all <;> aesop

theorem clock_lower_occupied {n : Nat} {s : State n} {p : Proc n}
    {pc : Algorithm3.PC} {c : Algorithm3.Local} {b : Bool}
    (own : (s p).value.clock = .lower b) (h : clockInstruction s p false pc = some c) :
    ∃ v, c.q = some v := by
  unfold clockInstruction at h
  apply clock_occupied (b := b) (h := h)
  simp [clockValue, position, own]

def LocalFacts {n : Nat} (l : Local n) : Prop :=
  match l.pc with
  | .maintain _ | .lowerTick _ | .test => ∃ b, l.value.clock = .lower b
  | .publish => (∃ b, l.value.clock = .lower b) ∧ l.behind = ∅
  | .enter | .cs | .release => l.value.clock = .cs ∧ l.behind = ∅
  | _ => visible l.value.clock = false

@[simp] theorem upper_invisible (q : Option Bool) : visible (clockTag true q) = false := by
  cases q <;> rfl

theorem tournamentInstruction_fields {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {l : Local n} (h : tournamentInstruction cfg s p = some l) :
    l.value.clock = (s p).value.clock ∧ l.behind = (s p).behind ∧
      (l.pc = .acquire ∨ ∃ cp, l.pc = .upperJoin cp) := by
  unfold tournamentInstruction at h
  obtain ⟨t, _, h⟩ := Option.map_eq_some_iff.mp h
  subst l
  split <;> simp

theorem ordinary_localFacts {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {l : Local n} (facts : LocalFacts (s p)) (h : ordinary cfg s p = some l) : LocalFacts l := by
  cases hp : (s p).pc
  case' build rest => cases rest
  case' maintain rest => cases rest
  case' lowerJoin cp => cases cp
  all_goals simp only [ordinary, hp] at h
  all_goals try contradiction
  case request | acquire =>
    obtain ⟨tag, _, pc⟩ := tournamentInstruction_fields h
    rcases pc with pc | ⟨cp, pc⟩ <;> simp_all [LocalFacts]
  case lowerTick cp =>
    obtain ⟨c, hc, h⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨b, hb⟩ : ∃ b, (s p).value.clock = .lower b := by simpa [LocalFacts, hp] using facts
    obtain ⟨v, hv⟩ := clock_lower_occupied hb hc
    subst l
    split <;> simp [LocalFacts, hv, clockTag]
  all_goals try (rw [Option.map_eq_some_iff] at h; obtain ⟨c, hc, h⟩ := h)
  all_goals repeat (split at h)
  all_goals try simp only [Option.some.injEq] at h
  all_goals subst l
  all_goals simp_all [LocalFacts, dead]
  all_goals rfl

/-- Already inspected identifiers remain in B while still visible; uninspected
identifiers are tracked by the actual remaining cursor, not an atomic snapshot. -/
def Coverage {n : Nat} (s : State n) (p : Proc n) (rest : List (Proc n))
    (B : Finset (Proc n)) : Prop :=
  ∀ q, q ≠ p → visible (s q).value.clock = true → q ∈ rest ∨ q ∈ B

def ScanFacts {n : Nat} (s : State n) (p : Proc n) : Prop :=
  match (s p).pc with
  | .build rest => Coverage s p rest (s p).behind
  | .off | .lowerJoin _ | .complete _ | .enqueue _ => Coverage s p [] (s p).behind
  | _ => True

/-- This pairwise blocking fact is a conclusion of the concrete execution.
It does not assume FIFO, global list order, or clock observations. -/
def Blocking {n : Nat} (s : State n) : Prop :=
  ∀ p q, p ≠ q → visible (s p).value.clock = true → visible (s q).value.clock = true →
    p ∈ (s q).behind ∨ q ∈ (s p).behind

structure Invariant {n : Nat} (s : State n) : Prop where
  localFacts : ∀ p, LocalFacts (s p)
  scanFacts : ∀ p, ScanFacts s p
  blocking : Blocking s

/-- Classifies changes to queue visibility and surviving list entries. These
are proved consequences, never interpreter guards. -/
inductive Change {n : Nat} (s : State n) (p : Proc n) (l : Local n) : Prop where
  | gone : visible l.value.clock = false → Change s p l
  | retained : visible (s p).value.clock = true →
      (∀ q, visible (s q).value.clock = true → q ∈ (s p).behind → q ∈ l.behind) → Change s p l
  | arrival : Holding (s p).pc → Coverage s p [] l.behind → Change s p l

theorem ordinary_change {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {l : Local n} (facts : LocalFacts (s p)) (scan : ScanFacts s p)
    (h : ordinary cfg s p = some l) : Change s p l := by
  cases hp : (s p).pc
  case' build rest => cases rest
  case' maintain rest => cases rest
  case' lowerJoin cp => cases cp
  all_goals simp only [ordinary, hp] at h
  all_goals try contradiction
  case request | acquire =>
    apply Change.gone
    rw [(tournamentInstruction_fields h).1]
    simpa [LocalFacts, hp] using facts
  case enqueue b =>
    simp only [Option.some.injEq] at h; subst l
    exact .arrival (by simp [Holding, hp]) (by simpa [ScanFacts, hp] using scan)
  all_goals try (rw [Option.map_eq_some_iff] at h; obtain ⟨c, hc, h⟩ := h)
  all_goals repeat (split at h)
  all_goals try simp only [Option.some.injEq] at h
  all_goals subst l
  all_goals first
    | (apply Change.gone; simpa [LocalFacts, hp] using facts)
    | (apply Change.gone; rfl)
    | (apply Change.retained
       · cases ht : (s p).value.clock <;> simp_all [LocalFacts, visible]
       · intro q vis mem
         simp_all only [Finset.mem_erase] <;> aesop)

@[simp] theorem coverage_self {n : Nat} {s : State n} {p : Proc n} {l : Local n}
    {rest : List (Proc n)} {B : Finset (Proc n)} :
    Coverage (setLocal s p l) p rest B ↔ Coverage s p rest B := by
  unfold Coverage
  simp only [setLocal]
  constructor <;> intro h q ne vis
  · exact h q ne (by simpa [ne] using vis)
  · exact h q ne (by simpa [ne] using vis)

theorem coverage_transport {n : Nat} {cfg : Config n} {s : State n} {p actor : Proc n}
    {l : Local n} {rest : List (Proc n)} {B : Finset (Proc n)}
    (reach : Reachable cfg s) (held : Holding (s p).pc) (other : p ≠ actor)
    (change : Change s actor l) (before : Coverage s p rest B) :
    Coverage (setLocal s actor l) p rest B := by
  intro q qp vis
  by_cases qa : q = actor
  · subst q
    simp only [setLocal_self] at vis
    cases change with
    | gone absent => simp [absent] at vis
    | retained old _ => exact before actor qp old
    | arrival owner _ => exact (other (holding_unique reach held owner)).elim
  · exact before q qp (by simpa [qa] using vis)

theorem other_scanFacts {n : Nat} {cfg : Config n} {s : State n} {p actor : Proc n}
    {l : Local n} (reach : Reachable cfg s) (before : ScanFacts s p)
    (other : p ≠ actor) (change : Change s actor l) : ScanFacts (setLocal s actor l) p := by
  cases hp : (s p).pc
  all_goals simp only [ScanFacts, setLocal_other s actor p l other, hp] at before ⊢
  all_goals exact coverage_transport reach (by simp [Holding, hp]) other change before

theorem change_blocking {n : Nat} {s : State n} {actor : Proc n} {l : Local n}
    (before : Blocking s) (change : Change s actor l) : Blocking (setLocal s actor l) := by
  have pair (q : Proc n) (ne : actor ≠ q) (vis : visible l.value.clock = true)
      (qvis : visible (s q).value.clock = true) :
      actor ∈ (s q).behind ∨ q ∈ l.behind := by
    cases change with
    | gone gone => simp [gone] at vis
    | retained old keep =>
      rcases before actor q ne old qvis with h | h
      · exact Or.inl h
      · exact Or.inr (keep q qvis h)
    | arrival _ coverage =>
      exact Or.inr (by simpa using coverage q ne.symm qvis)
  intro p q ne pv qv
  by_cases pa : p = actor
  · subst p
    have qa := ne.symm
    simpa [qa] using pair q ne (by simpa using pv) (by simpa [qa] using qv)
  · by_cases qa : q = actor
    · subst q
      have h := pair p (Ne.symm pa) (by simpa using qv) (by simpa [pa] using pv)
      simpa [pa] using h.symm
    · simpa [pa, qa] using before p q ne (by simpa [pa] using pv) (by simpa [qa] using qv)

theorem coverage_read {n : Nat} {s : State n} {p q : Proc n} {rest : List (Proc n)}
    {B : Finset (Proc n)} (before : Coverage s p (q :: rest) B) :
    Coverage s p rest (if visible (s q).value.clock then insert q B else B) := by
  intro r rp rv
  rcases before r rp rv with member | member
  · simp only [List.mem_cons] at member
    rcases member with eq | tail
    · subst r; simp [rv]
    · exact Or.inl tail
  · right
    split <;> simp_all

theorem ordinary_scanFacts {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {l : Local n} (scan : ScanFacts s p) (h : ordinary cfg s p = some l) :
    ScanFacts (setLocal s p l) p := by
  cases hp : (s p).pc
  case' build rest => cases rest
  case' maintain rest => cases rest
  case' lowerJoin cp => cases cp
  all_goals simp only [ordinary, hp] at h
  all_goals try contradiction
  case request | acquire =>
    rcases (tournamentInstruction_fields h).2.2 with pc | ⟨cp, pc⟩ <;>
      simp [ScanFacts, pc]
  case build.cons q rest =>
    simp only [Option.some.injEq] at h; subst l
    simp only [ScanFacts, setLocal_self, coverage_self]
    exact coverage_read (by simpa [ScanFacts, hp] using scan)
  all_goals try (rw [Option.map_eq_some_iff] at h; obtain ⟨c, hc, h⟩ := h)
  all_goals repeat (split at h)
  all_goals try simp only [Option.some.injEq] at h
  all_goals subst l
  all_goals simp_all [ScanFacts]
  all_goals intro q qp _
  all_goals exact Or.inl ((cfg.complete p q).mpr qp)

theorem replace_invariant {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {l : Local n} (reach : Reachable cfg s) (inv : Invariant s)
    (localFacts : LocalFacts l) (scan : ScanFacts (setLocal s p l) p)
    (change : Change s p l) : Invariant (setLocal s p l) := by
  refine ⟨?_, ?_, change_blocking inv.blocking change⟩
  · intro q
    by_cases eq : q = p
    · subst q; simpa using localFacts
    · simpa [eq] using inv.localFacts q
  · intro q
    by_cases eq : q = p
    · subst q; exact scan
    · exact other_scanFacts reach (inv.scanFacts q) eq change

theorem next_invariant {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    (reach : Reachable cfg s) (inv : Invariant s) (step : next cfg s c = some t) : Invariant t := by
  cases c with
  | stutter =>
    have eq : s = t := Option.some.inj step
    simpa [← eq] using inv
  | run p =>
    obtain ⟨l, h, rfl⟩ := Option.map_eq_some_iff.mp step
    exact replace_invariant reach inv (ordinary_localFacts (inv.localFacts p) h)
      (ordinary_scanFacts (inv.scanFacts p) h)
      (ordinary_change (inv.localFacts p) (inv.scanFacts p) h)
  | fail p | restart p =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals apply replace_invariant reach inv
    all_goals first
      | exact Change.gone rfl
      | simp [reset, dead, LocalFacts, ScanFacts, visible]

theorem reachable_invariant {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) : Invariant s := by
  induction reach with
  | initial =>
    constructor
    · intro p; rfl
    · intro p; trivial
    · intro p q _ pv; simp [initial, reset, dead, visible] at pv
  | step before edge ih =>
    obtain ⟨c, step, _⟩ := edge
    exact next_invariant before ih step

/-- Finite-execution safety for every configured positive population. Clock
success, fairness, list order and FIFO are absent from the theorem premises. -/
theorem safety : SafetyTarget := by
  intro n cfg s reach p q hp hq
  have inv := reachable_invariant reach
  have fp := inv.localFacts p
  have fq := inv.localFacts q
  simp only [LocalFacts, hp, hq] at fp fq
  by_contra ne
  have h := inv.blocking p q ne (by simp [fp.1, visible]) (by simp [fq.1, visible])
  simpa [fp.2, fq.2] using h

end EconomicalSolutions.Algorithm6

#print axioms EconomicalSolutions.Algorithm6.reachable_invariant
#print axioms EconomicalSolutions.Algorithm6.safety
