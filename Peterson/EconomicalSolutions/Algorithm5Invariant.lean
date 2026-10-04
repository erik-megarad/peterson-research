module

public import Peterson.EconomicalSolutions.Algorithm5Projection

@[expose] public section

set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm5

abbrev priority {n : Nat} (s : State n) (p : Proc n) : Int := (s p).value.priority

def Bounds {n : Nat} (s : State n) : Prop := ∀ p, -1 ≤ priority s p ∧ priority s p < n

def Unique {n : Nat} (s : State n) : Prop :=
  ∀ p q, 0 ≤ priority s p → priority s p = priority s q → p = q

def MaxRead {n : Nat} (s : State n) (p : Proc n) (rest : List (Proc n)) (m : Int) : Prop :=
  ∀ q, q ≠ p → q ∉ rest → priority s q ≤ m

def AbsentRead {n : Nat} (s : State n) (p : Proc n) (rest : List (Proc n)) (k : Int) : Prop :=
  ∀ q, q ≠ p → q ∉ rest → priority s q ≠ k - 1

/-- These scan facts concern the *current* values of already-read peers.
Their step proof below is the stale-observation argument; they are never guards. -/
def QueueFacts {n : Nat} (s : State n) (p : Proc n) : Prop :=
  match (s p).pc with
  | .down | .idle | .request | .acquire => priority s p = -1
  | .capacity rest m => priority s p = -1 ∧ -1 ≤ m ∧ m < n ∧ MaxRead s p rest m
  | .choose rest m => priority s p = -1 ∧ -1 ≤ m ∧ m < (n : Int) - 1 ∧
      MaxRead s p rest m ∧ (∀ q, q ≠ p → priority s q < (n : Int) - 1)
  | .enqueue v => priority s p = -1 ∧ 0 ≤ v ∧ v < n ∧ (∀ q, q ≠ p → priority s q < v)
  | .complete | .depart | .test => 0 ≤ priority s p
  | .absent rest k => priority s p = k ∧ 0 < k ∧ AbsentRead s p rest k
  | .prepare k => priority s p = k ∧ 0 < k ∧ AbsentRead s p [] k
  | .decrement v => priority s p = v + 1 ∧ 0 ≤ v ∧ AbsentRead s p [] (v + 1)
  | .enter | .cs | .release => priority s p = 0

structure Invariant {n : Nat} (s : State n) : Prop where
  bounds : Bounds s
  unique : Unique s
  facts : ∀ p, QueueFacts s p

/-- Classification of actual writes, derived from the invariant of the
pre-state. The interpreter itself has no such condition. -/
inductive Change {n : Nat} (s : State n) (p : Proc n) (l : Local n) : Prop where
  | same : l.value.priority = priority s p → Change s p l
  | reset : l.value.priority = -1 → Change s p l
  | enqueue : Holding (s p).pc → 0 ≤ l.value.priority → l.value.priority < n →
      (∀ q, q ≠ p → priority s q < l.value.priority) → Change s p l
  | decrement : priority s p = l.value.priority + 1 → 0 ≤ l.value.priority →
      (∀ q, q ≠ p → priority s q ≠ l.value.priority) → Change s p l

theorem tournamentInstruction_priority {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {l : Local n} (h : tournamentInstruction cfg s p = some l) :
    l.value.priority = priority s p := by
  unfold tournamentInstruction at h
  cases ho : Algorithm2.ordinary cfg.tournament p (project s) <;> simp_all
  subst l; rfl

theorem ordinary_change {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {l : Local n} (facts : QueueFacts s p) (h : ordinary cfg s p = some l) : Change s p l := by
  cases hp : (s p).pc
  all_goals try (rename_i rest m; cases rest)
  all_goals simp only [ordinary, hp] at h
  all_goals try contradiction
  case request | acquire => exact .same (tournamentInstruction_priority h)
  case enqueue v =>
    simp only [Option.some.injEq] at h; subst l
    simp only [QueueFacts, hp] at facts
    exact .enqueue (by simp [Holding, hp]) facts.2.1 facts.2.2.1 facts.2.2.2
  case decrement v =>
    simp only [Option.some.injEq] at h; subst l
    simp only [QueueFacts, hp] at facts
    exact .decrement facts.1 facts.2.1 (by simpa [AbsentRead] using facts.2.2)
  case release =>
    simp only [Option.some.injEq] at h; subst l
    exact .reset rfl
  all_goals try (split at h)
  all_goals simp only [Option.some.injEq] at h
  all_goals subst l; exact .same rfl

theorem change_bounds {n : Nat} {s : State n} {p : Proc n} {l : Local n}
    (positive : 0 < n) (bound : Bounds s) (change : Change s p l) :
    Bounds (setLocal s p l) := by
  intro q
  by_cases he : q = p
  · subst q
    simp only [priority, setLocal_self]
    cases change with
    | same h => simpa [h] using bound p
    | reset h => have := positive; simp only [h]; constructor <;> omega
    | enqueue _ lo hi => constructor <;> omega
    | decrement eq lo => have := (bound p).2; constructor <;> omega
  · simpa [priority, he] using bound q

theorem change_unique {n : Nat} {s : State n} {p : Proc n} {l : Local n}
    (unique : Unique s) (change : Change s p l) : Unique (setLocal s p l) := by
  have unequal (q : Proc n) (other : q ≠ p) (nonneg : 0 ≤ l.value.priority) :
      l.value.priority ≠ priority s q := by
    cases change with
    | same h =>
      intro eq
      exact other (unique p q (by omega) (by omega)).symm
    | reset h => omega
    | enqueue _ _ _ above => have := above q other; omega
    | decrement _ _ absent => exact (absent q other).symm
  intro a b nonneg same
  by_cases ha : a = p
  · subst a
    by_cases hb : b = p
    · exact hb.symm
    · simp only [priority, setLocal_self, setLocal_other s p b l hb] at same nonneg
      exact (unequal b hb nonneg same).elim
  · by_cases hb : b = p
    · subst b
      simp only [priority, setLocal_self, setLocal_other s p a l ha] at same nonneg
      exact (unequal a ha (by omega) same.symm).elim
    · simp only [priority, setLocal_other s p a l ha, setLocal_other s p b l hb] at same nonneg
      exact unique a b nonneg same

/-- While p owns admission, a peer can only decrease or reset. A second
insertion is ruled out by the proved concrete tournament projection. -/
theorem change_le {n : Nat} {cfg : Config n} {s : State n} {p actor : Proc n}
    {l : Local n} (reach : Reachable cfg s) (held : Holding (s p).pc)
    (other : actor ≠ p) (change : Change s actor l) {m : Int}
    (floor : -1 ≤ m) (before : priority s actor ≤ m) : l.value.priority ≤ m := by
  cases change with
  | same h => omega
  | reset h => omega
  | enqueue owner _ _ _ => exact (other (holding_unique reach owner held)).elim
  | decrement h _ _ => omega

/-- A retained k protects a scanned vacancy k-1. A new insertion is above k;
a decrement into k-1 would start at k, contradicting existing uniqueness.
This remains true during arbitrary delays and peer failure/restart episodes. -/
theorem change_absent {n : Nat} {s : State n} {p actor : Proc n} {l : Local n}
    (unique : Unique s) (other : actor ≠ p) (change : Change s actor l)
    {k : Int} (own : priority s p = k) (positive : 0 < k)
    (before : priority s actor ≠ k - 1) : l.value.priority ≠ k - 1 := by
  cases change with
  | same h => omega
  | reset h => omega
  | enqueue _ _ _ above => have := above p other.symm; omega
  | decrement h _ _ =>
    intro bad
    exact other (unique actor p (by omega) (by omega))

theorem maxRead_transport {n : Nat} {cfg : Config n} {s : State n}
    {p actor : Proc n} {l : Local n} (reach : Reachable cfg s)
    (held : Holding (s p).pc) (other : p ≠ actor) (change : Change s actor l)
    {rest : List (Proc n)} {m : Int} (floor : -1 ≤ m) (read : MaxRead s p rest m) :
    MaxRead (setLocal s actor l) p rest m := by
  intro q qp qr
  by_cases qa : q = actor
  · subst q
    simpa [priority] using change_le reach held other.symm change floor (read actor qp qr)
  · simpa [priority, qa] using read q qp qr

theorem absentRead_transport {n : Nat} {s : State n} {p actor : Proc n} {l : Local n}
    (unique : Unique s) (other : p ≠ actor) (change : Change s actor l)
    {rest : List (Proc n)} {k : Int} (own : priority s p = k) (positive : 0 < k)
    (read : AbsentRead s p rest k) : AbsentRead (setLocal s actor l) p rest k := by
  intro q qp qr
  by_cases qa : q = actor
  · subst q
    simpa [priority] using change_absent unique other.symm change own positive (read actor qp qr)
  · simpa [priority, qa] using read q qp qr

theorem strict_transport {n : Nat} {cfg : Config n} {s : State n}
    {p actor : Proc n} {l : Local n} (reach : Reachable cfg s)
    (held : Holding (s p).pc) (other : p ≠ actor) (change : Change s actor l)
    {m : Int} (floor : 0 ≤ m) (before : ∀ q, q ≠ p → priority s q < m) :
    ∀ q, q ≠ p → priority (setLocal s actor l) q < m := by
  intro q qp
  by_cases qa : q = actor
  · subst q
    have h := change_le reach held other.symm change (m := m - 1) (by omega)
      (by have := before actor qp; omega)
    simpa [priority] using (show l.value.priority < m by omega)
  · simpa [priority, qa] using before q qp

theorem change_other_facts {n : Nat} {cfg : Config n} {s : State n}
    {p actor : Proc n} {l : Local n} (reach : Reachable cfg s)
    (inv : Invariant s) (other : p ≠ actor) (change : Change s actor l) :
    QueueFacts (setLocal s actor l) p := by
  have facts := inv.facts p
  have same : priority (setLocal s actor l) p = priority s p := by simp [priority, other]
  cases hp : (s p).pc
  all_goals simp only [QueueFacts, setLocal_other s actor p l other, hp] at facts ⊢
  all_goals rw [same]
  case capacity rest m =>
    exact ⟨facts.1, facts.2.1, facts.2.2.1,
      maxRead_transport reach (by simp [Holding, hp]) other change facts.2.1 facts.2.2.2⟩
  case choose rest m =>
    exact ⟨facts.1, facts.2.1, facts.2.2.1,
      maxRead_transport reach (by simp [Holding, hp]) other change facts.2.1 facts.2.2.2.1,
      strict_transport reach (by simp [Holding, hp]) other change
        (by have := cfg.tournament.positive; omega) facts.2.2.2.2⟩
  case enqueue v =>
    exact ⟨facts.1, facts.2.1, facts.2.2.1,
      strict_transport reach (by simp [Holding, hp]) other change facts.2.1 facts.2.2.2⟩
  case absent rest k | prepare k =>
    exact ⟨facts.1, facts.2.1,
      absentRead_transport inv.unique other change facts.1 facts.2.1 facts.2.2⟩
  case decrement v =>
    exact ⟨facts.1, facts.2.1,
      absentRead_transport inv.unique other change facts.1 (by omega) facts.2.2⟩
  all_goals simpa [same] using facts

@[simp] theorem maxRead_setLocal {n : Nat} (s : State n) (p : Proc n) (l : Local n)
    (rest : List (Proc n)) (m : Int) :
    MaxRead (setLocal s p l) p rest m ↔ MaxRead s p rest m := by
  simp +contextual [MaxRead, priority, setLocal]

@[simp] theorem absentRead_setLocal {n : Nat} (s : State n) (p : Proc n) (l : Local n)
    (rest : List (Proc n)) (k : Int) :
    AbsentRead (setLocal s p l) p rest k ↔ AbsentRead s p rest k := by
  simp +contextual [AbsentRead, priority, setLocal]

@[simp] theorem peers_setLocal {n : Nat} (s : State n) (p : Proc n) (l : Local n)
    (m : Int) :
    (∀ q, q ≠ p → priority (setLocal s p l) q < m) ↔
      (∀ q, q ≠ p → priority s q < m) := by
  simp +contextual [priority, setLocal]

theorem maxRead_start {n : Nat} (cfg : Config n) (s : State n) (p : Proc n) (m : Int) :
    MaxRead s p (cfg.order p) m := by
  intro q other missing
  exact (missing ((cfg.complete p q).mpr other)).elim

theorem absentRead_start {n : Nat} (cfg : Config n) (s : State n) (p : Proc n) (k : Int) :
    AbsentRead s p (cfg.order p) k := by
  intro q other missing
  exact (missing ((cfg.complete p q).mpr other)).elim

theorem maxRead_cons {n : Nat} {s : State n} {p q : Proc n} {rest : List (Proc n)} {m : Int}
    (read : MaxRead s p (q :: rest) m) : MaxRead s p rest (max m (priority s q)) := by
  intro r other missing
  by_cases eq : r = q
  · subst r; exact le_max_right _ _
  · exact (read r other (by simp [eq, missing])).trans (le_max_left _ _)

theorem absentRead_cons {n : Nat} {s : State n} {p q : Proc n} {rest : List (Proc n)} {k : Int}
    (read : AbsentRead s p (q :: rest) k) (sample : priority s q ≠ k - 1) :
    AbsentRead s p rest k := by
  intro r other missing
  by_cases eq : r = q
  · simpa [eq] using sample
  · exact read r other (by simp [eq, missing])

theorem ordinary_own_facts {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {l : Local n} (inv : Invariant s) (h : ordinary cfg s p = some l) :
    QueueFacts (setLocal s p l) p := by
  have facts := inv.facts p
  have positive := cfg.tournament.positive
  cases hp : (s p).pc
  all_goals simp only [QueueFacts, hp, priority] at facts
  case down => simp [ordinary, hp] at h
  case request | acquire =>
    simp only [ordinary, hp, tournamentInstruction] at h
    cases ht : Algorithm2.ordinary cfg.tournament p (project s) with
    | none => simp [ht] at h
    | some t =>
      simp only [ht, Option.map_some, Option.some.injEq] at h
      subst l
      split
      · simpa [QueueFacts, priority, facts, show (-1 : Int) < n by omega]
          using maxRead_start cfg s p (-1)
      · simpa [QueueFacts, priority] using facts
  case capacity rest m =>
    cases rest with
    | nil =>
      simp only [ordinary, hp, Option.some.injEq] at h
      split at h
      · rename_i room
        subst l
        simp only [QueueFacts, setLocal_self, priority, maxRead_setLocal, peers_setLocal]
        refine ⟨facts.1, by omega, by omega, maxRead_start cfg s p (-1), ?_⟩
        intro q other
        have hq := facts.2.2.2 q other (by simp)
        change (s q).value.priority ≤ m at hq
        omega
      · subst l
        simpa [QueueFacts, priority, facts.1, show (-1 : Int) < n by omega]
          using maxRead_start cfg s p (-1)
    | cons q rest =>
      simp only [ordinary, hp, Option.some.injEq] at h; subst l
      simp only [QueueFacts, setLocal_self, priority, maxRead_setLocal]
      exact ⟨facts.1, (facts.2.1.trans (le_max_left _ _)),
        max_lt facts.2.2.1 (inv.bounds q).2, maxRead_cons facts.2.2.2⟩
  case choose rest m =>
    cases rest with
    | nil =>
      simp only [ordinary, hp, Option.some.injEq] at h; subst l
      simp only [QueueFacts, setLocal_self, priority, peers_setLocal]
      refine ⟨facts.1, by omega, by omega, ?_⟩
      intro q other
      have hq := facts.2.2.2.1 q other (by simp)
      change (s q).value.priority ≤ m at hq
      omega
    | cons q rest =>
      have upper : priority s q < (n : Int) - 1 := by
        change (s q).value.priority < (n : Int) - 1
        by_cases eq : q = p
        · subst q; omega
        · exact facts.2.2.2.2 q eq
      simp only [ordinary, hp, Option.some.injEq] at h; subst l
      simp only [QueueFacts, setLocal_self, priority, maxRead_setLocal, peers_setLocal]
      exact ⟨facts.1, (facts.2.1.trans (le_max_left _ _)),
        max_lt facts.2.2.1 upper, maxRead_cons facts.2.2.2.1, facts.2.2.2.2⟩
  case enqueue v =>
    simp only [ordinary, hp, Option.some.injEq] at h; subst l
    simpa [QueueFacts, priority] using facts.2.1
  case test =>
    simp only [ordinary, hp, Option.some.injEq] at h
    split at h
    · rename_i zero
      subst l
      simpa [QueueFacts, priority] using zero
    · rename_i nonzero
      subst l
      simp only [QueueFacts, setLocal_self, priority, absentRead_setLocal]
      exact ⟨trivial, by omega, absentRead_start cfg s p _⟩
  case absent rest k =>
    cases rest with
    | nil =>
      simp only [ordinary, hp, Option.some.injEq] at h; subst l
      simpa [QueueFacts, priority] using facts
    | cons q rest =>
      simp only [ordinary, hp, Option.some.injEq] at h
      split at h
      · subst l
        simp only [QueueFacts, setLocal_self, priority, absentRead_setLocal]
        exact ⟨facts.1, facts.2.1, absentRead_start cfg s p k⟩
      · rename_i sample
        subst l
        simp only [QueueFacts, setLocal_self, priority, absentRead_setLocal]
        exact ⟨facts.1, facts.2.1, absentRead_cons facts.2.2 sample⟩
  case prepare k =>
    simp only [ordinary, hp, Option.some.injEq] at h; subst l
    simp only [QueueFacts, setLocal_self, priority, absentRead_setLocal]
    exact ⟨by omega, by omega, by simpa using facts.2.2⟩
  case decrement v =>
    simp only [ordinary, hp, Option.some.injEq] at h; subst l
    simpa [QueueFacts, priority] using facts.2.1
  case release =>
    simp only [ordinary, hp, Option.some.injEq] at h; subst l
    simp [QueueFacts, priority, dead]
  all_goals simp only [ordinary, hp, Option.some.injEq] at h; subst l
  all_goals simpa [QueueFacts, priority] using facts

theorem invariant_initial {n : Nat} (cfg : Config n) : Invariant (initial n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p; have := cfg.tournament.positive; simp [Bounds, priority, initial, dead]; omega
  · intro p q h; simp [priority, initial, dead] at h
  · intro p; rfl

theorem invariant_next {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    (reach : Reachable cfg s) (inv : Invariant s) (h : next cfg s c = some t) : Invariant t := by
  cases c with
  | stutter => have he : s = t := Option.some.inj h; simpa [← he] using inv
  | run actor =>
    simp only [next] at h
    cases ho : ordinary cfg s actor with
    | none => simp [ho] at h
    | some l =>
      simp only [ho, Option.map_some, Option.some.injEq] at h; subst t
      have change := ordinary_change (inv.facts actor) ho
      refine ⟨change_bounds cfg.tournament.positive inv.bounds change,
        change_unique inv.unique change, ?_⟩
      intro p
      by_cases other : p = actor
      · subst p; exact ordinary_own_facts inv ho
      · exact change_other_facts reach inv other change
  | fail actor | restart actor =>
    simp only [next] at h
    split at h
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at h; subst t
    all_goals refine ⟨change_bounds cfg.tournament.positive inv.bounds (.reset rfl),
      change_unique inv.unique (.reset rfl), ?_⟩
    all_goals intro p; by_cases other : p = actor
    all_goals try (subst p; simp [QueueFacts, priority, dead])
    all_goals exact change_other_facts reach inv other (.reset rfl)

theorem reachable_invariant {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) : Invariant s := by
  induction reach with
  | initial => exact invariant_initial cfg
  | step reach edge ih =>
    obtain ⟨c, hc, _⟩ := edge
    exact invariant_next reach ih hc

/-- Every initialized finite execution has priorities in {-1,0,...,n-1}; the
broad integer interpreter does not enforce this range at writes. -/
theorem priority_bounds {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) : Bounds s := (reachable_invariant reach).bounds

theorem priority_unique {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) : Unique s := (reachable_invariant reach).unique

theorem critical_zero {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) {p : Proc n} (critical : (s p).pc = .cs) : priority s p = 0 := by
  have facts := (reachable_invariant reach).facts p
  simpa [QueueFacts, critical] using facts

/-- Theorem 4-2 for the exact reviewed separate-access reconstruction, all
positive populations and fixed complete scan orders, arbitrary repetitions,
failures, restarts and delayed writes. No fairness assumption is used. -/
theorem safety : SafetyTarget := by
  intro n cfg s reach p q hp hq
  exact priority_unique reach p q (by rw [critical_zero reach hp])
    ((critical_zero reach hp).trans (critical_zero reach hq).symm)

end EconomicalSolutions.Algorithm5

#print axioms EconomicalSolutions.Algorithm5.priority_bounds
#print axioms EconomicalSolutions.Algorithm5.priority_unique
#print axioms EconomicalSolutions.Algorithm5.critical_zero
#print axioms EconomicalSolutions.Algorithm5.safety
