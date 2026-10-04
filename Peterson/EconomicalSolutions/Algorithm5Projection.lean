module

public import Peterson.EconomicalSolutions.Algorithm5

@[expose] public section

set_option linter.unusedSimpArgs false

namespace EconomicalSolutions.Algorithm5

/-- A structural connection between the two private interpreters. No priority
bound, unique owner or queue order occurs in this predicate. -/
def Linked {n : Nat} (l : Local n) : Prop :=
  match l.pc with
  | .acquire => l.tournamentPC ≠ .down
  | .down => l.tournamentPC = .down ∧ l.value.tournament = Algorithm2.dead
  | .idle | .request | .test | .absent _ _ | .prepare _ | .decrement _ | .enter | .cs | .release =>
      l.tournamentPC = .idle ∧ l.value.tournament = Algorithm2.dead
  | .depart => l.tournamentPC = .release
  | .capacity _ _ | .choose _ _ | .enqueue _ | .complete => l.tournamentPC = .cs

def Holding {n : Nat} (pc : PC n) : Prop :=
  match pc with
  | .capacity _ _ | .choose _ _ | .enqueue _ | .complete => True
  | _ => False

@[simp] theorem setLocal_self {n : Nat} (s : State n) (p : Proc n) (l : Local n) :
    setLocal s p l p = l := by simp [setLocal]

@[simp] theorem setLocal_other {n : Nat} (s : State n) (p q : Proc n) (l : Local n)
    (h : q ≠ p) : setLocal s p l q = s q := by simp [setLocal, h]

@[simp] theorem project_setLocal {n : Nat} (s : State n) (p : Proc n) (l : Local n) :
    project (setLocal s p l) = Algorithm2.setLocal (project s) p ⟨l.tournamentPC, l.value.tournament⟩ := by
  funext q
  by_cases h : q = p <;> simp [project, setLocal, Algorithm2.setLocal, h]

theorem tournamentInstruction_linked {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {l : Local n} (h : tournamentInstruction cfg s p = some l) : Linked l := by
  unfold tournamentInstruction at h
  cases ho : Algorithm2.ordinary cfg.tournament p (project s) with
  | none => simp [ho] at h
  | some t =>
    simp only [ho, Option.map_some, Option.some.injEq] at h
    subst l
    have rn (c : Algorithm2.Continuation) (k : Nat) (x : Algorithm2.Value) :
        Algorithm2.resume cfg.tournament p c k x ≠ .down := by
      cases c <;> simp only [Algorithm2.resume]
      all_goals repeat first | split | simp [Algorithm2.scan]
    have hn : t.pc ≠ .down := by
      cases ht : (project s p).pc
      case scan c k remaining =>
        cases remaining <;> simp only [Algorithm2.ordinary, ht, Option.some.injEq] at ho
        all_goals subst t; dsimp
        all_goals repeat first | apply rn | split | simp [Algorithm2.scan]
      all_goals simp only [Algorithm2.ordinary, ht] at ho
      all_goals try contradiction
      all_goals simp only [Option.some.injEq] at ho
      all_goals subst t
      all_goals dsimp
      all_goals repeat first | assumption | apply rn | split | simp [Algorithm2.scan]
    split <;> simp_all [Linked, dead]

theorem ordinary_linked {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {l : Local n} (link : Linked (s p)) (h : ordinary cfg s p = some l) : Linked l := by
  cases hp : (s p).pc
  all_goals try (rename_i remaining m; cases remaining)
  all_goals simp only [ordinary, hp] at h
  all_goals try exact tournamentInstruction_linked h
  all_goals try contradiction
  all_goals try (split at h)
  all_goals try simp only [Option.some.injEq] at h
  all_goals subst l; simp_all [Linked, dead]

def projectCommand {n : Nat} (s : State n) : Command n → Algorithm2.Command n
  | .run p => match (s p).pc with
      | .request | .acquire | .complete | .depart => .run p
      | _ => .stutter
  | .fail p => if (s p).tournamentPC = .down then .stutter else .fail p
  | .restart p => .restart p
  | .stutter => .stutter

theorem ordinary_projection {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {l : Local n} (link : Linked (s p)) (h : ordinary cfg s p = some l) :
    Algorithm2.next cfg.tournament (project s) (projectCommand s (.run p)) =
      some (project (setLocal s p l)) := by
  cases hp : (s p).pc
  all_goals try (rename_i remaining m; cases remaining)
  all_goals simp only [ordinary, hp] at h
  all_goals try contradiction
  case request | acquire =>
    simp only [tournamentInstruction] at h
    cases ho : Algorithm2.ordinary cfg.tournament p (project s) with
    | none => simp [ho] at h
    | some t =>
      simp only [ho, Option.map_some, Option.some.injEq] at h
      subst l
      simp [projectCommand, hp, Algorithm2.next, ho]
  case complete =>
    simp only [Option.some.injEq] at h; subst l
    have hl : (s p).tournamentPC = .cs := by simpa [Linked, hp] using link
    simp [projectCommand, hp, Algorithm2.next, Algorithm2.ordinary, project, hl,
      Algorithm2.setLocal, setLocal]
  case depart =>
    simp only [Option.some.injEq] at h; subst l
    have hl : (s p).tournamentPC = .release := by simpa [Linked, hp] using link
    simp [projectCommand, hp, Algorithm2.next, Algorithm2.ordinary, project, hl,
      Algorithm2.setLocal, setLocal]
  all_goals try (split at h)
  all_goals try simp only [Option.some.injEq] at h
  all_goals subst l
  all_goals simp only [projectCommand, hp, Algorithm2.next, Option.some.injEq]
  all_goals funext q; by_cases he : q = p
  all_goals simp_all [project, setLocal, Linked, dead]

theorem next_linked {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    (link : ∀ p, Linked (s p)) (h : next cfg s c = some t) : ∀ p, Linked (t p) := by
  cases c with
  | stutter =>
    have he : s = t := Option.some.inj h
    simpa [← he] using link
  | run p =>
    simp only [next] at h
    cases ho : ordinary cfg s p with
    | none => simp [ho] at h
    | some l =>
      simp only [ho, Option.map_some, Option.some.injEq] at h
      subst t
      intro q
      by_cases he : q = p
      · subst q; simpa using ordinary_linked (link p) ho
      · simpa [he] using link q
  | fail p | restart p =>
    simp only [next] at h
    split at h
    all_goals try contradiction
    all_goals try simp only [Option.some.injEq] at h; subst t; intro q
    all_goals by_cases he : q = p
    all_goals simp_all [setLocal, Linked, dead]

theorem next_projection {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    (link : ∀ p, Linked (s p)) (h : next cfg s c = some t) :
    Algorithm2.next cfg.tournament (project s) (projectCommand s c) = some (project t) := by
  cases c with
  | stutter => simpa [next, projectCommand, Algorithm2.next] using congrArg (Option.map project) h
  | run p =>
    simp only [next] at h
    cases ho : ordinary cfg s p with
    | none => simp [ho] at h
    | some l =>
      simp only [ho, Option.map_some, Option.some.injEq] at h
      subst t
      exact ordinary_projection (link p) ho
  | fail p =>
    simp only [next] at h
    split at h
    · contradiction
    · simp only [Option.some.injEq] at h; subst t
      have hd : (s p).tournamentPC ≠ .down := by
        have lp := link p
        cases hp : (s p).pc <;> simp_all [Linked, dead]
      simp [projectCommand, hd, Algorithm2.next, project, Algorithm2.setLocal, setLocal, dead]
  | restart p =>
    simp only [next] at h
    split at h
    · rename_i hd
      simp only [Option.some.injEq] at h; subst t
      have hl : (s p).tournamentPC = .down := by
        have lp := link p
        simp only [Linked, hd] at lp
        exact lp.1
      simp [projectCommand, Algorithm2.next, project, hl, Algorithm2.setLocal, setLocal, dead]
    · contradiction

theorem reachable_projection {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) :
    (∀ p, Linked (s p)) ∧ Algorithm2.Reachable cfg.tournament (project s) := by
  induction reach with
  | initial =>
    exact ⟨by intro p; simp [initial, Linked, dead], Algorithm2.Reachable.initial⟩
  | @step s t a _ edge ih =>
    obtain ⟨c, hc, _⟩ := edge
    exact ⟨next_linked ih.1 hc,
      Algorithm2.Reachable.step ih.2 ⟨projectCommand s c, next_projection ih.1 hc, rfl⟩⟩

/-- Includes the singleton's private admission ownership: the projection's
critical control, not its visible dead value, is what supplies exclusion. -/
theorem holding_unique {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) {p q : Proc n}
    (hp : Holding (s p).pc) (hq : Holding (s q).pc) : p = q := by
  have inv := reachable_projection reach
  apply Algorithm2.safety n cfg.tournament (project s) inv.2 p q
  · have lp := inv.1 p
    cases h : (s p).pc <;> simp_all [Holding, Linked, project]
  · have lq := inv.1 q
    cases h : (s q).pc <;> simp_all [Holding, Linked, project]

end EconomicalSolutions.Algorithm5

#print axioms EconomicalSolutions.Algorithm5.reachable_projection
#print axioms EconomicalSolutions.Algorithm5.holding_unique
