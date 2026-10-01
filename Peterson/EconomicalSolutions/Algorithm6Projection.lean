import Peterson.EconomicalSolutions.Algorithm6

set_option linter.unusedSimpArgs false

namespace EconomicalSolutions.Algorithm6

/-- A structural connection between the two private interpreters. No priority
bound, unique owner or queue order occurs in this predicate. -/
def Linked {n : Nat} (l : Local n) : Prop :=
  match l.pc with
  | .acquire => l.tournamentPC ≠ .down
  | .down => l.tournamentPC = .down ∧ l.value.tournament = Algorithm2.dead
  | .idle | .request | .maintain _ | .lowerTick _ | .test | .publish | .enter | .cs | .release =>
      l.tournamentPC = .idle ∧ l.value.tournament = Algorithm2.dead
  | .enqueue _ => l.tournamentPC = .release
  | .upperJoin _ | .upperTick _ _ | .build _ | .off | .lowerJoin _ | .complete _ =>
      l.tournamentPC = .cs

def Holding {n : Nat} (pc : PC n) : Prop :=
  match pc with
  | .upperJoin _ | .upperTick _ _ | .build _ | .off | .lowerJoin _ | .complete _ | .enqueue _ => True
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
    split <;> simp_all [Linked, dead, reset]

theorem ordinary_linked {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {l : Local n} (link : Linked (s p)) (h : ordinary cfg s p = some l) : Linked l := by
  cases hp : (s p).pc
  case' build rest => cases rest
  case' maintain rest => cases rest
  case' lowerJoin cp => cases cp
  all_goals simp only [ordinary, hp] at h
  all_goals try exact tournamentInstruction_linked h
  all_goals try contradiction
  all_goals try (rw [Option.map_eq_some_iff] at h; obtain ⟨c, hc, h⟩ := h)
  all_goals repeat (split at h)
  all_goals try simp only [Option.some.injEq] at h
  all_goals subst l; simp_all [Linked, dead, reset]

def projectCommand {n : Nat} (s : State n) : Command n → Algorithm2.Command n
  | .run p => match (s p).pc with
      | .request | .acquire | .complete _ | .enqueue _ => .run p
      | _ => .stutter
  | .fail p => if (s p).tournamentPC = .down then .stutter else .fail p
  | .restart p => .restart p
  | .stutter => .stutter

theorem ordinary_projection {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {l : Local n} (link : Linked (s p)) (h : ordinary cfg s p = some l) :
    Algorithm2.next cfg.tournament (project s) (projectCommand s (.run p)) =
      some (project (setLocal s p l)) := by
  cases hp : (s p).pc
  case' build rest => cases rest
  case' maintain rest => cases rest
  case' lowerJoin cp => cases cp
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
  case complete b =>
    simp only [Option.some.injEq] at h; subst l
    have hl : (s p).tournamentPC = .cs := by simpa [Linked, hp] using link
    simp [projectCommand, hp, Algorithm2.next, Algorithm2.ordinary, project, hl,
      Algorithm2.setLocal, setLocal]
  case enqueue b =>
    simp only [Option.some.injEq] at h; subst l
    have hl : (s p).tournamentPC = .release := by simpa [Linked, hp] using link
    simp [projectCommand, hp, Algorithm2.next, Algorithm2.ordinary, project, hl,
      Algorithm2.setLocal, setLocal]
  all_goals try (rw [Option.map_eq_some_iff] at h; obtain ⟨c, hc, h⟩ := h)
  all_goals repeat (split at h)
  all_goals try simp only [Option.some.injEq] at h
  all_goals subst l
  all_goals simp only [projectCommand, hp, Algorithm2.next, Option.some.injEq]
  all_goals funext q; by_cases he : q = p
  all_goals simp_all [project, setLocal, Linked, dead, reset]

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
    all_goals simp_all [setLocal, Linked, dead, reset]

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
        cases hp : (s p).pc <;> simp_all [Linked, dead, reset]
      simp [projectCommand, hd, Algorithm2.next, project, Algorithm2.setLocal, setLocal, dead, reset]
  | restart p =>
    simp only [next] at h
    split at h
    · rename_i hd
      simp only [Option.some.injEq] at h; subst t
      have hl : (s p).tournamentPC = .down := by
        have lp := link p
        simp only [Linked, hd] at lp
        exact lp.1
      simp [projectCommand, Algorithm2.next, project, hl, Algorithm2.setLocal, setLocal, dead, reset]
    · contradiction

theorem reachable_projection {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) :
    (∀ p, Linked (s p)) ∧ Algorithm2.Reachable cfg.tournament (project s) := by
  induction reach with
  | initial =>
    exact ⟨by intro p; simp [initial, Linked, dead, reset], Algorithm2.Reachable.initial⟩
  | @step s t a _ edge ih =>
    obtain ⟨c, hc, _⟩ := edge
    exact ⟨next_linked ih.1 hc,
      Algorithm2.Reachable.step ih.2 ⟨projectCommand s c, next_projection ih.1 hc, rfl⟩⟩

/-- Admission includes the delayed local release, still retaining root ownership. -/
theorem holding_unique {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) {p q : Proc n}
    (hp : Holding (s p).pc) (hq : Holding (s q).pc) : p = q := by
  have inv := reachable_projection reach
  obtain ⟨finish, trace, commands, initially, valid, last⟩ :=
    Algorithm2.reachable_has_prefix inv.2
  have unique := Algorithm2.concrete_treeUnique initially valid (Algorithm2.height n)
    (le_refl _) finish (le_refl _)
  rw [last] at unique
  have passed (r : Proc n) (held : Holding (s r).pc) :
      Algorithm2.passedLevel (project s r) = Algorithm2.height n := by
    have link := inv.1 r
    cases h : (s r).pc <;> simp_all [Holding, Linked, project, Algorithm2.passedLevel]
  apply unique p q _ (by rw [passed p hp]) (by rw [passed q hq])
  have ps : p.val < 2 ^ Algorithm2.height n := Nat.lt_of_lt_of_le p.isLt (Algorithm2.real_fits_padding n)
  have qs : q.val < 2 ^ Algorithm2.height n := Nat.lt_of_lt_of_le q.isLt (Algorithm2.real_fits_padding n)
  simp [Nat.div_eq_of_lt ps, Nat.div_eq_of_lt qs]

end EconomicalSolutions.Algorithm6

#print axioms EconomicalSolutions.Algorithm6.reachable_projection
#print axioms EconomicalSolutions.Algorithm6.holding_unique
