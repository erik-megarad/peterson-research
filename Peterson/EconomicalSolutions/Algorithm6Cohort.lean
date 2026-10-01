import Peterson.EconomicalSolutions.Algorithm6Joining
import Peterson.EconomicalSolutions.Algorithm6Observation

/-! Concrete occupied-cohort reduction during retained Algorithm 6 admission.
No successful ticking, completion, or eventual peer stability is assumed. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm6

def IsUpper : Tag → Prop
  | .upper _ => True
  | _ => False

def IsLower : Tag → Prop
  | .lower _ => True
  | _ => False

def UpperOwnerFacts {n : Nat} (l : Local n) : Prop := IsUpper l.value.clock → Holding l.pc

theorem ordinary_upper_owner {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {out : Local n} (facts : UpperOwnerFacts (s p)) (step : ordinary cfg s p = some out) :
    UpperOwnerFacts out := by
  cases hp : (s p).pc
  case' build rest => cases rest
  case' maintain rest => cases rest
  case' lowerJoin cp => cases cp
  all_goals simp only [ordinary, hp] at step
  all_goals try contradiction
  case request | acquire =>
    obtain ⟨tag, _, pc⟩ := tournamentInstruction_fields step
    have absent : ¬ IsUpper (s p).value.clock := by
      intro upper
      have := facts upper
      simp [hp, Holding] at this
    intro upper
    exact (absent (by simpa [tag] using upper)).elim
  case upperJoin cp | upperTick count cp =>
    obtain ⟨c, _, eq⟩ := Option.map_eq_some_iff.mp step
    subst out
    dsimp [UpperOwnerFacts]
    split_ifs <;> simp [Holding]
  all_goals try (obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step; subst out)
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try (cases hq : c.q)
  all_goals simp_all [UpperOwnerFacts, Holding, clockTag, IsUpper, dead]

theorem reachable_upper_owner {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) : ∀ p, UpperOwnerFacts (s p) := by
  induction reach with
  | initial => intro p; simp [UpperOwnerFacts, initial, reset, dead, IsUpper]
  | @step s t a _ edge ih =>
    obtain ⟨command, step, _⟩ := edge
    cases command with
    | stutter => have eq : s = t := Option.some.inj step; simpa [← eq] using ih
    | run p =>
      obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp step
      intro q
      by_cases eq : q = p
      · subst q; simpa using ordinary_upper_owner (ih p) ho
      · simpa [eq] using ih q
    | fail p | restart p =>
      simp only [next] at step
      split at step <;> try contradiction
      all_goals simp only [Option.some.injEq] at step; subst t; intro q
      all_goals by_cases eq : q = p
      all_goals first
        | (subst q; simp [UpperOwnerFacts, reset, dead, IsUpper])
        | simpa [eq] using ih q

/-- New lower occupancy requires actual queue publication, unless the same
physical process was already lower before this instruction. -/
theorem ordinary_lower_origin {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {out : Local n} (facts : LocalFacts (s p)) (step : ordinary cfg s p = some out)
    (lower : IsLower out.value.clock) :
    IsLower (s p).value.clock ∨ ∃ b, (s p).pc = .enqueue b := by
  cases hp : (s p).pc
  case' build rest => cases rest
  case' maintain rest => cases rest
  case' lowerJoin cp => cases cp
  all_goals simp only [ordinary, hp] at step
  all_goals try contradiction
  case request | acquire =>
    obtain ⟨tag, _, _⟩ := tournamentInstruction_fields step
    exact Or.inl (by simpa [tag] using lower)
  case enqueue b => exact Or.inr ⟨b, rfl⟩
  case lowerTick cp =>
    obtain ⟨b, tag⟩ : ∃ b, (s p).value.clock = .lower b := by simpa [LocalFacts, hp] using facts
    exact Or.inl (by simp [tag, IsLower])
  all_goals try (obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step; subst out)
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals dsimp at lower
  all_goals first
    | exact Or.inl lower
    | (cases hq : c.q <;> simp [hq, clockTag, IsLower] at lower)
    | simp [dead, IsLower] at lower

/-- Holding admission excludes every peer's occupied upper position. -/
theorem held_peer_not_upper {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) {owner peer : Proc n} (held : Holding (s owner).pc)
    (other : peer ≠ owner) : ¬ IsUpper (s peer).value.clock := by
  intro upper
  exact other (holding_unique reach (reachable_upper_owner reach peer upper) held)

/-- During retained admission, failures and departures can remove lower peers,
but neither restarts nor stale instructions can introduce new lower occupancy. -/
theorem held_lower_no_arrival {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {owner peer : Proc n} (reach : Reachable cfg s)
    (held : Holding (s owner).pc) (other : peer ≠ owner)
    (step : next cfg s command = some t) (lower : IsLower (t peer).value.clock) :
    IsLower (s peer).value.clock := by
  cases command with
  | stutter => have eq : s = t := Option.some.inj step; simpa [← eq] using lower
  | run p =>
    obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : peer = p
    · subst p
      rcases ordinary_lower_origin ((reachable_invariant reach).localFacts peer) ho (by simpa using lower) with old | ⟨b, enqueue⟩
      · exact old
      · exact (other (holding_unique reach (by simp [enqueue, Holding]) held)).elim
    · simpa [eq] using lower
  | fail p | restart p =>
    simp only [next] at step
    split at step <;> try contradiction
    all_goals simp only [Option.some.injEq] at step; subst t
    all_goals by_cases eq : peer = p
    all_goals first
      | (subst p; simp [reset, dead, IsLower] at lower)
      | simpa [eq] using lower

/-- Once a peer leaves lower, it cannot return while this admission is held. -/
theorem held_lower_past {n : Nat} {cfg : Config n} (r : Run cfg) {owner peer : Proc n}
    {start finish : Nat} (order : start ≤ finish) (other : peer ≠ owner)
    (held : ∀ t, start ≤ t → t < finish → Holding (r.state t owner).pc)
    (lower : IsLower (r.state finish peer).value.clock) :
    IsLower (r.state start peer).value.clock := by
  induction finish, order using Nat.le_induction with
  | base => exact lower
  | succ finish order ih =>
    apply ih (by intro t lo hi; exact held t lo (by omega))
    exact held_lower_no_arrival (r.reachable finish) (held finish order (by omega)) other
      (r.valid finish) lower

/-- Finitely many peers each lose lower occupancy at most once. No fairness or
restriction on failures of already absent processes is needed. -/
theorem held_cohort_stabilizes {n : Nat} {cfg : Config n} (r : Run cfg)
    (owner : Proc n) (start : Nat)
    (held : ∀ t, start ≤ t → Holding (r.state t owner).pc) :
    ∃ finish, start ≤ finish ∧ ∀ t, finish ≤ t → ∀ peer, peer ≠ owner →
      (IsLower (r.state t peer).value.clock ↔ IsLower (r.state finish peer).value.clock) ∧
      ¬ IsUpper (r.state t peer).value.clock := by
  classical
  have each : ∀ peer : Proc n, ∃ time, start ≤ time ∧ ∀ t, time ≤ t → peer ≠ owner →
      (IsLower (r.state t peer).value.clock ↔ IsLower (r.state time peer).value.clock) := by
    intro peer
    by_cases departed : ∃ time, start ≤ time ∧ ¬ IsLower (r.state time peer).value.clock
    · obtain ⟨time, lo, absent⟩ := departed
      refine ⟨time, lo, ?_⟩
      intro t hi other
      have laterAbsent : ¬ IsLower (r.state t peer).value.clock := by
        intro lower
        exact absent (held_lower_past r hi other (by intro u ulo _; exact held u (by omega)) lower)
      simp [absent, laterAbsent]
    · refine ⟨start, le_rfl, ?_⟩
      intro t lo _
      have all : ∀ u, start ≤ u → IsLower (r.state u peer).value.clock := by
        intro u ulo
        by_contra absent
        exact departed ⟨u, ulo, absent⟩
      exact ⟨fun _ => all start le_rfl, fun _ => all t lo⟩
  choose times lo stable using each
  let finish := (List.finRange n).foldl (fun a peer => max a (times peer)) start
  have bound : ∀ (xs : List (Proc n)) a, a ≤ xs.foldl (fun a p => max a (times p)) a ∧
      ∀ p ∈ xs, times p ≤ xs.foldl (fun a p => max a (times p)) a := by
    intro xs
    induction xs with
    | nil => intro a; simp
    | cons p xs ih =>
      intro a
      obtain ⟨le, all⟩ := ih (max a (times p))
      constructor
      · exact (Nat.le_max_left _ _).trans le
      · intro q mem
        rcases List.mem_cons.mp mem with rfl | mem
        · exact (Nat.le_max_right _ _).trans le
        · exact all q mem
  have b := bound (List.finRange n) start
  refine ⟨finish, b.1, ?_⟩
  intro t ht peer other
  have hp : times peer ≤ finish := b.2 peer (by simp)
  exact ⟨(stable peer t (by omega) other).trans (stable peer finish hp other).symm,
    held_peer_not_upper (r.reachable t) (held t (by omega)) other⟩

end EconomicalSolutions.Algorithm6

#print axioms EconomicalSolutions.Algorithm6.reachable_upper_owner
#print axioms EconomicalSolutions.Algorithm6.held_lower_no_arrival
#print axioms EconomicalSolutions.Algorithm6.held_cohort_stabilizes
