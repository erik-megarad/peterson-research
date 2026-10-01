import Peterson.EconomicalSolutions.Algorithm6Doorway

/-! Outer service intermediates. The full original-request progress theorem
still needs the historical predecessor-elimination argument. None of the
conditional reductions below is assumed as an execution-admissibility premise. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm6

/-- Frozen outer completion-or-failure premise. Local tournament completion
is a separate, already derived result. -/
def CriticalCompletion {n : Nat} {cfg : Config n} (r : Run cfg) : Prop :=
  ∀ t p, (r.state t p).pc = .cs →
    ∃ u, t ≤ u ∧ (r.event u = .complete p ∨ r.event u = .fail p)

def Pending {n : Nat} (pc : PC n) : Prop := Doorway pc ∨ Queued pc

def Outcome {n : Nat} {cfg : Config n} (r : Run cfg) (p : Proc n) (t : Nat) : Prop :=
  r.event t = .entry p ∨ r.event t = .fail p

/-- Only deletions occur after enqueue, including delayed publish/entry work. -/
theorem queued_ordinary_subset {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {out : Local n} (queued : Queued (s p).pc)
    (step : ordinary cfg s p = some out) : out.behind ⊆ (s p).behind := by
  cases hp : (s p).pc <;> simp only [hp, Queued] at queued
  case maintain rest =>
    cases rest <;> simp only [ordinary, hp, Option.some.injEq] at step <;> subst out
    · exact Finset.Subset.refl _
    · dsimp only; split
      · exact Finset.Subset.refl _
      · exact Finset.erase_subset _ _
  case lowerTick cp =>
    simp only [ordinary, hp] at step
    obtain ⟨c, _, rfl⟩ := Option.map_eq_some_iff.mp step
    exact Finset.Subset.refl _
  case test | publish | enter =>
    simp only [ordinary, hp, Option.some.injEq] at step
    subst out; exact Finset.Subset.refl _

theorem next_queued_subset {n : Nat} {cfg : Config n} {s t : State n}
    {p : Proc n} {command : Command n} (queued : Queued (s p).pc)
    (step : next cfg s command = some t) : (t p).behind ⊆ (s p).behind := by
  by_cases act : Acts command p
  · rcases act with rfl | rfl
    · obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp step
      simpa using queued_ordinary_subset queued ho
    · simp only [next] at step
      split at step
      · contradiction
      · have eq := Option.some.inj step; subst t; simp [reset]
  · have live : (s p).pc ≠ .down := by intro hp; simp [hp, Queued] at queued
    rw [next_live_unchanged step live act]

/-- Include the real test, publication and entry instructions after the finite
maintenance/clock invocation. A refused attempt decreases the same rank. -/
def serviceRank {n : Nat} (pc : PC n) : Nat :=
  match pc with
  | .maintain _ | .lowerTick _ => lowerRoundRank pc + 3
  | .test => 3
  | .publish => 2
  | .enter => 1
  | _ => 0

theorem empty_queued_ordinary_descent {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {out : Local n} (queued : Queued (s p).pc)
    (empty : (s p).behind = ∅) (step : ordinary cfg s p = some out) :
    serviceRank out.pc < serviceRank (s p).pc := by
  by_cases round : LowerRound (s p).pc
  · have result := lower_round_ordinary round step
    have old : serviceRank (s p).pc = lowerRoundRank (s p).pc + 3 := by
      cases hp : (s p).pc <;> simp_all [LowerRound, serviceRank]
    rw [old]
    rcases result.1 with nextRound | test
    · have new : serviceRank out.pc = lowerRoundRank out.pc + 3 := by
        cases hp : out.pc <;> simp_all [LowerRound, serviceRank]
      rw [new]; omega
    · simp only [test, serviceRank]
      have := result.2
      simp only [test, lowerRoundRank] at this
      omega
  · cases hp : (s p).pc <;> simp_all only [Queued, LowerRound]
    all_goals simp only [ordinary, hp, empty, ↓reduceIte, Option.some.injEq] at step
    all_goals subst out; simp [hp, serviceRank]

/-- A hypothetical unresolved original queued occurrence stays queued. -/
theorem unresolved_queued {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {start : Nat} (queued : Queued (r.state start p).pc)
    (none : ∀ t, start ≤ t → ¬ Outcome r p t) :
    ∀ t, start ≤ t → Queued (r.state t p).pc := by
  intro t lo
  induction t, lo using Nat.le_induction with
  | base => exact queued
  | succ t lo ih =>
    exact next_queued ih (r.valid t) (fun h => none t lo (Or.inl h))
      (fun h => none t lo (Or.inr h))

/-- Empty-list service ends at actual outer entry or own failure, even when
started in a stale, possibly unsuccessful lower attempt. -/
theorem empty_queued_eventually_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (queued : Queued (r.state start p).pc) (empty : (r.state start p).behind = ∅) :
    ∃ finish, start ≤ finish ∧ Outcome r p finish := by
  classical
  by_contra missing
  have none : ∀ t, start ≤ t → ¬ Outcome r p t := by
    simpa only [not_exists, not_and] using missing
  have stays := unresolved_queued r queued none
  have emptyAll : ∀ t, start ≤ t → (r.state t p).behind = ∅ := by
    intro t lo
    induction t, lo using Nat.le_induction with
    | base => exact empty
    | succ t lo ih =>
      exact Finset.subset_empty.mp (ih ▸ next_queued_subset (stays t lo) (r.valid t))
  apply fair_descent_impossible r fair p start (fun l => serviceRank l.pc)
  · intro t lo
    have h := stays t lo
    cases hp : (r.state t p).pc <;> simp_all [Queued, Protocol]
  · intro t lo act
    rcases act with run | fail
    · have step := r.valid t
      rw [run] at step
      obtain ⟨out, ho, eq⟩ := Option.map_eq_some_iff.mp step
      rw [← eq, setLocal_self]
      exact empty_queued_ordinary_descent (stays t lo) (emptyAll t lo) ho
    · exact (none t lo (Or.inr (by simp [Run.event, label, fail]))).elim

/-- The least outcome retains the queued controls through the endpoint prestate.
It therefore belongs to this request, including normal replacement exclusion. -/
theorem empty_queued_first_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (queued : Queued (r.state start p).pc) (empty : (r.state start p).behind = ∅) :
    ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
      Outcome r p finish ∧
      (∀ t, start ≤ t → t < finish → ¬ Outcome r p t) ∧
      (∀ t, start ≤ t → t ≤ finish → Queued (r.state t p).pc) := by
  classical
  have ex := empty_queued_eventually_outcome r fair queued empty
  have first := Nat.find_spec ex
  have none : ∀ t, start ≤ t → t < Nat.find ex → ¬ Outcome r p t := by
    intro t lo hi outcome
    have := Nat.find_min' ex ⟨lo, outcome⟩
    omega
  refine ⟨Nat.find ex, first.1, ?_, first.2, none, ?_⟩
  · intro t lo hi bad; exact none t lo hi (Or.inr bad)
  · intro t lo hi
    induction t, lo using Nat.le_induction with
    | base => exact queued
    | succ t lo ih =>
      exact next_queued (ih (by omega)) (r.valid t)
        (fun h => none t lo (by omega) (Or.inl h))
        (fun h => none t lo (by omega) (Or.inr h))

/-- Any indefinitely unresolved queued request stays in the lower clock;
delayed publication/entry cannot account for indefinite waiting. -/
theorem unresolved_queued_lower {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (queued : Queued (r.state start p).pc)
    (none : ∀ t, start ≤ t → ¬ Outcome r p t) :
    ∀ t, start ≤ t → IsLower (r.state t p).value.clock ∧ (r.state t p).behind ≠ ∅ := by
  intro t lo
  have stays := unresolved_queued r queued none t lo
  have nonempty : (r.state t p).behind ≠ ∅ := by
    intro empty
    obtain ⟨finish, hi, outcome⟩ := empty_queued_eventually_outcome r fair stays empty
    exact none finish (by omega) outcome
  refine ⟨?_, nonempty⟩
  have facts := (reachable_invariant (r.reachable t)).localFacts p
  cases hp : (r.state t p).pc <;> simp_all [Queued, LocalFacts]
  all_goals cases ht : (r.state t p).value.clock <;> simp_all [IsLower]

/-- Pending own inspection of one identifier in a partial maintenance scan. -/
def BeforeMaintenance {n : Nat} (q : Proc n) (pc : PC n) : Prop :=
  ∃ rest, pc = .maintain rest ∧ q ∈ rest

def maintenanceRank {n : Nat} : PC n → Nat
  | .maintain rest => rest.length
  | _ => 0

theorem next_before_maintenance {n : Nat} {cfg : Config n} {s t : State n}
    {p q : Proc n} {command : Command n} (before : BeforeMaintenance q (s p).pc)
    (step : next cfg s command = some t)
    (noRead : ¬ MaintenanceRead s command p q) (noFail : label s command ≠ .fail p) :
    BeforeMaintenance q (t p).pc ∧
      (Acts command p → maintenanceRank (t p).pc < maintenanceRank (s p).pc) := by
  by_cases act : Acts command p
  · rcases act with rfl | rfl
    · obtain ⟨rest, pc, mem⟩ := before
      cases rest with
      | nil => simp at mem
      | cons head rest =>
        have ne : head ≠ q := by
          intro eq; subst head; exact noRead ⟨rfl, rest, pc⟩
        have tail : q ∈ rest := (List.mem_cons.mp mem).resolve_left (Ne.symm ne)
        simp only [next, ordinary, pc, Option.map_some, Option.some.injEq] at step
        subst t
        constructor
        · exact ⟨rest, by simp, tail⟩
        · intro _; simp [pc, maintenanceRank]
    · exact (noFail rfl).elim
  · obtain ⟨rest, pc, mem⟩ := before
    have live : (s p).pc ≠ .down := by simp [pc]
    have eq := next_live_unchanged step live act
    refine ⟨?_, fun h => (act h).elim⟩
    simpa [eq] using (show BeforeMaintenance q (s p).pc from ⟨rest, pc, mem⟩)

/-- Fairness reaches the actual stage 6 register read, not a clock-position
sample or a later read in a replacement episode. -/
theorem maintenance_eventually_read {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p q : Proc n} {start : Nat}
    (before : BeforeMaintenance q (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧
      (MaintenanceRead (r.state finish) (r.command finish) p q ∨ r.event finish = .fail p) := by
  classical
  by_contra missing
  have none : ∀ t, start ≤ t →
      ¬ (MaintenanceRead (r.state t) (r.command t) p q ∨ r.event t = .fail p) := by
    simpa only [not_exists, not_and] using missing
  have stays : ∀ t, start ≤ t → BeforeMaintenance q (r.state t p).pc := by
    intro t lo
    induction t, lo using Nat.le_induction with
    | base => exact before
    | succ t lo ih =>
      exact (next_before_maintenance ih (r.valid t)
        (fun h => none t lo (Or.inl h)) (fun h => none t lo (Or.inr h))).1
  apply fair_descent_impossible r fair p start (fun l => maintenanceRank l.pc)
  · intro t lo
    obtain ⟨rest, pc, _⟩ := stays t lo
    simp [pc, Protocol]
  · intro t lo act
    exact (next_before_maintenance (stays t lo) (r.valid t)
      (fun h => none t lo (Or.inl h)) (fun h => none t lo (Or.inr h))).2 act

/-- An indefinitely unresolved request performs an actual maintenance read of
every distinct identifier arbitrarily late. Its stale initial cursor is allowed. -/
theorem unresolved_reads_later {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p q : Proc n} {start : Nat}
    (queued : Queued (r.state start p).pc)
    (none : ∀ t, start ≤ t → ¬ Outcome r p t) (other : q ≠ p)
    {t : Nat} (lo : start ≤ t) :
    ∃ read, t < read ∧ MaintenanceRead (r.state read) (r.command read) p q := by
  have lower := unresolved_queued_lower r fair queued none
  obtain ⟨begin, finish, tb, _, fresh, _, _, _⟩ := continuous_lower_rounds r fair
    (fun u hi => (lower u hi).1) t lo
  obtain ⟨read, hi, outcome⟩ := maintenance_eventually_read r fair
    (p := p) (q := q) (start := begin) ⟨cfg.order p, fresh, (cfg.complete p q).mpr other⟩
  rcases outcome with readEvent | fail
  · exact ⟨read, by omega, readEvent⟩
  · exact (none read (by omega) (Or.inr fail)).elim

theorem maintenance_removes_invisible {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {reader owner : Proc n}
    (read : MaintenanceRead s command reader owner)
    (invisible : visible (s owner).value.clock = false)
    (step : next cfg s command = some t) : owner ∉ (t reader).behind := by
  obtain ⟨rfl, rest, pc⟩ := read
  simp only [next, ordinary, pc, invisible, Bool.false_eq_true, ↓reduceIte,
    Option.map_some, Option.some.injEq] at step
  subst t
  simp

/-- Lists decrease along the same queued episode; no peer action can add an
identifier and the original owner has neither entered nor failed. -/
theorem unresolved_list_subset {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {start : Nat} (queued : Queued (r.state start p).pc)
    (none : ∀ t, start ≤ t → ¬ Outcome r p t)
    {a b : Nat} (lo : start ≤ a) (ab : a ≤ b) :
    (r.state b p).behind ⊆ (r.state a p).behind := by
  induction b, ab using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ b ab ih =>
    exact (next_queued_subset (unresolved_queued r queued none b (by omega))
      (r.valid b)).trans ih

/-- Permanent invisibility is eventually observed and its deletion persists.
This does not assume any minimum dead interval for a failed identifier. -/
theorem unresolved_eventually_removes_invisible {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p q : Proc n} {start bound : Nat}
    (queued : Queued (r.state start p).pc)
    (none : ∀ t, start ≤ t → ¬ Outcome r p t) (other : q ≠ p)
    (invisible : ∀ t, bound ≤ t → visible (r.state t q).value.clock = false) :
    ∃ removed, start ≤ removed ∧ ∀ t, removed ≤ t → q ∉ (r.state t p).behind := by
  obtain ⟨read, hi, event⟩ := unresolved_reads_later r fair queued none other
    (t := max start bound) (le_max_left _ _)
  have absent := maintenance_removes_invisible event
    (invisible read (by omega)) (r.valid read)
  refine ⟨read + 1, by omega, ?_⟩
  intro t lo mem
  exact absent (unresolved_list_subset r queued none (by omega) lo mem)

/-- A hypothetical infinite wait has a fixed, nonempty list after some point.
The fixed set is derived from finite deletion, not a fairness premise. -/
theorem unresolved_list_stabilizes {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (queued : Queued (r.state start p).pc)
    (none : ∀ t, start ≤ t → ¬ Outcome r p t) :
    ∃ stable, start ≤ stable ∧ (r.state stable p).behind.Nonempty ∧
      ∀ t, stable ≤ t → (r.state t p).behind = (r.state stable p).behind := by
  classical
  have ex : ∃ size, ∃ t, start ≤ t ∧ (r.state t p).behind.card = size :=
    ⟨(r.state start p).behind.card, start, le_rfl, rfl⟩
  obtain ⟨stable, lo, size⟩ := Nat.find_spec ex
  refine ⟨stable, lo, Finset.nonempty_iff_ne_empty.mpr
    (unresolved_queued_lower r fair queued none stable lo).2, ?_⟩
  intro t hi
  apply Finset.eq_of_subset_of_card_le (unresolved_list_subset r queued none lo hi)
  have min := Nat.find_min' ex ⟨t, by omega, rfl⟩
  omega

/-- Every distinct member of that fixed list is visible arbitrarily late.
Otherwise its real maintenance read would delete it. Reuse-sensitive ordering
must still show that these recurring blockers cannot sustain a cycle. -/
theorem unresolved_stable_blockers {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (queued : Queued (r.state start p).pc)
    (none : ∀ t, start ≤ t → ¬ Outcome r p t) :
    ∃ stable, start ≤ stable ∧ (r.state stable p).behind.Nonempty ∧
      (∀ t, stable ≤ t → (r.state t p).behind = (r.state stable p).behind) ∧
      ∀ q, q ∈ (r.state stable p).behind → q ≠ p →
        ∀ bound, ∃ t, bound ≤ t ∧ visible (r.state t q).value.clock = true := by
  classical
  obtain ⟨stable, lo, nonempty, fixed⟩ := unresolved_list_stabilizes r fair queued none
  refine ⟨stable, lo, nonempty, fixed, ?_⟩
  intro q mem other bound
  by_contra absent
  have invisible : ∀ t, bound ≤ t → visible (r.state t q).value.clock = false := by
    intro t hi
    have h : visible (r.state t q).value.clock ≠ true := by
      intro vis; exact absent ⟨t, hi, vis⟩
    exact Bool.eq_false_iff.mpr h
  obtain ⟨removed, _, gone⟩ := unresolved_eventually_removes_invisible r fair queued none other invisible
  have bad := gone (max stable removed) (le_max_right _ _)
  rw [fixed _ (le_max_left _ _)] at bad
  exact bad mem

/-- The completed doorway reduces an unresolved original pending occurrence to
its own queued episode. No eventual entry is inferred from enqueue alone. -/
theorem unresolved_pending_queued {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (pending : Pending (r.state start p).pc)
    (none : ∀ t, start ≤ t → ¬ Outcome r p t) :
    ∃ queuedAt, start ≤ queuedAt ∧ Queued (r.state queuedAt p).pc := by
  rcases pending with doorway | queued
  · obtain ⟨finish, lo, _, outcome, _, _⟩ := doorway_first_outcome r fair doorway
    rcases outcome with enqueued | failed
    · exact ⟨finish + 1, by omega, enqueue_queued (r.valid finish) enqueued⟩
    · exact (none finish lo (Or.inr failed)).elim
  · exact ⟨start, le_rfl, queued⟩

/-- Every hypothetical unresolved original request reduces to continuous lower
waiting with a fixed nonempty list of recurring blockers. This is a necessary
condition for nontermination, not the still-open exclusion of that condition. -/
theorem unresolved_pending_reduction {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (pending : Pending (r.state start p).pc)
    (none : ∀ t, start ≤ t → ¬ Outcome r p t) :
    ∃ stable, start ≤ stable ∧ SameEpisodeUntil r p start stable ∧
      (r.state stable p).behind.Nonempty ∧
      (∀ t, stable ≤ t → IsLower (r.state t p).value.clock ∧
        (r.state t p).behind = (r.state stable p).behind) ∧
      ∀ q, q ∈ (r.state stable p).behind → q ≠ p →
        ∀ bound, ∃ t, bound ≤ t ∧ visible (r.state t q).value.clock = true := by
  obtain ⟨queuedAt, lo, queued⟩ := unresolved_pending_queued r fair pending none
  have laterNone : ∀ t, queuedAt ≤ t → ¬ Outcome r p t := by
    intro t hi; exact none t (by omega)
  obtain ⟨stable, hi, nonempty, fixed, blockers⟩ :=
    unresolved_stable_blockers r fair queued laterNone
  refine ⟨stable, by omega, ?_, nonempty, ?_, blockers⟩
  · intro t lo _ fail; exact none t lo (Or.inr fail)
  · intro t bound
    exact ⟨(unresolved_queued_lower r fair queued laterNone t (by omega)).1, fixed t bound⟩

/-- Reusing a persistent blocker cannot hide a complete fresh upper episode:
three writes would force its deletion before its next list construction. -/
theorem unresolved_member_excludes_upper_passage {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {reader owner : Proc n} {start a b : Nat}
    {joinBit writeBit : Bool} (queued : Queued (r.state start reader).pc)
    (none : ∀ t, start ≤ t → ¬ Outcome r reader t) (lo : start ≤ a) (ab : a < b)
    (other : owner ≠ reader)
    (publication : (r.state a owner).pc = .upperJoin (.joinWrite joinBit))
    (publishCommand : r.command a = .run owner)
    (third : (r.state b owner).pc = .upperTick 2 (.tickWrite writeBit))
    (thirdCommand : r.command b = .run owner)
    (upperEpisode : ∀ t, a < t → t ≤ b → ∃ bit, (r.state t owner).value.clock = .upper bit) :
    ∀ t, b ≤ t → owner ∉ (r.state t reader).behind := by
  have lower : ∀ t, a ≤ t → t ≤ b → ∃ bit, (r.state t reader).value.clock = .lower bit := by
    intro t hi _
    have h := (unresolved_queued_lower r fair queued none t (by omega)).1
    cases tag : (r.state t reader).value.clock <;> simp_all [IsLower]
  have removed := (three_tick_observation_removal
    (show ValidPrefix cfg r.state r.command (b + 1) from ⟨r.initialized, fun t _ => r.valid t⟩)
    ab (by omega) other publication publishCommand third thirdCommand upperEpisode lower).2
  intro t hi mem
  exact removed (unresolved_list_subset r queued none (by omega) hi mem)

/-- Completion and failure labels refer to real outer controls and commands. -/
theorem completion_event_acts {n : Nat} {s : State n} {c : Command n} {p : Proc n}
    (event : label s c = .complete p ∨ label s c = .fail p) :
    (c = .run p ∧ (s p).pc = .cs) ∨ c = .fail p := by
  cases c with
  | run q =>
    cases hp : (s q).pc
    case' upperJoin cp => cases cp
    case' upperTick count cp => cases cp
    case' lowerTick cp => cases cp
    all_goals simp only [label, hp, reduceCtorEq, or_false] at event
    all_goals cases event; exact Or.inl ⟨rfl, hp⟩
  | fail q =>
    simp only [label, reduceCtorEq, false_or, Label.fail.injEq] at event
    subst q; exact Or.inr rfl
  | restart | stutter => simp [label] at event

/-- Critical completion alone leaves a delayed release. Protocol scheduling
also pays that release, so actual outer occupancy eventually becomes invisible. -/
theorem critical_eventually_invisible {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    {p : Proc n} {start : Nat} (critical : (r.state start p).pc = .cs) :
    ∃ finish, start < finish ∧ visible (r.state finish p).value.clock = false := by
  obtain ⟨u, lo, event⟩ := completion start p critical
  rcases completion_event_acts event with ⟨run, pc⟩ | fail
  · have step := r.valid u
    simp only [run, next, ordinary, pc, Option.map_some, Option.some.injEq] at step
    have release : (r.state (u + 1) p).pc = .release := by rw [← step]; simp
    obtain ⟨v, hi, act, same⟩ := first_scheduled_action r fair
      (p := p) (start := u + 1) (by simp [release, Protocol])
    have pcv : (r.state v p).pc = .release := by rw [same]; exact release
    have last := r.valid v
    refine ⟨v + 1, by omega, ?_⟩
    rcases act with run | fail
    · simp only [run, next, ordinary, pcv, Option.map_some, Option.some.injEq] at last
      rw [← last]; simp [dead, visible]
    · simp only [fail, next, pcv, reduceCtorEq, ↓reduceIte, Option.some.injEq] at last
      rw [← last]; simp [reset, dead, visible]
  · have step := r.valid u
    simp only [fail, next] at step
    split at step
    · contradiction
    · have eq := Option.some.inj step
      refine ⟨u + 1, by omega, ?_⟩
      rw [← eq]; simp [reset, dead, visible]

/-- Surviving empty-list service reaches actual entry in the original episode. -/
theorem empty_queued_surviving_enters {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (queued : Queued (r.state start p).pc) (empty : (r.state start p).behind = ∅)
    (survives : ∀ t, start ≤ t → r.event t ≠ .fail p) :
    ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
      r.event finish = .entry p ∧
      (∀ t, start ≤ t → t < finish → ¬ Outcome r p t) ∧
      (∀ t, start ≤ t → t ≤ finish → Queued (r.state t p).pc) := by
  obtain ⟨finish, lo, episode, outcome, first, states⟩ :=
    empty_queued_first_outcome r fair queued empty
  exact ⟨finish, lo, episode, outcome.resolve_right (survives finish lo), first, states⟩

end EconomicalSolutions.Algorithm6

#print axioms EconomicalSolutions.Algorithm6.next_queued_subset
#print axioms EconomicalSolutions.Algorithm6.empty_queued_first_outcome
#print axioms EconomicalSolutions.Algorithm6.empty_queued_surviving_enters
#print axioms EconomicalSolutions.Algorithm6.unresolved_queued_lower
#print axioms EconomicalSolutions.Algorithm6.maintenance_eventually_read
#print axioms EconomicalSolutions.Algorithm6.unresolved_reads_later
#print axioms EconomicalSolutions.Algorithm6.unresolved_eventually_removes_invisible
#print axioms EconomicalSolutions.Algorithm6.unresolved_pending_reduction
#print axioms EconomicalSolutions.Algorithm6.unresolved_member_excludes_upper_passage
#print axioms EconomicalSolutions.Algorithm6.critical_eventually_invisible
