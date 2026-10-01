import Peterson.EconomicalSolutions.Algorithm6Progress

/-! Historical admissions and episode-sensitive predecessor elimination.
All history witnesses below are derived from the unchanged interpreter. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm6

def UpperPhase {n : Nat} : PC n → Prop
  | .upperTick _ _ => True
  | _ => False

def AfterThird {n : Nat} : PC n → Prop
  | .build _ | .off | .lowerJoin _ | .complete _ | .enqueue _ => True
  | _ => False

def UpperPublication {n : Nat} (s : State n) (c : Command n) (p : Proc n) : Prop :=
  c = .run p ∧ ∃ bit, (s p).pc = .upperJoin (.joinWrite bit)

def ThirdWrite {n : Nat} (s : State n) (c : Command n) (p : Proc n) : Prop :=
  c = .run p ∧ ∃ bit, (s p).pc = .upperTick 2 (.tickWrite bit)

private theorem ordinary_upper_origin {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {out : Local n} (reach : Reachable cfg s)
    (step : ordinary cfg s p = some out) (after : UpperPhase out.pc) :
    UpperPhase (s p).pc ∨ UpperPublication s (.run p) p := by
  cases hp : (s p).pc
  case upperTick count cp => exact Or.inl trivial
  case upperJoin cp =>
    right
    have joining : UpperJoining (s p).pc := by simp [hp, UpperJoining]
    by_contra absent
    have noJoin : label s (.run p) ≠ .upperJoin p := by
      cases cp <;> simp_all [UpperPublication, label]
    have nextJoin := (upper_join_ordinary (reachable_joinFacts reach p) joining step).2 noJoin
    cases hout : out.pc <;> simp_all [UpperPhase, UpperJoining]
  all_goals simp only [ordinary, hp] at step
  all_goals try contradiction
  case request | acquire =>
    rcases (tournamentInstruction_fields step).2.2 with h | ⟨cp, h⟩ <;>
      simp [h, UpperPhase] at after
  all_goals repeat (split at step)
  all_goals try (obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp step)
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try split_ifs at after
  all_goals simp_all [UpperPhase]

private theorem ordinary_third_origin {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {out : Local n}
    (step : ordinary cfg s p = some out) (after : AfterThird out.pc) :
    AfterThird (s p).pc ∨ ThirdWrite s (.run p) p := by
  cases hp : (s p).pc
  case build rest | off | lowerJoin cp | complete bit | enqueue bit => exact Or.inl trivial
  all_goals simp only [ordinary, hp] at step
  all_goals try contradiction
  case request | acquire =>
    rcases (tournamentInstruction_fields step).2.2 with h | ⟨cp, h⟩ <;>
      simp [h, AfterThird] at after
  case upperTick count cp =>
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp step
    cases cp <;> simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true, ite_false] at after
    all_goals try (solve | simp [AfterThird] at after)
    rename_i bit
    by_cases countEq : count = 2
    · exact Or.inr ⟨rfl, bit, hp.trans (by rw [countEq])⟩
    · have ne : count + 1 ≠ 3 := by omega
      simp [ne, AfterThird] at after
  all_goals repeat (split at step)
  all_goals try (obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp step)
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try split_ifs at after
  all_goals simp_all [AfterThird]

/-- Lift a local predecessor classification through interleaved commands.
Resets cannot enter either admitted phase. -/
private theorem next_phase_origin {n : Nat} {cfg : Config n} {s t : State n}
    {p : Proc n} {command : Command n} (phase : PC n → Prop)
    (boundary : State n → Command n → Proc n → Prop)
    (down : ¬ phase .down) (idle : ¬ phase .idle)
    (own : ∀ out, ordinary cfg s p = some out → phase out.pc →
      phase (s p).pc ∨ boundary s (.run p) p)
    (step : next cfg s command = some t) (after : phase (t p).pc) :
    phase (s p).pc ∨ boundary s command p := by
  cases command with
  | stutter => have eq : s = t := Option.some.inj step; exact Or.inl (eq ▸ after)
  | run q =>
    obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = q
    · subst q; exact own out ho (by simpa using after)
    · exact Or.inl (by simpa [eq] using after)
  | fail q | restart q =>
    simp only [next] at step
    split at step <;> try contradiction
    all_goals have eq := Option.some.inj step
    all_goals subst t
    all_goals by_cases pq : p = q
    all_goals first
      | (subst q; simp only [setLocal_self, reset, ite_true, ite_false] at after
         exact (down after).elim)
      | (subst q; simp only [setLocal_self, reset, ite_true, ite_false] at after
         exact (idle after).elim)
      | exact Or.inl (by simpa [pq] using after)

/-- Reconstruct the last entrance into a phase and every intervening state.
This is finite history, with no scheduling or survival premise. -/
private theorem phase_history (phase : Nat → Prop) (boundary : Nat → Prop)
    (initial : ¬ phase 0)
    (previous : ∀ t, phase (t + 1) → phase t ∨ boundary t)
    {finish : Nat} (atFinish : phase finish) :
    ∃ start, start < finish ∧ boundary start ∧
      ∀ t, start < t → t ≤ finish → phase t := by
  induction finish with
  | zero => exact (initial atFinish).elim
  | succ finish ih =>
    rcases previous finish atFinish with old | entrance
    · obtain ⟨start, lt, event, states⟩ := ih old
      refine ⟨start, by omega, event, ?_⟩
      intro t lo hi
      by_cases eq : t = finish + 1
      · simpa [eq] using atFinish
      · exact states t lo (by omega)
    · refine ⟨finish, by omega, entrance, ?_⟩
      intro t lo hi
      have eq : t = finish + 1 := by omega
      simpa [eq] using atFinish

/-- Every in-flight upper phase comes from this occurrence's real publication. -/
theorem upper_phase_history {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {finish : Nat} (upper : UpperPhase (r.state finish p).pc) :
    ∃ start, start < finish ∧ UpperPublication (r.state start) (r.command start) p ∧
      ∀ t, start < t → t ≤ finish → UpperPhase (r.state t p).pc := by
  apply phase_history (fun t => UpperPhase (r.state t p).pc)
    (fun t => UpperPublication (r.state t) (r.command t) p) _ _ upper
  · simp [r.initialized, initial, reset, UpperPhase]
  · intro t after
    exact next_phase_origin UpperPhase UpperPublication (by simp [UpperPhase])
      (by simp [UpperPhase]) (fun out step h => ordinary_upper_origin (r.reachable t) step h)
      (r.valid t) after

/-- Enqueue's finite suffix traces back to the actual third upper write. -/
theorem after_third_history {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {finish : Nat} (after : AfterThird (r.state finish p).pc) :
    ∃ start, start < finish ∧ ThirdWrite (r.state start) (r.command start) p ∧
      ∀ t, start < t → t ≤ finish → AfterThird (r.state t p).pc := by
  apply phase_history (fun t => AfterThird (r.state t p).pc)
    (fun t => ThirdWrite (r.state t) (r.command t) p) _ _ after
  · simp [r.initialized, initial, reset, AfterThird]
  · intro t later
    exact next_phase_origin AfterThird ThirdWrite (by simp [AfterThird])
      (by simp [AfterThird]) (fun out step h => ordinary_third_origin step h)
      (r.valid t) later

/-- The real admission behind every enqueue: publication, third write, and
unbroken tournament ownership through the enqueue prestate. Fail/restart and
normal replacement cannot occur within this interval. -/
theorem enqueue_admission_history {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {finish : Nat} (arrival : r.event finish = .enqueue p) :
    ∃ publication third, publication < third ∧ third < finish ∧
      UpperPublication (r.state publication) (r.command publication) p ∧
      ThirdWrite (r.state third) (r.command third) p ∧
      (∀ t, publication < t → t ≤ third → ∃ bit, (r.state t p).value.clock = .upper bit) ∧
      (∀ t, publication ≤ t → t ≤ finish → Holding (r.state t p).pc) := by
  obtain ⟨_, bit, pc⟩ := enqueue_event_iff.mp arrival
  obtain ⟨third, tf, write, suffix⟩ := after_third_history r (p := p)
    (finish := finish) (by simp [pc, AfterThird])
  obtain ⟨command, writeBit, thirdPC⟩ := write
  obtain ⟨publication, pt, published, upper⟩ := upper_phase_history r (p := p)
    (finish := third) (by simp [thirdPC, UpperPhase])
  refine ⟨publication, third, pt, tf, published, ⟨command, writeBit, thirdPC⟩, ?_, ?_⟩
  · intro t lo hi
    have phase := upper t lo hi
    cases hp : (r.state t p).pc <;> simp only [hp, UpperPhase] at phase
    exact reachable_upper_tick_occupied (r.reachable t) hp
  · intro t lo hi
    by_cases eq : t = publication
    · obtain ⟨_, b, hp⟩ := published
      simp [eq, hp, Holding]
    · by_cases before : t ≤ third
      · have phase := upper t (by omega) before
        cases hp : (r.state t p).pc <;> simp_all [UpperPhase, Holding]
      · have phase := suffix t (by omega) hi
        cases hp : (r.state t p).pc <;> simp_all [AfterThird, Holding]

/-- A later enqueue's upper publication is strictly after an earlier distinct
enqueue. In-flight earlier admissions are excluded by concrete tournament
exclusion, not by assuming an admission ordering. -/
theorem later_enqueue_admission {n : Nat} {cfg : Config n} (r : Run cfg)
    {p q : Proc n} {a b : Nat} (other : q ≠ p) (ab : a < b)
    (first : r.event a = .enqueue p) (second : r.event b = .enqueue q) :
    ∃ publication third, a < publication ∧ publication < third ∧ third < b ∧
      UpperPublication (r.state publication) (r.command publication) q ∧
      ThirdWrite (r.state third) (r.command third) q ∧
      (∀ t, publication < t → t ≤ third → ∃ bit, (r.state t q).value.clock = .upper bit) := by
  obtain ⟨publication, third, pt, tb, publish, write, upper, held⟩ := enqueue_admission_history r second
  have later : a < publication := by
    by_contra bad
    obtain ⟨_, bit, pc⟩ := enqueue_event_iff.mp first
    exact other (holding_unique (r.reachable a) (held a (by omega) (by omega))
      (by simp [pc, Holding]))
  exact ⟨publication, third, later, pt, tb, publish, write, upper⟩

/-- No later admission can still be a blocker of this indefinitely unresolved
queued episode. This remains true for arbitrarily fast failure/restart and
identifier reuse, and does not require observing an off interval. -/
theorem unresolved_later_enqueue_absent {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p q : Proc n} {a b : Nat}
    (other : q ≠ p) (ab : a < b) (first : r.event a = .enqueue p)
    (none : ∀ t, a < t → ¬ Outcome r p t) (second : r.event b = .enqueue q) :
    ∀ t, b ≤ t → q ∉ (r.state t p).behind := by
  obtain ⟨publication, third, ap, pt, tb, ⟨pubCommand, pubBit, pubPC⟩,
    ⟨thirdCommand, thirdBit, thirdPC⟩, upper⟩ := later_enqueue_admission r other ab first second
  have queued := enqueue_queued (r.valid a) first
  have removed := unresolved_member_excludes_upper_passage r fair queued
    (fun t lo => none t (by omega)) (by omega : a + 1 ≤ publication) pt other
    pubPC pubCommand thirdPC thirdCommand upper
  intro t lo
  exact removed t (by omega)

/-- The build cursor and list exclude the physical owner. This is a reachable
fact about real scans, not an assumed property of a predecessor graph. -/
def SelfFree {n : Nat} (p : Proc n) (l : Local n) : Prop :=
  p ∉ l.behind ∧ ∀ rest, l.pc = .build rest → p ∉ rest

private theorem ordinary_selfFree {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {out : Local n} (before : SelfFree p (s p))
    (step : ordinary cfg s p = some out) : SelfFree p out := by
  obtain ⟨absent, cursor⟩ := before
  cases hp : (s p).pc
  case' build rest => cases rest
  case' maintain rest => cases rest
  case' lowerJoin cp => cases cp
  all_goals simp only [ordinary, hp] at step
  all_goals try contradiction
  case request | acquire =>
    obtain ⟨_, list, control⟩ := tournamentInstruction_fields step
    refine ⟨by simpa [list] using absent, ?_⟩
    rcases control with h | ⟨cp, h⟩ <;> simp [h]
  case build.cons q rest =>
    simp only [Option.some.injEq] at step; subst out
    have domain := cursor (q :: rest) hp
    simp only [List.mem_cons, not_or] at domain
    constructor
    · dsimp only; split <;> simp_all
    · intro remaining eq
      simp only [PC.build.injEq] at eq
      simpa [← eq] using domain.2
  all_goals try (obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp step)
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals simp only [SelfFree]
  all_goals repeat first | split | constructor
  all_goals simp_all
  all_goals exact fun mem => (cfg.complete p p).mp mem rfl

theorem reachable_selfFree {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) : ∀ p, SelfFree p (s p) := by
  induction reach with
  | initial => intro p; simp [SelfFree, initial, reset]
  | @step s t a reach edge ih =>
    obtain ⟨command, step, _⟩ := edge
    cases command with
    | stutter => have eq : s = t := Option.some.inj step; simpa [← eq] using ih
    | run p =>
      obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp step
      intro q
      by_cases eq : q = p
      · subst q; simpa using ordinary_selfFree (ih p) ho
      · simpa [eq] using ih q
    | fail p | restart p =>
      simp only [next] at step
      split at step <;> try contradiction
      all_goals have eq := Option.some.inj step
      all_goals subst t
      all_goals intro q
      all_goals by_cases eq : q = p
      all_goals first
        | (subst q; simp [SelfFree, reset])
        | simpa [eq] using ih q

def VisibleControl {n : Nat} (pc : PC n) : Prop := Queued pc ∨ pc = .cs ∨ pc = .release

private theorem visible_control_iff {n : Nat} {l : Local n} (facts : LocalFacts l) :
    visible l.value.clock = true ↔ VisibleControl l.pc := by
  cases hp : l.pc <;> cases tag : l.value.clock <;>
    simp_all [LocalFacts, visible, VisibleControl, Queued]

def EnqueueEvent {n : Nat} (s : State n) (c : Command n) (p : Proc n) : Prop :=
  label s c = .enqueue p

private theorem ordinary_visible_origin {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {out : Local n} (step : ordinary cfg s p = some out)
    (after : VisibleControl out.pc) :
    VisibleControl (s p).pc ∨ EnqueueEvent s (.run p) p := by
  cases hp : (s p).pc
  case maintain rest | lowerTick cp | test | publish | enter | cs | release =>
    exact Or.inl (by simp [VisibleControl, Queued])
  case enqueue bit => exact Or.inr (by simp [EnqueueEvent, label, hp])
  case' build rest => cases rest
  case' lowerJoin cp => cases cp
  all_goals simp only [ordinary, hp] at step
  all_goals try contradiction
  case request | acquire =>
    rcases (tournamentInstruction_fields step).2.2 with h | ⟨cp, h⟩ <;>
      simp [h, VisibleControl, Queued] at after
  all_goals try (obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp step)
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try split_ifs at after
  all_goals simp_all [VisibleControl, Queued]

/-- A visible occurrence has one actual enqueue and a continuous visible
interval since that enqueue. Resets cannot be hidden by identifier equality. -/
theorem visible_enqueue_history {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {finish : Nat} (visibleAt : visible (r.state finish p).value.clock = true) :
    ∃ arrival, arrival < finish ∧ r.event arrival = .enqueue p ∧
      ∀ t, arrival < t → t ≤ finish → visible (r.state t p).value.clock = true := by
  have facts t := (reachable_invariant (r.reachable t)).localFacts p
  obtain ⟨arrival, lt, event, states⟩ := phase_history
    (fun t => VisibleControl (r.state t p).pc)
    (fun t => EnqueueEvent (r.state t) (r.command t) p)
    (by simp [r.initialized, initial, reset, VisibleControl, Queued])
    (fun t after => next_phase_origin VisibleControl EnqueueEvent
      (by simp [VisibleControl, Queued]) (by simp [VisibleControl, Queued])
      (fun out step h => ordinary_visible_origin step h) (r.valid t) after)
    ((visible_control_iff (facts finish)).mp visibleAt)
  exact ⟨arrival, lt, event, fun t lo hi => (visible_control_iff (facts t)).mpr (states t lo hi)⟩

/-- Once later enqueues are excluded, arbitrarily late visibility really does
identify a single surviving visible episode. No minimum off duration is needed. -/
theorem recurring_without_enqueue_survives {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {bound : Nat}
    (noEnqueue : ∀ t, bound < t → r.event t ≠ .enqueue p)
    (recurring : ∀ limit, ∃ t, limit ≤ t ∧ visible (r.state t p).value.clock = true) :
    ∀ t, bound < t → visible (r.state t p).value.clock = true := by
  intro t lo
  obtain ⟨later, hi, vis⟩ := recurring t
  obtain ⟨arrival, _, event, interval⟩ := visible_enqueue_history r vis
  have early : arrival ≤ bound := by
    by_contra bad
    exact noEnqueue arrival (by omega) event
  exact interval t (by omega) hi

private theorem release_eventually_invisible {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (release : (r.state start p).pc = .release) :
    ∃ finish, start < finish ∧ visible (r.state finish p).value.clock = false := by
  obtain ⟨t, lo, act, same⟩ := first_scheduled_action r fair
    (p := p) (start := start) (by simp [release, Protocol])
  have pc : (r.state t p).pc = .release := by rw [same]; exact release
  have step := r.valid t
  refine ⟨t + 1, by omega, ?_⟩
  rcases act with run | fail
  · simp only [run, next, ordinary, pc, Option.map_some, Option.some.injEq] at step
    rw [← step]; simp [dead, visible]
  · simp only [fail, next, pc, reduceCtorEq, ↓reduceIte, Option.some.injEq] at step
    rw [← step]; simp [reset, dead, visible]

/-- A continuously visible suffix cannot be a completed outer episode:
completion and the separately scheduled release force actual invisibility. -/
theorem forever_visible_queued {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    {p : Proc n} {start : Nat}
    (vis : ∀ t, start ≤ t → visible (r.state t p).value.clock = true) :
    ∀ t, start ≤ t → Queued (r.state t p).pc := by
  intro t lo
  have control := (visible_control_iff ((reachable_invariant (r.reachable t)).localFacts p)).mp (vis t lo)
  rcases control with queued | critical | release
  · exact queued
  · obtain ⟨finish, hi, gone⟩ := critical_eventually_invisible r fair completion critical
    have := vis finish (by omega)
    simp [gone] at this
  · obtain ⟨finish, hi, gone⟩ := release_eventually_invisible r fair release
    have := vis finish (by omega)
    simp [gone] at this

private theorem outcome_not_queued_after {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {t : Nat} (outcome : Outcome r p t) :
    ¬ Queued (r.state (t + 1) p).pc := by
  have step := r.valid t
  rcases outcome with entry | fail
  · obtain ⟨command, pc⟩ := entry_event_iff.mp entry
    simp only [command, next, ordinary, pc, Option.map_some, Option.some.injEq] at step
    rw [← step]; simp [Queued]
  · have command : r.command t = .fail p := by
      rcases completion_event_acts (Or.inr fail) with ⟨run, pc⟩ | failed
      · simp [Run.event, run, label, pc] at fail
      · exact failed
    simp only [command, next] at step
    split at step
    · contradiction
    · have eq := Option.some.inj step
      rw [← eq]; simp [reset, Queued]

/-- Continuous visibility, with the two frozen progress premises, leaves the
same episode queued forever and excludes any own entry or failure. -/
theorem forever_visible_unresolved {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    {p : Proc n} {start : Nat}
    (vis : ∀ t, start ≤ t → visible (r.state t p).value.clock = true) :
    ∀ t, start ≤ t → ¬ Outcome r p t := by
  intro t lo outcome
  exact outcome_not_queued_after r outcome
    (forever_visible_queued r fair completion vis (t + 1) (by omega))

/-- Every hypothetically unresolved enqueue has a distinct, strictly earlier
unresolved enqueue. Mixed-time list construction contributes no assumed order:
real later admissions are removed, and actual recurring visibility reconstructs
the earlier surviving episode. -/
theorem unresolved_enqueue_predecessor {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    {p : Proc n} {arrival : Nat} (event : r.event arrival = .enqueue p)
    (none : ∀ t, arrival < t → ¬ Outcome r p t) :
    ∃ q earlier, q ≠ p ∧ earlier < arrival ∧ r.event earlier = .enqueue q ∧
      (∀ t, earlier < t → visible (r.state t q).value.clock = true) ∧
      (∀ t, earlier < t → ¬ Outcome r q t) := by
  have queued := enqueue_queued (r.valid arrival) event
  have laterNone : ∀ t, arrival + 1 ≤ t → ¬ Outcome r p t := by
    intro t lo; exact none t (by omega)
  obtain ⟨stable, lo, nonempty, fixed, recurring⟩ := unresolved_stable_blockers r fair queued laterNone
  obtain ⟨q, member⟩ := nonempty
  have other : q ≠ p := by
    intro eq; subst q
    exact (reachable_selfFree (r.reachable stable) p).1 member
  have noEnqueue : ∀ t, arrival < t → r.event t ≠ .enqueue q := by
    intro t hi later
    have removed := unresolved_later_enqueue_absent r fair other hi event none later
      (max t stable) (le_max_left _ _)
    rw [fixed _ (le_max_right _ _)] at removed
    exact removed member
  have vis := recurring_without_enqueue_survives r noEnqueue (recurring q member other)
  obtain ⟨earlier, hi, predecessor, interval⟩ := visible_enqueue_history r (vis (arrival + 1) (by omega))
  have earlierLT : earlier < arrival := by
    have ne : earlier ≠ arrival := by
      intro eq
      rw [eq, event] at predecessor
      exact other (Label.enqueue.inj predecessor).symm
    omega
  have allVisible : ∀ t, earlier < t → visible (r.state t q).value.clock = true := by
    intro t low
    by_cases before : t ≤ arrival + 1
    · exact interval t low before
    · exact vis t (by omega)
  refine ⟨q, earlier, other, earlierLT, predecessor, allVisible, ?_⟩
  intro t low
  exact forever_visible_unresolved r fair completion
    (start := earlier + 1) (fun u hu => allVisible u (by omega)) t (by omega)

/-- Enqueue times are natural numbers, so the derived predecessor relation
cannot sustain a cycle or an infinite unresolved chain. -/
theorem enqueue_eventually_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    {p : Proc n} {arrival : Nat} (event : r.event arrival = .enqueue p) :
    ∃ finish, arrival < finish ∧ Outcome r p finish := by
  induction arrival using Nat.strong_induction_on generalizing p with
  | h arrival ih =>
    by_contra missing
    have none : ∀ t, arrival < t → ¬ Outcome r p t := by
      simpa only [not_exists, not_and] using missing
    obtain ⟨q, earlier, _, lt, predecessor, _, unresolved⟩ :=
      unresolved_enqueue_predecessor r fair completion event none
    obtain ⟨finish, hi, outcome⟩ := ih earlier lt predecessor
    exact unresolved finish hi outcome

private theorem ordinary_queued_origin {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {out : Local n} (step : ordinary cfg s p = some out)
    (after : Queued out.pc) : Queued (s p).pc ∨ EnqueueEvent s (.run p) p := by
  rcases ordinary_visible_origin step (Or.inl after) with control | event
  · rcases control with queued | critical | release
    · exact Or.inl queued
    · simp only [ordinary, critical, Option.some.injEq] at step
      subst out; simp [Queued] at after
    · simp only [ordinary, release, Option.some.injEq] at step
      subst out; simp [Queued] at after
  · exact Or.inr event

/-- Every queued occurrence still belongs to its original enqueue; the full
interval is queued, excluding earlier entry, release, failure and replacement. -/
theorem queued_enqueue_history {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {finish : Nat} (queued : Queued (r.state finish p).pc) :
    ∃ arrival, arrival < finish ∧ r.event arrival = .enqueue p ∧
      (∀ t, arrival < t → t ≤ finish → Queued (r.state t p).pc) ∧
      (∀ t, arrival < t → t < finish → ¬ Outcome r p t) := by
  obtain ⟨arrival, lt, event, states⟩ := phase_history
    (fun t => Queued (r.state t p).pc) (fun t => EnqueueEvent (r.state t) (r.command t) p)
    (by simp [r.initialized, initial, reset, Queued])
    (fun t after => next_phase_origin Queued EnqueueEvent (by simp [Queued]) (by simp [Queued])
      (fun out step h => ordinary_queued_origin step h) (r.valid t) after) queued
  refine ⟨arrival, lt, event, states, ?_⟩
  intro t lo hi outcome
  exact outcome_not_queued_after r outcome (states (t + 1) (by omega) (by omega))

/-- Full service from an arbitrary in-flight queued occurrence, with no
empty-list, stable-cohort or clock-success premise. -/
theorem queued_eventually_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    {p : Proc n} {start : Nat} (queued : Queued (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ Outcome r p finish := by
  obtain ⟨arrival, _, event, _, earlierNone⟩ := queued_enqueue_history r queued
  obtain ⟨finish, lo, outcome⟩ := enqueue_eventually_outcome r fair completion event
  have hi : start ≤ finish := by
    by_contra bad
    exact earlierNone finish lo (by omega) outcome
  exact ⟨finish, hi, outcome⟩

/-- The complete frozen outer target: every original pending occurrence reaches
an actual own entry or failure under protocol scheduling and outer completion. -/
theorem pending_eventually_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    {p : Proc n} {start : Nat} (pending : Pending (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ Outcome r p finish := by
  by_contra missing
  have none : ∀ t, start ≤ t → ¬ Outcome r p t := by
    simpa only [not_exists, not_and] using missing
  obtain ⟨queuedAt, lo, queued⟩ := unresolved_pending_queued r fair pending none
  obtain ⟨finish, hi, outcome⟩ := queued_eventually_outcome r fair completion queued
  exact none finish (by omega) outcome

private theorem next_pending {n : Nat} {cfg : Config n} {s t : State n}
    {p : Proc n} {c : Command n} (pending : Pending (s p).pc)
    (step : next cfg s c = some t) (noEntry : label s c ≠ .entry p)
    (noFail : label s c ≠ .fail p) : Pending (t p).pc := by
  rcases pending with doorway | queued
  · by_cases enqueue : label s c = .enqueue p
    · exact Or.inr (enqueue_queued step enqueue)
    · exact Or.inl (doorway_next doorway step enqueue noFail)
  · exact Or.inr (next_queued queued step noEntry noFail)

/-- The least real outcome belongs to the original pending request. Pending
control persists through its endpoint prestate, excluding normal re-request
as well as failure/restart replacement. Immediate failure or entry is allowed. -/
theorem pending_first_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    {p : Proc n} {start : Nat} (pending : Pending (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
      Outcome r p finish ∧
      (∀ t, start ≤ t → t < finish → ¬ Outcome r p t) ∧
      (∀ t, start ≤ t → t ≤ finish → Pending (r.state t p).pc) := by
  classical
  have ex := pending_eventually_outcome r fair completion pending
  have first := Nat.find_spec ex
  have none : ∀ t, start ≤ t → t < Nat.find ex → ¬ Outcome r p t := by
    intro t lo hi outcome
    have := Nat.find_min' ex ⟨lo, outcome⟩
    omega
  refine ⟨Nat.find ex, first.1, ?_, first.2, none, ?_⟩
  · intro t lo hi bad; exact none t lo hi (Or.inr bad)
  · intro t lo hi
    induction t, lo using Nat.le_induction with
    | base => exact pending
    | succ t lo ih =>
      exact next_pending (ih (by omega)) (r.valid t)
        (fun h => none t lo (by omega) (Or.inl h))
        (fun h => none t lo (by omega) (Or.inr h))

/-- Every surviving pending requester enters in that original request. Peer
failure/restart counts and timing remain unrestricted. -/
theorem pending_surviving_enters {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    {p : Proc n} {start : Nat} (pending : Pending (r.state start p).pc)
    (survives : ∀ t, start ≤ t → r.event t ≠ .fail p) :
    ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
      r.event finish = .entry p ∧
      (∀ t, start ≤ t → t < finish → ¬ Outcome r p t) ∧
      (∀ t, start ≤ t → t ≤ finish → Pending (r.state t p).pc) := by
  obtain ⟨finish, lo, episode, outcome, first, states⟩ :=
    pending_first_outcome r fair completion pending
  exact ⟨finish, lo, episode, outcome.resolve_right (survives finish lo), first, states⟩

/-- Deadlock consequence in the reviewed failure-sensitive sense: a surviving
pending request guarantees a new actual entry. -/
theorem surviving_pending_deadlock_freedom {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r) {start : Nat}
    (requester : ∃ p, Pending (r.state start p).pc ∧
      ∀ t, start ≤ t → r.event t ≠ .fail p) :
    ∃ finish p, start ≤ finish ∧ r.event finish = .entry p := by
  obtain ⟨p, pending, survives⟩ := requester
  obtain ⟨finish, lo, _, entry, _, _⟩ := pending_surviving_enters r fair completion pending survives
  exact ⟨finish, p, lo, entry⟩

end EconomicalSolutions.Algorithm6

#print axioms EconomicalSolutions.Algorithm6.enqueue_admission_history
#print axioms EconomicalSolutions.Algorithm6.later_enqueue_admission
#print axioms EconomicalSolutions.Algorithm6.unresolved_later_enqueue_absent


#print axioms EconomicalSolutions.Algorithm6.reachable_selfFree
#print axioms EconomicalSolutions.Algorithm6.visible_enqueue_history
#print axioms EconomicalSolutions.Algorithm6.recurring_without_enqueue_survives
#print axioms EconomicalSolutions.Algorithm6.forever_visible_queued
#print axioms EconomicalSolutions.Algorithm6.forever_visible_unresolved
#print axioms EconomicalSolutions.Algorithm6.unresolved_enqueue_predecessor
#print axioms EconomicalSolutions.Algorithm6.enqueue_eventually_outcome
#print axioms EconomicalSolutions.Algorithm6.queued_enqueue_history
#print axioms EconomicalSolutions.Algorithm6.queued_eventually_outcome
#print axioms EconomicalSolutions.Algorithm6.pending_first_outcome
#print axioms EconomicalSolutions.Algorithm6.pending_surviving_enters
#print axioms EconomicalSolutions.Algorithm6.surviving_pending_deadlock_freedom
