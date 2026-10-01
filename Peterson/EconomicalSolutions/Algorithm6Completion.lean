import Peterson.EconomicalSolutions.Algorithm6Ticking
import Peterson.EconomicalSolutions.Algorithm2Progress

/-! Finite stage 4/5 work and derived completion of the projected tournament.
Only the frozen protocol scheduler is assumed; outer critical completion is absent. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm6

/-- A joining scan cannot return `attempt` before the separate cached write. -/
theorem clock_join_scan {m : Nat} {s : Algorithm3.State m} {i : Fin m}
    {out : Algorithm3.Local} (joining : Joining (s i).pc)
    (noWrite : ∀ b, (s i).pc ≠ .joinWrite b)
    (step : Algorithm3.ordinary s i = some out) : Joining out.pc := by
  cases hp : (s i).pc <;> simp only [hp, Joining] at joining
  case joinWrite b => exact (noWrite b hp).elim
  all_goals simp only [Algorithm3.ordinary, hp] at step
  all_goals split at step <;> try contradiction
  all_goals rename_i valid
  all_goals cases sample : (s ⟨_, valid⟩).q
  all_goals simp only [sample, Option.some.injEq] at step
  all_goals subst out
  all_goals simp only [Algorithm3.joinLower]
  all_goals repeat first | split | trivial

/-- Control facts needed to cover every projected critical occurrence. These
restrict no transition: all are proved from the initialized interpreter. -/
def CompletionFacts {n : Nat} (l : Local n) : Prop :=
  match l.pc with
  | .acquire => Algorithm2.pendingPC l.tournamentPC = true
  | .upperTick count _ => count < 3
  | .lowerJoin cp => Joining cp
  | _ => True

private theorem tournamentInstruction_completionFacts {n : Nat} {cfg : Config n}
    {s : State n} {p : Proc n} {l : Local n}
    (source : (s p).tournamentPC = .idle ∨ Algorithm2.pendingPC (s p).tournamentPC = true)
    (step : tournamentInstruction cfg s p = some l) : CompletionFacts l := by
  unfold tournamentInstruction at step
  obtain ⟨t, ho, eq⟩ := Option.map_eq_some_iff.mp step
  subst l
  dsimp
  split
  · trivial
  · rename_i notCS
    change Algorithm2.pendingPC t.pc = true
    have resum (c : Algorithm2.Continuation) (k : Nat) (v : Algorithm2.Value) :
        Algorithm2.pendingPC (Algorithm2.resume cfg.tournament p c k v) = true := by
      cases c <;> simp only [Algorithm2.resume]
      all_goals repeat first | split | simp [Algorithm2.pendingPC, Algorithm2.scan]
    cases hp : (s p).tournamentPC
    all_goals simp only [hp, Algorithm2.pendingPC] at source
    all_goals try simp at source
    case scan c k rest =>
      cases rest <;> simp only [Algorithm2.ordinary, project, hp, Option.some.injEq] at ho
      all_goals subst t
      all_goals repeat first | apply resum | split | simp [Algorithm2.pendingPC]
    all_goals simp only [Algorithm2.ordinary, project, hp] at ho
    all_goals simp only [Option.some.injEq] at ho
    all_goals subst t
    all_goals repeat first | assumption | apply resum | split | simp_all [Algorithm2.pendingPC, Algorithm2.scan]

private theorem ordinary_completionFacts {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {out : Local n} (link : Linked (s p)) (facts : CompletionFacts (s p))
    (step : ordinary cfg s p = some out) : CompletionFacts out := by
  cases hp : (s p).pc
  case' build rest => cases rest
  case' maintain rest => cases rest
  all_goals simp only [ordinary, hp] at step
  all_goals try contradiction
  case request =>
    apply tournamentInstruction_completionFacts _ step
    simp only [Linked, hp] at link
    exact Or.inl link.1
  case acquire =>
    exact tournamentInstruction_completionFacts (Or.inr (by simpa [CompletionFacts, hp] using facts)) step
  case upperJoin cp =>
    obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step
    subst out; split
    · exact Nat.zero_lt_succ 2
    · trivial
  case upperTick count cp =>
    obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step
    subst out
    have bound : count < 3 := by simpa [CompletionFacts, hp] using facts
    cases cp <;> simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true, ite_false]
    all_goals try exact bound
    all_goals split
    · trivial
    · rename_i ne; simp only [decide_eq_true_eq] at ne
      simp only [CompletionFacts, ite_true]; omega
  case off =>
    simp only [Option.some.injEq] at step; subst out
    exact startJoin_joining p false
  case lowerJoin cp =>
    have join : Joining cp := by simpa [CompletionFacts, hp] using facts
    cases cp <;> simp only [Joining] at join
    case joinWrite b => simp only [Option.some.injEq] at step; subst out; trivial
    all_goals obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step
    all_goals subst out
    all_goals apply clock_join_scan (s := fun j => ⟨clockValue s j,
      if j = position p false then _ else .idle⟩) (i := position p false) (by simp [Joining]) _ hc
    all_goals intro b; simp
  all_goals try (obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step; subst out)
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals repeat first | split | trivial

theorem reachable_completionFacts {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) : ∀ p, CompletionFacts (s p) := by
  induction reach with
  | initial => intro p; trivial
  | @step s t a reach edge ih =>
    obtain ⟨command, step, _⟩ := edge
    cases command with
    | stutter => have eq : s = t := Option.some.inj step; simpa [← eq] using ih
    | run p =>
      obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp step
      intro q
      by_cases eq : q = p
      · subst q; simpa using ordinary_completionFacts ((reachable_projection reach).1 p) (ih p) ho
      · simpa [eq] using ih q
    | fail p | restart p =>
      simp only [next] at step
      split at step <;> try contradiction
      all_goals simp only [Option.some.injEq] at step; subst t; intro q
      all_goals by_cases eq : q = p
      all_goals first | (subst q; simp [reset, CompletionFacts]) | simpa [eq] using ih q

/-- Stage 4 and stage 5 preparation, including an arbitrary remaining scan. -/
def PostThird {n : Nat} : PC n → Prop
  | .build _ | .off | .lowerJoin _ | .complete _ => True
  | _ => False

/-- The real private instruction which completes the tournament's local
critical work. The following enqueue instruction still owns the tournament. -/
def LocalComplete {n : Nat} (s : State n) (command : Command n) (p : Proc n) : Prop :=
  command = .run p ∧ ∃ b, (s p).pc = .complete b

def CompletionOutcome {n : Nat} {cfg : Config n} (r : Run cfg) (p : Proc n) (t : Nat) : Prop :=
  LocalComplete (r.state t) (r.command t) p ∨ r.event t = .fail p

def postThirdRank {n : Nat} : PC n → Nat
  | .build rest => rest.length + 4 * n + 5
  | .off => 4 * n + 4
  | .lowerJoin cp => joinRank (2 * n) cp + 1
  | .complete _ => 1
  | _ => 0

private theorem lower_start_rank {n : Nat} (p : Proc n) :
    joinRank (2 * n) (startJoin p false) < 4 * n + 3 := by
  unfold startJoin Algorithm3.joinLower
  have bound := p.isLt
  simp only [position, Bool.false_eq_true, ite_false]
  split
  · simp only [joinRank]; omega
  · split <;> simp only [joinRank] <;> omega

theorem post_third_ordinary {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {out : Local n} (facts : CompletionFacts (s p)) (post : PostThird (s p).pc)
    (step : ordinary cfg s p = some out) :
    postThirdRank out.pc < postThirdRank (s p).pc ∧
      (¬ LocalComplete s (.run p) p → PostThird out.pc) := by
  cases hp : (s p).pc <;> simp only [hp, PostThird] at post
  case build rest =>
    cases rest <;> simp only [ordinary, hp, Option.some.injEq] at step
    all_goals subst out; simp [postThirdRank, hp, PostThird]
  case off =>
    simp only [ordinary, hp, Option.some.injEq] at step
    subst out
    have bound := lower_start_rank p
    exact ⟨by simp only [postThirdRank, hp]; omega, fun _ => trivial⟩
  case complete b =>
    simp only [ordinary, hp, Option.some.injEq] at step
    subst out
    exact ⟨by simp [postThirdRank, hp], fun no => (no ⟨rfl, b, hp⟩).elim⟩
  case lowerJoin cp =>
    have join : Joining cp := by simpa [CompletionFacts, hp] using facts
    cases cp <;> simp only [Joining] at join
    case joinWrite b =>
      simp only [ordinary, hp, Option.some.injEq] at step
      subst out; simp [postThirdRank, hp, joinRank, PostThird]
    all_goals simp only [ordinary, hp] at step
    all_goals obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step
    all_goals subst out
    all_goals have less := (clock_join_step (s := fun j => ⟨clockValue s j,
      if j = position p false then _ else .idle⟩) (i := position p false) (by simp [Joining]) hc).2
    all_goals exact ⟨by simpa [postThirdRank, hp] using Nat.add_lt_add_right less 1, fun _ => trivial⟩

theorem next_post_third {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {p : Proc n} (reach : Reachable cfg s)
    (post : PostThird (s p).pc) (step : next cfg s command = some t)
    (noComplete : ¬ LocalComplete s command p) (noFail : label s command ≠ .fail p) :
    PostThird (t p).pc ∧
      (Acts command p → postThirdRank (t p).pc < postThirdRank (s p).pc) := by
  by_cases act : Acts command p
  · rcases act with rfl | rfl
    · obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp step
      have result := post_third_ordinary (reachable_completionFacts reach p) post ho
      exact ⟨by simpa using result.2 noComplete, by intro _; simpa using result.1⟩
    · exact (noFail rfl).elim
  · have live : (s p).pc ≠ .down := by intro eq; simp [eq, PostThird] at post
    have eq := next_live_unchanged step live act
    exact ⟨by simpa [eq] using post, fun h => (act h).elim⟩

/-- Finite list construction and lower joining reach the real local completion
instruction or own failure. Every scan may already be partly executed. -/
theorem post_third_eventually {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (post : PostThird (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ CompletionOutcome r p finish := by
  classical
  by_contra missing
  have none : ∀ t, start ≤ t → ¬ CompletionOutcome r p t := by
    intro t lo outcome; exact missing ⟨t, lo, outcome⟩
  have stays : ∀ t, start ≤ t → PostThird (r.state t p).pc := by
    intro t lo
    induction t, lo using Nat.le_induction with
    | base => exact post
    | succ t lo ih =>
      exact (next_post_third (r.reachable t) ih (r.valid t)
        (fun h => none t lo (Or.inl h)) (fun h => none t lo (Or.inr h))).1
  apply fair_descent_impossible r fair p start (fun l => postThirdRank l.pc)
  · intro t lo
    have := stays t lo
    cases hp : (r.state t p).pc <;> simp_all [PostThird, Protocol]
  · intro t lo act
    exact (next_post_third (r.reachable t) (stays t lo) (r.valid t)
      (fun h => none t lo (Or.inl h)) (fun h => none t lo (Or.inr h))).2 act

/-- The first local-completion-or-failure endpoint retains the original
post-third occurrence, with its control region preserved through the prestate. -/
theorem post_third_original_episode {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (post : PostThird (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
      CompletionOutcome r p finish ∧
      (∀ t, start ≤ t → t < finish → ¬ CompletionOutcome r p t) ∧
      (∀ t, start ≤ t → t ≤ finish → PostThird (r.state t p).pc) := by
  classical
  have ex := post_third_eventually r fair post
  have first := Nat.find_spec ex
  have none : ∀ t, start ≤ t → t < Nat.find ex → ¬ CompletionOutcome r p t := by
    intro t lo hi outcome
    have := Nat.find_min' ex ⟨lo, outcome⟩
    omega
  refine ⟨Nat.find ex, first.1, ?_, first.2, none, ?_⟩
  · intro t lo hi bad; exact none t lo hi (Or.inr bad)
  · intro t lo hi
    induction t, lo using Nat.le_induction with
    | base => exact post
    | succ t lo ih =>
      exact (next_post_third (r.reachable t) (ih (by omega)) (r.valid t)
        (fun h => none t lo (by omega) (Or.inl h))
        (fun h => none t lo (by omega) (Or.inr h))).1

/-- The actual third cached write enters stage 4 in its successor state. -/
theorem third_upper_write_starts_build {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {time : Nat} (third : ThirdUpperWrite r p time) :
    (r.state (time + 1) p).pc = .build (cfg.order p) := by
  obtain ⟨command, bit, pc⟩ := third
  obtain ⟨old, own⟩ := reachable_upper_tick_occupied (r.reachable time) pc
  have ownClock : clockValue (r.state time) (position p true) = some old := by
    simp [clockValue, position, own]
  have step := r.valid time
  simp only [command, next, ordinary, pc, clockInstruction, Algorithm3.ordinary,
    ite_true, ownClock, bind, pure, Option.bind] at step
  simp only [Bool.true_and, decide_true, ite_true] at step
  split at step
  · simp only [Option.map_some, Option.some.injEq] at step
    rw [← step]; simp
  · simp at step

private theorem same_episode_splice {n : Nat} {cfg : Config n} (r : Run cfg)
    (p : Proc n) {a middle finish : Nat} (before : SameEpisodeUntil r p a middle)
    (noFail : r.event middle ≠ .fail p)
    (after : SameEpisodeUntil r p (middle + 1) finish) : SameEpisodeUntil r p a finish := by
  intro t lo hi
  by_cases lt : t < middle
  · exact before t lo lt
  · by_cases eq : t = middle
    · subst t; exact noFail
    · exact after t (by omega) hi

/-- Compose the reviewed upper termination with finite stage 4/5 work in the
same admission. In particular, a restarted request cannot pay this debt. -/
theorem before_third_local_completion {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (before : BeforeThird (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
      CompletionOutcome r p finish := by
  obtain ⟨third, lo, episode, outcome⟩ := upper_termination n cfg r fair p start before
  rcases outcome with written | fail
  · have post := third_upper_write_starts_build r written
    obtain ⟨finish, hi, rest, done, _, _⟩ := post_third_original_episode r fair
      (p := p) (start := third + 1) (by simp [post, PostThird])
    refine ⟨finish, by omega, same_episode_splice r p episode ?_ rest, done⟩
    rcases written with ⟨command, b, pc⟩
    simp [Run.event, command, label, pc]
  · exact ⟨third, lo, episode, Or.inr fail⟩

/-- The same step-for-step projection used by finite safety, now on an
initialized infinite execution. All clock/list instructions project to stutter. -/
def Run.tournament {n : Nat} {cfg : Config n} (r : Run cfg) : Algorithm2.Run cfg.tournament where
  state t := project (r.state t)
  command t := projectCommand (r.state t) (r.command t)
  initialized := by rw [r.initialized]; rfl
  valid t := next_projection (reachable_projection (r.reachable t)).1 (r.valid t)

theorem projected_failure_iff {n : Nat} {cfg : Config n} (r : Run cfg) (t : Nat) (p : Proc n) :
    r.tournament.event t = .fail p ↔ r.event t = .fail p := by
  have step := r.valid t
  have link := (reachable_projection (r.reachable t)).1
  cases hc : r.command t with
  | stutter => simp [Run.tournament, Algorithm2.Run.event, Run.event, hc, projectCommand, label, Algorithm2.label]
  | restart q => simp [Run.tournament, Algorithm2.Run.event, Run.event, hc, projectCommand, label, Algorithm2.label]
  | run q =>
    cases hp : (r.state t q).pc
    case' upperJoin cp => cases cp
    case' upperTick count cp => cases cp
    case' lowerTick cp => cases cp
    all_goals simp [Run.tournament, Algorithm2.Run.event, Run.event, hc, projectCommand, hp, label, Algorithm2.label]
    all_goals cases ht : (r.state t q).tournamentPC <;> simp [project, ht]
  | fail q =>
    rw [hc] at step
    have live : (r.state t q).pc ≠ .down := by intro hp; simp [next, hp] at step
    have inner : (r.state t q).tournamentPC ≠ .down := by
      have l := link q
      cases hp : (r.state t q).pc <;> simp_all [Linked]
    simp [Run.tournament, Algorithm2.Run.event, Run.event, hc, projectCommand, inner, label, Algorithm2.label]

theorem local_complete_projects {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {t : Nat} (complete : LocalComplete (r.state t) (r.command t) p) :
    r.tournament.event t = .complete p := by
  obtain ⟨command, b, pc⟩ := complete
  have inner : (r.state t p).tournamentPC = .cs := by
    simpa [Linked, pc] using (reachable_projection (r.reachable t)).1 p
  simp [Run.tournament, Algorithm2.Run.event, projectCommand, command, pc, Algorithm2.label, project, inner]

/-- Every projected critical occurrence is either before the third upper
write or in its finite stage 4/5 suffix. Acquisition cannot already be critical. -/
theorem projected_critical_location {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) {p : Proc n} (inner : (s p).tournamentPC = .cs) :
    BeforeThird (s p).pc ∨ PostThird (s p).pc := by
  have link := (reachable_projection reach).1 p
  have facts := reachable_completionFacts reach p
  cases hp : (s p).pc <;>
    simp_all [Linked, CompletionFacts, Algorithm2.pendingPC, BeforeThird, PostThird]

/-- Local completion changes only private tournament control; the admission
register is still held. Its next own instruction combines release and enqueue. -/
theorem local_complete_poststate {n : Nat} {cfg : Config n} {s t : State n}
    {p : Proc n} {b : Bool} (pc : (s p).pc = .complete b)
    (step : next cfg s (.run p) = some t) :
    (t p).pc = .enqueue b ∧ (t p).tournamentPC = .release ∧
      (t p).value = (s p).value := by
  simp only [next, ordinary, pc, Option.map_some, Option.some.injEq] at step
  subst t; simp

/-- The scheduled combined write publishes the prepared lower candidate and
releases the tournament in that same atomic register update. -/
theorem enqueue_poststate {n : Nat} {cfg : Config n} {s t : State n}
    {p : Proc n} {b : Bool} (pc : (s p).pc = .enqueue b)
    (step : next cfg s (.run p) = some t) :
    (t p).pc = .maintain (cfg.order p) ∧ (t p).tournamentPC = .idle ∧
      (t p).value = ⟨Algorithm2.dead, .lower b⟩ := by
  simp only [next, ordinary, pc, Option.map_some, Option.some.injEq] at step
  subst t; simp

/-- A prepared publication either executes or fails in its original episode.
The cached candidate and enqueue control persist through the endpoint prestate. -/
theorem enqueue_original_episode {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat} {b : Bool}
    (pc : (r.state start p).pc = .enqueue b) :
    ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
      (r.event finish = .enqueue p ∨ r.event finish = .fail p) ∧
      (∀ t, start ≤ t → t ≤ finish → (r.state t p).pc = .enqueue b) := by
  classical
  have ex := fair start p (by simp [pc, Protocol])
  have first := Nat.find_spec ex
  have noAct : ∀ t, start ≤ t → t < Nat.find ex → ¬ Acts (r.command t) p := by
    intro t lo hi act
    have := Nat.find_min' ex ⟨lo, act⟩
    omega
  have stays : ∀ t, start ≤ t → t ≤ Nat.find ex → r.state t p = r.state start p := by
    intro t lo hi
    induction t, lo using Nat.le_induction with
    | base => rfl
    | succ t lo ih =>
      have prev := ih (by omega)
      exact (next_live_unchanged (r.valid t) (by simp [prev, pc]) (noAct t lo (by omega))).trans prev
  refine ⟨Nat.find ex, first.1, ?_, ?_, ?_⟩
  · intro t lo hi fail
    have act : r.command t = .fail p := by
      cases hc : r.command t
      case' run q =>
        cases hp : (r.state t q).pc
        case' upperJoin cp => cases cp
        case' upperTick count cp => cases cp
        case' lowerTick cp => cases cp
      all_goals simp_all [Run.event, label]
    exact noAct t lo hi (Or.inr act)
  · rcases first.2 with run | fail
    · exact Or.inl (by simp [Run.event, run, label, stays _ first.1 le_rfl, pc])
    · exact Or.inr (by simp [Run.event, fail, label])
  · intro t lo hi; rw [stays t lo hi]; exact pc

/-- From any stage 4/5 occurrence the original admission reaches the actual
combined lower publication or its own failure. The tournament remains held
through every prestate, including a failure endpoint. -/
theorem post_third_enqueue_original_episode {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (post : PostThird (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
      (r.event finish = .enqueue p ∨ r.event finish = .fail p) ∧
      (∀ t, start ≤ t → t ≤ finish → Holding (r.state t p).pc) := by
  obtain ⟨complete, lo, before, result, _, states⟩ := post_third_original_episode r fair post
  rcases result with completed | failed
  · obtain ⟨command, b, pc⟩ := completed
    have nextpc := (local_complete_poststate pc (by simpa [command] using r.valid complete)).1
    obtain ⟨finish, hi, after, outcome, waiting⟩ := enqueue_original_episode r fair nextpc
    refine ⟨finish, by omega, same_episode_splice r p before ?_ after, outcome, ?_⟩
    · simp [Run.event, command, label, pc]
    · intro t startLo endHi
      by_cases early : t ≤ complete
      · have control := states t startLo early
        cases hp : (r.state t p).pc <;> simp_all [PostThird, Holding]
      · simp [waiting t (by omega) endHi, Holding]
  · refine ⟨complete, lo, before, Or.inr failed, ?_⟩
    intro t startLo endHi
    have control := states t startLo endHi
    cases hp : (r.state t p).pc <;> simp_all [PostThird, Holding]

/-- With no local completion or own failure, the original projected critical
control persists. No normal release/re-entry can be substituted. -/
theorem next_projected_critical {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {p : Proc n} (reach : Reachable cfg s)
    (inner : (s p).tournamentPC = .cs) (step : next cfg s command = some t)
    (noComplete : ¬ LocalComplete s command p) (noFail : label s command ≠ .fail p) :
    (t p).tournamentPC = .cs := by
  have loc := projected_critical_location reach inner
  by_cases act : Acts command p
  · rcases act with rfl | rfl
    · obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp step
      simp only [setLocal_self]
      cases hp : (s p).pc <;> simp only [hp, BeforeThird, PostThird] at loc
      all_goals try simp at loc
      case complete b => exact (noComplete ⟨rfl, b, hp⟩).elim
      case' build rest => cases rest
      case' lowerJoin cp => cases cp
      all_goals simp only [ordinary, hp] at ho
      all_goals try (obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp ho; subst out)
      all_goals try (simp only [Option.some.injEq] at ho; subst out)
      all_goals exact inner
    · exact (noFail rfl).elim
  · have live : (s p).pc ≠ .down := by
      intro hp; simp [hp, BeforeThird, PostThird] at loc
    rw [next_live_unchanged step live act]; exact inner

/-- Every projected critical occurrence has a first real local completion or
own failure, with the original critical control retained through its prestate.
The inclusive endpoint covers immediate failure and already-ready completion. -/
theorem tournament_local_completion_original_episode {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (inner : (r.state start p).tournamentPC = .cs) :
    ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
      CompletionOutcome r p finish ∧
      (∀ t, start ≤ t → t < finish → ¬ CompletionOutcome r p t) ∧
      (∀ t, start ≤ t → t ≤ finish → (r.state t p).tournamentPC = .cs) := by
  classical
  have loc := projected_critical_location (r.reachable start) inner
  have ex : ∃ finish, start ≤ finish ∧ CompletionOutcome r p finish := by
    rcases loc with before | post
    · obtain ⟨finish, lo, _, outcome⟩ := before_third_local_completion r fair before
      exact ⟨finish, lo, outcome⟩
    · exact post_third_eventually r fair post
  have first := Nat.find_spec ex
  have none : ∀ t, start ≤ t → t < Nat.find ex → ¬ CompletionOutcome r p t := by
    intro t lo hi outcome
    have := Nat.find_min' ex ⟨lo, outcome⟩
    omega
  refine ⟨Nat.find ex, first.1, ?_, first.2, none, ?_⟩
  · intro t lo hi bad; exact none t lo hi (Or.inr bad)
  · intro t lo hi
    induction t, lo using Nat.le_induction with
    | base => exact inner
    | succ t lo ih =>
      exact next_projected_critical (r.reachable t) (ih (by omega)) (r.valid t)
        (fun h => none t lo (by omega) (Or.inl h))
        (fun h => none t lo (by omega) (Or.inr h))

/-- The exact E3 client interface is derived, with no assumed tournament or
outer critical completion. It includes failures and arbitrary in-flight starts. -/
theorem tournament_completion {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) : Algorithm2.CriticalCompletion r.tournament := by
  intro start p inner
  obtain ⟨finish, lo, _, outcome, _, _⟩ := tournament_local_completion_original_episode r fair inner
  refine ⟨finish, lo, ?_⟩
  rcases outcome with complete | fail
  · exact Or.inl (local_complete_projects r complete)
  · exact Or.inr ((projected_failure_iff r finish p).2 fail)

end EconomicalSolutions.Algorithm6

#print axioms EconomicalSolutions.Algorithm6.reachable_completionFacts
#print axioms EconomicalSolutions.Algorithm6.post_third_original_episode
#print axioms EconomicalSolutions.Algorithm6.third_upper_write_starts_build
#print axioms EconomicalSolutions.Algorithm6.before_third_local_completion
#print axioms EconomicalSolutions.Algorithm6.tournament_completion
#print axioms EconomicalSolutions.Algorithm6.local_complete_poststate
#print axioms EconomicalSolutions.Algorithm6.enqueue_poststate
#print axioms EconomicalSolutions.Algorithm6.post_third_enqueue_original_episode

#print axioms EconomicalSolutions.Algorithm6.tournament_local_completion_original_episode
