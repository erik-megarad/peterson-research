import Peterson.EconomicalSolutions.Algorithm6Completion

/-! The complete critical-independent doorway, from the original outer request.
Both E3 client premises are derived from Algorithm 6 protocol scheduling. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm6

theorem projected_protocol_location {n : Nat} {l : Local n} (link : Linked l)
    (owed : Algorithm2.protocolPC l.tournamentPC = true) :
    Protocol l.pc ∧ (l.pc = .acquire ∨ ∃ b, l.pc = .enqueue b) := by
  cases hp : l.pc <;> simp_all [Linked, Protocol, Algorithm2.protocolPC, Algorithm2.pendingPC]

/-- Only acquisition and the combined enqueue/release owe projected protocol
work. Their first own action is an actual E3 instruction or failure. -/
theorem tournament_scheduling {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) : Algorithm2.ProtocolScheduling r.tournament := by
  intro t p owed
  have loc := projected_protocol_location ((reachable_projection (r.reachable t)).1 p) owed
  obtain ⟨u, lo, act, same⟩ := first_scheduled_action r fair loc.1
  refine ⟨u, lo, ?_⟩
  have current : (r.state u p).tournamentPC ≠ .down := by
    intro down
    change Algorithm2.protocolPC (r.state t p).tournamentPC = true at owed
    rw [same] at down
    simp [down, Algorithm2.protocolPC, Algorithm2.pendingPC] at owed
  rcases act with act | act
  · left
    change projectCommand (r.state u) (r.command u) = .run p
    rcases loc.2 with hp | ⟨b, hp⟩ <;> simp [act, projectCommand, same, hp]
  · right
    simp [Run.tournament, act, projectCommand, current]

/-- Precisely the pending controls before lower publication. Outer idle,
post-enqueue waiting, critical occupancy and final release are excluded. -/
def Doorway {n : Nat} : PC n → Prop
  | .request | .acquire | .upperJoin _ | .upperTick _ _ | .build _
    | .off | .lowerJoin _ | .complete _ | .enqueue _ => True
  | _ => False

def DoorwayOutcome {n : Nat} {cfg : Config n} (r : Run cfg) (p : Proc n) (t : Nat) : Prop :=
  r.event t = .enqueue p ∨ r.event t = .fail p

/-- This control region persists until the actual enqueue or own failure.
The assertion uses the full interpreter, including arbitrary cached controls. -/
theorem doorway_next {n : Nat} {cfg : Config n} {s t : State n} {p : Proc n}
    {c : Command n} (h : Doorway (s p).pc) (step : next cfg s c = some t)
    (ne : label s c ≠ .enqueue p) (nf : label s c ≠ .fail p) : Doorway (t p).pc := by
  by_cases act : Acts c p
  · rcases act with rfl | rfl
    · obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp step
      simp only [setLocal_self]
      cases hp : (s p).pc <;> simp only [Doorway, hp] at h
      case request | acquire =>
        simp only [ordinary, hp, tournamentInstruction] at ho
        obtain ⟨inner, _, eq⟩ := Option.map_eq_some_iff.mp ho
        subst out; split <;> trivial
      case enqueue b => exact (ne (by simp [label, hp])).elim
      case' build rest => cases rest
      case' lowerJoin cp => cases cp
      all_goals simp only [ordinary, hp] at ho
      all_goals try (obtain ⟨clock, _, eq⟩ := Option.map_eq_some_iff.mp ho; subst out)
      all_goals try (simp only [Option.some.injEq] at ho; subst out)
      all_goals repeat first | split | trivial
    · exact (nf rfl).elim
  · have live : (s p).pc ≠ .down := by intro hp; simp [Doorway, hp] at h
    simpa [next_live_unchanged step live act] using h

/-- All admitted controls, including cached enqueue, reach the real publication
or fail. The earlier three-tick and finite-suffix results supply the work. -/
theorem holding_eventually_enqueue {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (held : Holding (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ DoorwayOutcome r p finish := by
  have casesPC : (∃ b, (r.state start p).pc = .enqueue b) ∨
      (r.state start p).tournamentPC = .cs := by
    have link := (reachable_projection (r.reachable start)).1 p
    cases hp : (r.state start p).pc <;> simp_all [Holding, Linked]
  rcases casesPC with ⟨b, pc⟩ | inner
  · obtain ⟨finish, lo, _, outcome, _⟩ := enqueue_original_episode r fair pc
    exact ⟨finish, lo, outcome⟩
  · obtain ⟨complete, lo, _, outcome, _, _⟩ :=
      tournament_local_completion_original_episode r fair inner
    rcases outcome with ⟨command, b, pc⟩ | fail
    · have nextpc := (local_complete_poststate pc (by simpa [command] using r.valid complete)).1
      obtain ⟨finish, hi, _, done, _⟩ := enqueue_original_episode r fair nextpc
      exact ⟨finish, by omega, done⟩
    · exact ⟨complete, lo, Or.inr fail⟩

/-- The outer request instruction starts a pending E3 request, including the
singleton's separately scheduled tournament entry. -/
theorem request_next_pending {n : Nat} {cfg : Config n} {s t : State n} {p : Proc n}
    (link : Linked (s p)) (pc : (s p).pc = .request)
    (step : next cfg s (.run p) = some t) : Algorithm2.Pending (project t) p := by
  have inner : (s p).tournamentPC = .idle := by
    have h : (s p).tournamentPC = .idle ∧ (s p).value.tournament = Algorithm2.dead := by
      simpa [Linked, pc] using link
    exact h.1
  simp only [next, ordinary, pc, tournamentInstruction, Algorithm2.ordinary, project, inner] at step
  split at step
  all_goals simp only [Option.map_some, Option.some.injEq] at step
  all_goals subst t; simp [Algorithm2.Pending, Algorithm2.pendingPC, Algorithm2.scan, project]

/-- Existence uses both derived E3 premises and real entry/completion successor
states. No assumption about outer critical completion is present. -/
theorem doorway_eventually_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (doorway : Doorway (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ DoorwayOutcome r p finish := by
  classical
  by_contra no
  have none : ∀ t, start ≤ t → ¬ DoorwayOutcome r p t := by
    simpa only [not_exists, not_and] using no
  have noHolding : ∀ t, start ≤ t → ¬ Holding (r.state t p).pc := by
    intro t lo h
    obtain ⟨u, bound, outcome⟩ := holding_eventually_enqueue r fair h
    exact none u (by omega) outcome
  have pending : ∃ t, start ≤ t ∧ Algorithm2.Pending (r.tournament.state t) p := by
    have casesPC : (r.state start p).pc = .request ∨ (r.state start p).pc = .acquire := by
      have noH := noHolding start le_rfl
      cases hp : (r.state start p).pc <;> simp_all [Doorway, Holding]
    rcases casesPC with request | acquire
    · obtain ⟨t, lo, act, same⟩ := first_scheduled_action r fair
        (p := p) (start := start) (by simp [request, Protocol])
      rcases act with act | act
      · refine ⟨t + 1, by omega, ?_⟩
        exact request_next_pending ((reachable_projection (r.reachable t)).1 p)
          (by rw [same]; exact request) (by simpa [act] using r.valid t)
      · exact (none t lo (Or.inr (by simp [Run.event, label, act]))).elim
    · refine ⟨start, le_rfl, ?_⟩
      have facts := reachable_completionFacts (r.reachable start) p
      simpa [Algorithm2.Pending, Run.tournament, project, CompletionFacts, acquire] using facts
  obtain ⟨t, lo, pending⟩ := pending
  obtain ⟨u, bound, outcome, _⟩ := Algorithm2.pending_first_outcome r.tournament
    (tournament_scheduling r fair) (tournament_completion r fair) pending
  rcases outcome with entry | failure
  · obtain ⟨command, inner⟩ := Algorithm2.event_entry_local _ _ _ entry
    have step := r.tournament.valid u
    simp only [command, Algorithm2.next, Algorithm2.ordinary, inner,
      Option.map_some, Option.some.injEq] at step
    have cs : (r.state (u + 1) p).tournamentPC = .cs := by
      change (r.tournament.state (u + 1) p).pc = .cs
      rw [← step]; simp [Algorithm2.setLocal]
    have loc := projected_critical_location (r.reachable (u + 1)) cs
    apply noHolding (u + 1) (by omega)
    cases hp : (r.state (u + 1) p).pc <;> simp_all [BeforeThird, PostThird, Holding]
  · exact none u (by omega) (Or.inr ((projected_failure_iff r u p).1 failure))

/-- The first actual enqueue-or-failure belongs to the original pending outer
occurrence. Controls persist through the inclusive endpoint prestate; no abort,
enqueue or replacement episode can be hidden in the interval. -/
theorem doorway_first_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (doorway : Doorway (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
      DoorwayOutcome r p finish ∧
      (∀ t, start ≤ t → t < finish → ¬ DoorwayOutcome r p t) ∧
      (∀ t, start ≤ t → t ≤ finish → Doorway (r.state t p).pc) := by
  classical
  have ex := doorway_eventually_outcome r fair doorway
  have first := Nat.find_spec ex
  have none : ∀ t, start ≤ t → t < Nat.find ex → ¬ DoorwayOutcome r p t := by
    intro t lo hi outcome
    have := Nat.find_min' ex ⟨lo, outcome⟩
    omega
  refine ⟨Nat.find ex, first.1, ?_, first.2, none, ?_⟩
  · intro t lo hi bad; exact none t lo hi (Or.inr bad)
  · intro t lo hi
    induction t, lo using Nat.le_induction with
    | base => exact doorway
    | succ t lo ih =>
      exact doorway_next (ih (by omega)) (r.valid t)
        (fun h => none t lo (by omega) (Or.inl h))
        (fun h => none t lo (by omega) (Or.inr h))

theorem doorway_surviving_enqueues {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (doorway : Doorway (r.state start p).pc)
    (survives : ∀ t, start ≤ t → r.event t ≠ .fail p) :
    ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
      r.event finish = .enqueue p ∧
      (∀ t, start ≤ t → t < finish → ¬ DoorwayOutcome r p t) ∧
      (∀ t, start ≤ t → t ≤ finish → Doorway (r.state t p).pc) := by
  obtain ⟨finish, lo, episode, outcome, first, states⟩ := doorway_first_outcome r fair doorway
  exact ⟨finish, lo, episode, outcome.resolve_right (survives finish lo), first, states⟩

theorem doorway_no_replacement {n : Nat} (s : State n) (c : Command n) (p : Proc n)
    (doorway : Doorway (s p).pc) : label s c ≠ .request p ∧ label s c ≠ .entry p := by
  cases c with
  | run q =>
    by_cases eq : q = p
    · subst q
      cases hp : (s p).pc <;> simp_all [Doorway, label]
      all_goals cases ‹Algorithm3.PC› <;> simp [label, hp]
    · cases hp : (s q).pc
      case' upperJoin cp => cases cp
      case' upperTick count cp => cases cp
      case' lowerTick cp => cases cp
      all_goals simp [label, hp, eq]
  | fail | restart | stutter => simp [label]

end EconomicalSolutions.Algorithm6

#print axioms EconomicalSolutions.Algorithm6.tournament_scheduling
#print axioms EconomicalSolutions.Algorithm6.holding_eventually_enqueue
#print axioms EconomicalSolutions.Algorithm6.request_next_pending
#print axioms EconomicalSolutions.Algorithm6.doorway_first_outcome
#print axioms EconomicalSolutions.Algorithm6.doorway_surviving_enqueues
#print axioms EconomicalSolutions.Algorithm6.doorway_no_replacement
