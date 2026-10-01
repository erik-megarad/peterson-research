import Peterson.EconomicalSolutions.Algorithm5Capacity
import Peterson.EconomicalSolutions.Algorithm2Progress

/-! The infinite tournament refinement and critical-section-independent doorway. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm5

/-- The actual acquisition interpreter cannot be idle, completed, or released. -/
def AcquisitionLinked {n : Nat} (l : Local n) : Prop :=
  l.pc = .acquire → Algorithm2.pendingPC l.tournamentPC = true

theorem tournamentInstruction_acquisition {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {l : Local n}
    (source : (s p).tournamentPC = .idle ∨ Algorithm2.pendingPC (s p).tournamentPC = true)
    (step : tournamentInstruction cfg s p = some l) : AcquisitionLinked l := by
  unfold tournamentInstruction at step
  cases ho : Algorithm2.ordinary cfg.tournament p (project s) with
  | none => simp [ho] at step
  | some t =>
    simp only [ho, Option.map_some, Option.some.injEq] at step
    subst l
    unfold AcquisitionLinked
    split
    · simp
    · rename_i notCS
      intro _
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

theorem ordinary_acquisition {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {l : Local n} (link : Linked (s p)) (acq : AcquisitionLinked (s p))
    (step : ordinary cfg s p = some l) : AcquisitionLinked l := by
  cases hp : (s p).pc
  all_goals try (rename_i rest m; cases rest)
  all_goals simp only [ordinary, hp] at step
  case request =>
    apply tournamentInstruction_acquisition _ step
    exact Or.inl (by simpa [Linked, hp] using (show (s p).tournamentPC = .idle ∧ _ from by simpa [Linked, hp] using link).1)
  case acquire =>
    exact tournamentInstruction_acquisition (Or.inr (acq hp)) step
  all_goals try contradiction
  all_goals try split at step
  all_goals simp only [Option.some.injEq] at step
  all_goals subst l; simp_all [AcquisitionLinked]

theorem reachable_acquisition {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) : ∀ p, AcquisitionLinked (s p) := by
  induction reach with
  | initial => intro p; simp [initial, AcquisitionLinked]
  | @step s t a reach edge ih =>
    obtain ⟨c, step, _⟩ := edge
    cases c with
    | stutter => simp only [next, Option.some.injEq] at step; subst t; exact ih
    | run p =>
      simp only [next] at step
      cases ho : ordinary cfg s p with
      | none => simp [ho] at step
      | some l =>
        simp only [ho, Option.map_some, Option.some.injEq] at step
        subst t; intro q
        by_cases eq : q = p
        · subst q; simpa using ordinary_acquisition ((reachable_projection reach).1 p) (ih p) ho
        · simpa [eq] using ih q
    | fail p | restart p =>
      simp only [next] at step
      split at step <;> try contradiction
      all_goals simp only [Option.some.injEq] at step; subst t; intro q
      all_goals by_cases eq : q = p
      all_goals simp_all [setLocal, AcquisitionLinked]

/-- Every outer transition supplies one genuine tournament transition, including
explicit global stutter for queue work. -/
def Run.tournament {n : Nat} {cfg : Config n} (r : Run cfg) : Algorithm2.Run cfg.tournament where
  state t := project (r.state t)
  command t := projectCommand (r.state t) (r.command t)
  initialized := by rw [r.initialized]; rfl
  valid t := next_projection (reachable_projection (r.reachable t)).1 (r.valid t)

theorem projected_protocol_location {n : Nat} {l : Local n} (link : Linked l)
    (owed : Algorithm2.protocolPC l.tournamentPC = true) :
    Protocol l.pc ∧ (l.pc = .acquire ∨ l.pc = .depart) := by
  cases hp : l.pc <;> simp_all [Linked, Protocol, Algorithm2.protocolPC, Algorithm2.pendingPC]

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
    rcases loc.2 with hp | hp <;> simp [act, projectCommand, same, hp]
  · right
    simp [Run.tournament, act, projectCommand, current]

theorem projected_failure_iff {n : Nat} {cfg : Config n} (r : Run cfg) (t : Nat) (p : Proc n) :
    r.tournament.event t = .fail p ↔ r.event t = .fail p := by
  have step := r.valid t
  have link := (reachable_projection (r.reachable t)).1
  cases hc : r.command t with
  | stutter => simp [Run.tournament, Algorithm2.Run.event, Run.event, hc, projectCommand, label, Algorithm2.label]
  | restart q => simp [Run.tournament, Algorithm2.Run.event, Run.event, hc, projectCommand, label, Algorithm2.label]
  | run q =>
    cases hp : (r.state t q).pc <;>
      simp [Run.tournament, Algorithm2.Run.event, Run.event, hc, projectCommand, hp, label, Algorithm2.label]
    all_goals cases ht : (r.state t q).tournamentPC <;> simp [project, ht]
  | fail q =>
    rw [hc] at step
    have live : (r.state t q).pc ≠ .down := by intro hp; simp [next, hp] at step
    have inner : (r.state t q).tournamentPC ≠ .down := by
      have l := link q
      cases hp : (r.state t q).pc <;> simp_all [Linked]
    simp [Run.tournament, Algorithm2.Run.event, Run.event, hc, projectCommand, inner, label, Algorithm2.label]

theorem enqueue_next_complete {n : Nat} {cfg : Config n} {s t : State n} {p : Proc n}
    {c : Command n} (step : next cfg s c = some t) (event : label s c = .enqueue p) :
    (t p).pc = .complete := by
  cases c with
  | run q =>
    cases hp : (s q).pc <;> simp only [label, hp] at event
    all_goals try contradiction
    simp only [Label.enqueue.injEq] at event
    subst q
    simp only [next, ordinary, hp, Option.map_some, Option.some.injEq] at step
    rw [← step]; simp
  | fail | restart | stutter => simp [label] at event

theorem complete_eventually_completes {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (pc : (r.state start p).pc = .complete) :
    ∃ t, start ≤ t ∧ (r.tournament.event t = .complete p ∨ r.tournament.event t = .fail p) := by
  obtain ⟨t, lo, act, same⟩ := first_scheduled_action r fair (p := p) (start := start) (by simp [pc, Protocol])
  refine ⟨t, lo, ?_⟩
  rcases act with act | act
  · left
    have inner : (r.state t p).tournamentPC = .cs := by
      have link := (reachable_projection (r.reachable t)).1 p
      simpa [Linked, same, pc] using link
    simp [Algorithm2.Run.event, Run.tournament, projectCommand, act, same, pc,
      Algorithm2.label, project, show (r.state start p).tournamentPC = .cs from by simpa [same] using inner]
  · right
    apply (projected_failure_iff r t p).2
    simp [Run.event, act, label]

/-- Inner critical completion is derived from admission and a scheduled local
completion instruction. Outer critical completion is absent. -/
theorem tournament_completion {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) : Algorithm2.CriticalCompletion r.tournament := by
  intro start p inner
  change (r.state start p).tournamentPC = .cs at inner
  have link := (reachable_projection (r.reachable start)).1 p
  have acq := reachable_acquisition (r.reachable start) p
  have casesPC : Admission (r.state start p).pc ∨ (r.state start p).pc = .complete := by
    cases hp : (r.state start p).pc <;> simp_all [Linked, AcquisitionLinked, Admission, Algorithm2.pendingPC]
  rcases casesPC with admission | complete
  · obtain ⟨t, lo, event, _⟩ := admission_first_outcome r fair admission
    rcases event with enqueue | fail
    · have pc := enqueue_next_complete (r.valid t) enqueue
      obtain ⟨u, bound, outcome⟩ := complete_eventually_completes r fair pc
      exact ⟨u, by omega, outcome⟩
    · exact ⟨t, lo, Or.inr ((projected_failure_iff r t p).2 fail)⟩
  · exact complete_eventually_completes r fair complete

/-- Completion and separately scheduled departure release the tournament role,
even if the outer client never completes its later critical section. -/
theorem tournament_eventually_inactive {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (inner : (r.tournament.state start p).pc = .cs) :
    ∃ t, start ≤ t ∧ Algorithm2.Inactive (r.tournament.state t) p :=
  Algorithm2.critical_eventually_inactive r.tournament (tournament_scheduling r fair)
    (tournament_completion r fair) inner

/-- Before the first enqueue this control region retains the outer occurrence. -/
def Doorway {n : Nat} : PC n → Prop
  | .request | .acquire | .capacity _ _ | .choose _ _ | .enqueue _ => True
  | _ => False

theorem doorway_next {n : Nat} {cfg : Config n} {s t : State n} {p : Proc n}
    {c : Command n} (h : Doorway (s p).pc) (step : next cfg s c = some t)
    (ne : label s c ≠ .enqueue p) (nf : label s c ≠ .fail p) : Doorway (t p).pc := by
  by_cases act : Acts c p
  · rcases act with rfl | rfl
    · cases hp : (s p).pc <;> simp only [Doorway, hp] at h
      case request | acquire =>
        simp only [next, ordinary, hp, tournamentInstruction] at step
        cases ho : Algorithm2.ordinary cfg.tournament p (project s) with
        | none => simp [ho] at step
        | some l =>
          simp only [ho, Option.map_some, Option.some.injEq] at step
          subst t; simp only [setLocal_self]; split <;> trivial
      all_goals try (rename_i rest m; cases rest)
      all_goals simp only [next, ordinary, hp] at step
      all_goals try split at step
      all_goals simp only [Option.map_some, Option.some.injEq] at step
      all_goals subst t; simp_all [Doorway, label]
    · exact (nf rfl).elim
  · have live : (s p).pc ≠ .down := by intro hp; simp [Doorway, hp] at h
    simpa [next_live_unchanged step live act] using h

theorem doorway_inner_cs_admission {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) {p : Proc n} (doorway : Doorway (s p).pc)
    (inner : (s p).tournamentPC = .cs) : Admission (s p).pc := by
  have link := (reachable_projection reach).1 p
  have acq := reachable_acquisition reach p
  cases hp : (s p).pc <;>
    simp_all [Linked, AcquisitionLinked, Doorway, Admission, Algorithm2.pendingPC]

/-- The request preparation instruction creates a real pending tournament
request, including the singleton's separate local entry instruction. -/
theorem request_next_pending {n : Nat} {cfg : Config n} {s t : State n} {p : Proc n}
    (link : Linked (s p)) (pc : (s p).pc = .request)
    (step : next cfg s (.run p) = some t) : Algorithm2.Pending (project t) p := by
  have inner : (s p).tournamentPC = .idle := by
    have h : (s p).tournamentPC = .idle ∧ (s p).value.tournament = Algorithm2.dead := by simpa [Linked, pc] using link
    exact h.1
  simp only [next, ordinary, pc, tournamentInstruction, Algorithm2.ordinary, project, inner] at step
  split at step
  all_goals simp only [Option.map_some, Option.some.injEq] at step
  all_goals subst t; simp [Algorithm2.Pending, Algorithm2.pendingPC, Algorithm2.scan, project]

theorem doorway_eventually_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (doorway : Doorway (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ AdmissionOutcome r p finish := by
  classical
  by_contra no
  have none : ∀ t, start ≤ t → ¬ AdmissionOutcome r p t := by
    simpa only [not_exists, not_and] using no
  have stays : ∀ t, start ≤ t → Doorway (r.state t p).pc := by
    intro t lo
    induction t, lo using Nat.le_induction with
    | base => exact doorway
    | succ t lo ih =>
      exact doorway_next ih (r.valid t)
        (fun e => none t lo (Or.inl e)) (fun e => none t lo (Or.inr e))
  have noAdmission : ∀ t, start ≤ t → ¬ Admission (r.state t p).pc := by
    intro t lo h
    obtain ⟨u, bound, outcome⟩ := admission_eventually_outcome r fair h
    exact none u (by omega) outcome
  have pending : ∃ t, start ≤ t ∧ Algorithm2.Pending (r.tournament.state t) p := by
    have casesPC : (r.state start p).pc = .request ∨ (r.state start p).pc = .acquire := by
      have noA := noAdmission start le_rfl
      cases hp : (r.state start p).pc <;> simp_all [Doorway, Admission]
    rcases casesPC with request | acquire
    · obtain ⟨t, lo, act, same⟩ := first_scheduled_action r fair
        (p := p) (start := start) (by simp [request, Protocol])
      rcases act with act | act
      · refine ⟨t + 1, by omega, ?_⟩
        exact request_next_pending ((reachable_projection (r.reachable t)).1 p)
          (by rw [same]; exact request) (by simpa [act] using r.valid t)
      · exact (none t lo (Or.inr (by simp [Run.event, label, act]))).elim
    · exact ⟨start, le_rfl, reachable_acquisition (r.reachable start) p acquire⟩
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
    exact noAdmission (u + 1) (by omega)
      (doorway_inner_cs_admission (r.reachable (u + 1)) (stays (u + 1) (by omega)) cs)
  · exact none u (by omega) (Or.inr ((projected_failure_iff r u p).1 failure))

/-- The least own enqueue/failure retains every preceding outer doorway
control, preventing a restarted replacement request from supplying service. -/
theorem doorway_first_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (doorway : Doorway (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ AdmissionOutcome r p finish ∧
      ∀ t, start ≤ t → t < finish →
        Doorway (r.state t p).pc ∧ ¬ AdmissionOutcome r p t := by
  classical
  have ex := doorway_eventually_outcome r fair doorway
  obtain ⟨lo, event⟩ := Nat.find_spec ex
  have before : ∀ t, start ≤ t → t < Nat.find ex → ¬ AdmissionOutcome r p t := by
    intro t lo hi event
    have := Nat.find_min' ex ⟨lo, event⟩
    omega
  refine ⟨Nat.find ex, lo, event, ?_⟩
  intro t st tf
  refine ⟨?_, before t st tf⟩
  induction t, st using Nat.le_induction with
  | base => exact doorway
  | succ t st ih =>
    exact doorway_next (ih (by omega)) (r.valid t)
      (fun e => before t st (by omega) (Or.inl e))
      (fun e => before t st (by omega) (Or.inr e))

theorem doorway_surviving_enqueues {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (doorway : Doorway (r.state start p).pc)
    (survives : ∀ t, start ≤ t → r.event t ≠ .fail p) :
    ∃ finish, start ≤ finish ∧ r.event finish = .enqueue p ∧
      ∀ t, start ≤ t → t < finish →
        Doorway (r.state t p).pc ∧ ¬ AdmissionOutcome r p t := by
  obtain ⟨t, lo, event, before⟩ := doorway_first_outcome r fair doorway
  exact ⟨t, lo, event.resolve_right (survives t lo), before⟩

theorem doorway_no_replacement {n : Nat} (s : State n) (c : Command n) (p : Proc n)
    (doorway : Doorway (s p).pc) : label s c ≠ .request p ∧ label s c ≠ .entry p := by
  cases c with
  | run q =>
    by_cases eq : q = p
    · subst q
      cases hp : (s p).pc <;> simp_all [Doorway, label]
    · cases hp : (s q).pc <;> simp [label, hp, eq]
  | fail | restart | stutter => simp [label]

end EconomicalSolutions.Algorithm5

#print axioms EconomicalSolutions.Algorithm5.reachable_acquisition
#print axioms EconomicalSolutions.Algorithm5.Run.tournament
#print axioms EconomicalSolutions.Algorithm5.tournament_scheduling
#print axioms EconomicalSolutions.Algorithm5.tournament_completion
#print axioms EconomicalSolutions.Algorithm5.tournament_eventually_inactive
#print axioms EconomicalSolutions.Algorithm5.doorway_first_outcome
#print axioms EconomicalSolutions.Algorithm5.doorway_surviving_enqueues
#print axioms EconomicalSolutions.Algorithm5.doorway_no_replacement
