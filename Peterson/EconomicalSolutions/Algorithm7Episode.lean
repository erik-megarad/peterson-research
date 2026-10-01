import Peterson.EconomicalSolutions.Algorithm7CreditHistory

/-! Recover the original level-three exposure from a later eligibility or
permission control. These finite histories supply actual third writes to the
reviewed clock/list bridge; they do not assert full mutual exclusion. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm7
namespace EpisodeHistory
open CreditHistory

/-- The same request, from level-three publication through delayed release. -/
def Active : PC n → Prop
  | .attempt .three _ _ | .tickWrite .three _ _ | .pairDone .three
  | .attempt .eligible _ _ | .tickWrite .eligible _ _ | .pairDone .eligible
  | .eligible _ | .publish | .enter | .cs | .release => True
  | _ => False

/-- Controls reached only after both original level-three counters completed. -/
def Ready : PC n → Prop
  | .attempt .eligible _ _ | .tickWrite .eligible _ _ | .pairDone .eligible
  | .eligible _ | .publish | .enter | .cs | .release => True
  | _ => False

theorem ready_active {pc : PC n} (ready : Ready pc) : Active pc := by
  cases pc <;> simp_all [Ready, Active]
  case attempt phase _ _ | tickWrite phase _ _ | pairDone phase =>
    cases phase <;> simp_all [Ready, Active]

theorem ready_not_three {pc : PC n} (ready : Ready pc) : ¬ ThreePhase pc := by
  cases pc <;> simp_all [Ready, ThreePhase]
  case attempt phase _ _ | tickWrite phase _ _ | pairDone phase =>
    cases phase <;> simp_all [Ready, ThreePhase]

theorem active_exposed {l : Local n} (coherent : Coherent l) (active : Active l.pc) :
    exposed l.value = true := by
  cases pc : l.pc <;> simp only [pc, Active] at active
  case' attempt phase clock cp => cases phase
  case' tickWrite phase clock pending => cases phase
  case' pairDone phase => cases phase
  all_goals try contradiction
  all_goals simp only [Coherent, pc, phaseLevel] at coherent
  all_goals try (rw [coherent]; rfl)
  all_goals first
    | (obtain ⟨b0, b1, value⟩ := coherent; rw [value]; rfl)
    | (obtain ⟨⟨b0, b1, value⟩, _⟩ := coherent; rw [value]; rfl)

theorem ordinary_active {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {out : Local n} (step : ordinary cfg s p = some out)
    (after : Active out.pc) : Active (s p).pc ∨ Publication s (.run p) p := by
  cases pc : (s p).pc
  case' join clock first cp => cases cp
  case' attempt phase clock cp => cases phase
  case' tickWrite phase clock pending => cases phase
  case' pairDone phase => cases phase
  case' build rest => cases rest
  case' delete rest => cases rest
  case' add rest => cases rest
  case' eligible rest => cases rest
  all_goals try (left; simp [pc, Active]; done)
  case' attempt.one => cases cp
  case' attempt.maintain => cases cp
  all_goals simp only [ordinary, pc] at step
  all_goals try contradiction
  all_goals try (obtain ⟨result, _, rfl⟩ := Option.map_eq_some_iff.mp step)
  all_goals repeat (split at step)
  all_goals try contradiction
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try (simp_all [Active, afterAttempt, Publication]; done)
  all_goals try (cases clock <;> simp_all [Active, afterAttempt]; done)
  all_goals simp only [bind, Option.bind_eq_some_iff] at step
  all_goals obtain ⟨result, _, step⟩ := step
  all_goals split at step
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at step
  all_goals subst out
  all_goals contradiction

theorem next_active {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    {p : Proc n} (step : next cfg s c = some t) (after : Active (t p).pc) :
    Active (s p).pc ∨ Publication s c p := by
  cases c with
  | stutter => have eq := Option.some.inj step; exact Or.inl (by simpa [← eq] using after)
  | run actor =>
    obtain ⟨out, instruction, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor; exact ordinary_active instruction (by simpa using after)
    · exact Or.inl (by simpa [eq] using after)
  | request actor | complete actor | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp_all [Active, reset])
      | exact Or.inl (by simpa [eq] using after)

/-- Backward history chooses a publication whose entire suffix remains in the
same active band. A reset/replacement cannot be hidden inside that suffix. -/
theorem original_publication_history {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish b : Nat} {p : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (active : Active (trace b p).pc) :
    ∃ a, a < b ∧ Publication (trace a) (commands a) p ∧
      ∀ u, a < u → u ≤ b → Active (trace u p).pc := by
  induction b with
  | zero => simp [valid.1, initial, reset, Active] at active
  | succ b ih =>
    rcases next_active (valid.2 b (by omega)) active with before | publication
    · obtain ⟨a, ab, pub, kept⟩ := ih (by omega) before
      refine ⟨a, by omega, pub, ?_⟩
      intro u au ub
      by_cases last : u = b + 1
      · simpa [last] using active
      · exact kept u au (by omega)
    · refine ⟨b, by omega, publication, ?_⟩
      intro u bu ub
      have eq : u = b + 1 := by omega
      simpa [eq] using active

theorem active_no_failure {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {p : Proc n} (step : next cfg s c = some t)
    (after : Active (t p).pc) : c ≠ .fail p := by
  intro eq
  subst c
  simp only [next] at step
  split at step
  · contradiction
  · simp only [Option.some.injEq] at step
    subst t
    simp [reset, Active] at after

/-- Publication-to-endpoint identity and exposure, including cs permission,
actual critical execution and delayed release. All fields are consequences of
one initialized execution; there is no fairness or no-failure premise. -/
def Episode {n : Nat} (trace : Nat → State n) (commands : Nat → Command n)
    (p : Proc n) (a b : Nat) : Prop :=
  a < b ∧ Publication (trace a) (commands a) p ∧
  (∀ u, a < u → u ≤ b → Active (trace u p).pc) ∧
  (∀ u, a < u → u < b → commands u ≠ .fail p) ∧
  (∀ u, a < u → u ≤ b → exposed (trace u p).value = true)

theorem original_episode {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish b : Nat} {p : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (active : Active (trace b p).pc) : ∃ a, Episode trace commands p a b := by
  obtain ⟨a, ab, pub, kept⟩ := original_publication_history valid bf active
  refine ⟨a, ab, pub, kept, ?_, ?_⟩
  · intro u au ub
    exact active_no_failure (valid.2 u (by omega)) (kept (u + 1) (by omega) (by omega))
  · intro u au ub
    exact active_exposed (reachable_coherent valid (by omega) p) (kept u au ub)

/-- The first exit of the original exposure must be the real pair-completion
instruction. Its whole prefix is still in the original three-count phase. -/
theorem completed_exposure_history {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish a b : Nat} {p : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (episode : Episode trace commands p a b) (ready : Ready (trace b p).pc) :
    ∃ d, a < d ∧ d < b ∧ commands d = .run p ∧
      (trace d p).pc = .pairDone .three ∧
      3 ≤ (trace d p).count0 ∧ 3 ≤ (trace d p).count1 ∧
      (∀ u, a < u → u ≤ d → ThreePhase (trace u p).pc) := by
  have initial : ThreePhase (trace (a + 1) p).pc := by
    have start := (publication_starts episode.2.1 (valid.2 a (by have := episode.1; omega))).1
    simp [start, ThreePhase]
  have bad : ¬ ∀ i, i ≤ b - (a + 1) → ThreePhase (trace (a + 1 + i) p).pc := by
    intro all
    have last := all (b - (a + 1)) (le_refl _)
    have eq : a + 1 + (b - (a + 1)) = b := by have := episode.1; omega
    rw [eq] at last
    exact ready_not_three ready last
  obtain ⟨i, hi, phases, post⟩ := first_exit_prefix
    (P := fun r => ThreePhase (trace r p).pc) (start := a + 1) initial bad
  have departure := next_exposure_exit (phases i (le_refl _)) post
    (valid.2 (a + 1 + i) (by have := episode.1; omega))
  rcases departure with failure | ⟨command, pc, count0, count1, _⟩
  · exact (episode.2.2.2.1 _ (by omega) (by have := episode.1; omega) failure).elim
  · refine ⟨a + 1 + i, by omega, by have := episode.1; omega,
      command, pc, count0, count1, ?_⟩
    intro u au ud
    have eq : a + 1 + (u - (a + 1)) = u := by omega
    simpa only [eq] using phases (u - (a + 1)) (by omega)

/-- A unit-increment tally reaches three only by an actual third event. -/
theorem third_event {event : Nat → Bool} {start len : Nat}
    (three : 3 ≤ tally event start len) :
    ∃ i, i < len ∧ tally event start i = 2 ∧ event (start + i) = true := by
  induction len with
  | zero => simp [tally] at three
  | succ len ih =>
    by_cases earlier : 3 ≤ tally event start len
    · obtain ⟨i, il, count, event⟩ := ih earlier
      exact ⟨i, by omega, count, event⟩
    · refine ⟨len, by omega, ?_, ?_⟩
      all_goals simp only [tally] at three
      all_goals split at three <;> omega

theorem exposure_write_event {n : Nat} {s : State n} {c : Command n}
    {p : Proc n} {clock : Bool} (event : writeEvent s c p .three clock = true) :
    c = .run p ∧ ∃ pending, (s p).pc = .tickWrite .three clock pending := by
  simp only [writeEvent, Bool.and_eq_true, beq_iff_eq] at event
  obtain ⟨cmd, event⟩ := event
  refine ⟨cmd, ?_⟩
  cases pc : (s p).pc <;> simp only [pc, writePC] at event
  all_goals try contradiction
  simp only [Bool.and_eq_true, beq_iff_eq] at event
  rcases event with ⟨rfl, rfl⟩
  exact ⟨_, rfl⟩

/-- A later ready control supplies, for each clock, its literal third write
since this original publication, with no completed/replaced exposure spliced in. -/
theorem original_third_writes {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish a b : Nat} {p : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (episode : Episode trace commands p a b) (ready : Ready (trace b p).pc) :
    ∀ clock, ∃ len pending, a + 1 + len < b ∧
      (trace (a + 1 + len) p).pc = .tickWrite .three clock pending ∧
      commands (a + 1 + len) = .run p ∧
      tally (writes trace commands p .three clock) (a + 1) len = 2 ∧
      (∀ u, a < u → u ≤ a + 1 + len → ThreePhase (trace u p).pc) := by
  obtain ⟨d, ad, db, _, _, count0, count1, phases⟩ :=
    completed_exposure_history valid bf episode ready
  intro clock
  have eq : a + 1 + (d - (a + 1)) = d := by omega
  have count := history_counter (clock := clock) valid episode.2.1
    (by omega) (len := d - (a + 1)) (by omega)
    (by intro i hi; apply phases <;> omega)
  rw [eq] at count
  have three : 3 ≤ tally (writes trace commands p .three clock) (a + 1) (d - (a + 1)) := by
    rw [← count]
    cases clock <;> assumption
  obtain ⟨len, ld, two, event⟩ := third_event three
  obtain ⟨command, pending, pc⟩ := exposure_write_event event
  exact ⟨len, pending, by omega, pc, command, two,
    by intro u au ub; exact phases u au (by omega)⟩

/-- This supplies the previous unit's publication and third-event premises
from the actual later control. Only the peer's departure alternatives remain;
the original exposing owner's failure alternative is impossible. -/
theorem ready_observation_or_departure {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish b : Nat}
    {owner peer : Proc n} (valid : ValidPrefix cfg trace commands finish)
    (bf : b ≤ finish) (other : owner ≠ peer) (ready : Ready (trace b owner).pc) :
    ∃ a, Episode trace commands owner a b ∧
      ((¬ Maintaining (trace (a + 1) peer).pc) ∨
        (∃ r, a < r ∧ r < b ∧ MaintenanceExit (trace r) (commands r) (trace (r + 1)) peer) ∨
        (∃ clock, Observation trace commands owner peer clock (a + 1) b)) := by
  obtain ⟨a, episode⟩ := original_episode valid bf (ready_active ready)
  obtain ⟨clock, below⟩ := reversed_pair_order (Ne.symm other)
  obtain ⟨len, pending, bound, pc, command, two, _⟩ :=
    original_third_writes valid bf episode ready clock
  have observed := (actual_third_observation_or_departure valid episode.2.1
    (by have := episode.1; omega) (by omega) other below pc command two).2
  refine ⟨a, episode, ?_⟩
  rcases observed with absent | failure | departure | observation
  · exact Or.inl absent
  · obtain ⟨r, lo, hi, failure⟩ := failure
    exact (episode.2.2.2.1 r (by omega) (by omega) failure).elim
  · obtain ⟨r, lo, hi, departure⟩ := departure
    exact Or.inr (Or.inl ⟨r, by omega, by omega, departure⟩)
  · right; right
    obtain ⟨r, u, v, lo, ru, ub, rest⟩ := observation
    exact ⟨clock, r, u, v, lo, ru, by omega, rest⟩

/-- With retained peer credit at the endpoint (in particular permission,
entry or actual critical control), the addition branch forces the peer's own
failure. The remaining alternatives are initial nonmaintenance or an actual
failure/empty-list departure, not an assumed observation oracle. -/
theorem ready_passed_peer_requires_departure {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish b : Nat}
    {owner peer : Proc n} (valid : ValidPrefix cfg trace commands finish)
    (bf : b ≤ finish) (other : owner ≠ peer) (ready : Ready (trace b owner).pc)
    (passed : PassedPeer owner (trace b peer).pc) :
    ∃ a, Episode trace commands owner a b ∧
      ((¬ Maintaining (trace (a + 1) peer).pc) ∨
        ∃ r, a < r ∧ r < b ∧ MaintenanceExit (trace r) (commands r) (trace (r + 1)) peer) := by
  classical
  obtain ⟨a, episode, absent | departure | observation⟩ :=
    ready_observation_or_departure valid bf other ready
  · exact ⟨a, episode, Or.inl absent⟩
  · exact ⟨a, episode, Or.inr departure⟩
  · obtain ⟨clock, r, u, v, lo, ru, ub, _, _, rv, vu, addition, _⟩ := observation
    refine ⟨a, episode, Or.inr ?_⟩
    by_cases failure : ∃ w, v < w ∧ w < b ∧ commands w = .fail peer
    · obtain ⟨w, vw, wb, failure⟩ := failure
      exact ⟨w, by omega, wb, Or.inl failure⟩
    · have barrier := (addition_excludes_permission valid (by omega) bf addition
        (by intro w vw wb; exact episode.2.2.2.2 w (by omega) (by omega))
        (by intro w vw wb fail; exact failure ⟨w, vw, wb, fail⟩)).2
      exact (barrier passed).elim

/-- Throughout an original lower-identifier episode, its level-three or cs
register blocks every larger identifier's new eligibility sample. -/
theorem active_blocks {n : Nat} {l : Local n} {p q : Proc n}
    (coherent : Coherent l) (active : Active l.pc) (priority : q.val < p.val) :
    Blocks p q l.value := by
  cases pc : l.pc <;> simp only [pc, Active] at active
  case' attempt phase clock cp => cases phase
  case' tickWrite phase clock pending => cases phase
  case' pairDone phase => cases phase
  all_goals try contradiction
  all_goals simp only [Coherent, pc, phaseLevel] at coherent
  all_goals try (rw [coherent]; trivial)
  all_goals first
    | (obtain ⟨b0, b1, value⟩ := coherent; simpa [value, Blocks] using priority)
    | (obtain ⟨⟨b0, b1, value⟩, _⟩ := coherent; simpa [value, Blocks] using priority)

/-- A larger identifier retaining eligibility credit while a smaller original
request is exposed must already have that credit immediately after the smaller
request's level-three publication. This explicitly allows stale earlier reads
and arbitrarily delayed permission writes. -/
theorem priority_requires_prior_credit {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish a b : Nat}
    {p q : Proc n} (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (episode : Episode trace commands q a b) (priority : q.val < p.val)
    (passed : PassedPeer q (trace b p).pc) : PassedPeer q (trace (a + 1) p).pc := by
  classical
  by_contra absent
  have other : q ≠ p := by intro eq; subst p; omega
  have barrier := stable_blocker_exclusion valid (by have := episode.1; omega) bf other absent
    (by
      intro r lo hi
      exact active_blocks (reachable_coherent valid (by omega) q)
        (episode.2.2.1 r (by omega) (by omega)) priority)
  exact barrier passed

end EpisodeHistory
end EconomicalSolutions.Algorithm7

#print axioms EconomicalSolutions.Algorithm7.EpisodeHistory.original_episode

#print axioms EconomicalSolutions.Algorithm7.EpisodeHistory.completed_exposure_history

#print axioms EconomicalSolutions.Algorithm7.EpisodeHistory.original_third_writes

#print axioms EconomicalSolutions.Algorithm7.EpisodeHistory.ready_observation_or_departure

#print axioms EconomicalSolutions.Algorithm7.EpisodeHistory.ready_passed_peer_requires_departure

#print axioms EconomicalSolutions.Algorithm7.EpisodeHistory.priority_requires_prior_credit
