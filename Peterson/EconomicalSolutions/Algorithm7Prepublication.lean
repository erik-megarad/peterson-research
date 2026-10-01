import Peterson.EconomicalSolutions.Algorithm7BuildHistory

/-! Full Algorithm 7 safety via actual prepublication clock histories.
The credit interval includes list building and delayed prefix operations; original
request histories and physical priority close mutual exclusion. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm7
namespace PrepublicationHistory
open CreditHistory EpisodeHistory BuildHistory

/-- After level-one exposure and before level-three publication. Both delayed
prefix changes and the empty-list departure are included. Coherence excludes
unreachable malformed prefix controls; the predicate itself is control-only. -/
def BeforeThree : PC n → Prop
  | .build _ | .prefixRead _ | .prefixWrite _ => True
  | pc => Maintaining pc

theorem built_before_or_active {pc : PC n} {q : Proc n}
    (built : BuiltPeer q pc) : BeforeThree pc ∨ Active pc := by
  cases pc <;> simp_all [BuiltPeer, BeforeThree, Maintaining, Active]
  case attempt phase _ _ | tickWrite phase _ _ | pairDone phase =>
    cases phase <;> simp_all [BuiltPeer, BeforeThree, Maintaining, Active]

/-- Reachable prefix controls have live bits even while the visible level is one. -/
theorem before_live {l : Local n} (coherent : Coherent l) (band : BeforeThree l.pc)
    (clock : Bool) : ∃ b, bit l.value clock = some b := by
  by_cases maintain : Maintaining l.pc
  · obtain ⟨b0, b1, value⟩ := maintenance_level coherent maintain
    exact ⟨if clock then b1 else b0, by simp [value, bit]⟩
  cases pc : l.pc <;> simp only [pc, BeforeThree] at band
  all_goals try (simp_all [Maintaining]; done)
  all_goals simp only [Coherent, pc] at coherent
  case build rest =>
    obtain ⟨b0, b1, value⟩ := coherent
    exact ⟨if clock then b1 else b0, by simp [value, bit]⟩
  all_goals obtain ⟨old, _, b0, b1, value⟩ := coherent
  all_goals exact ⟨if clock then b1 else b0, by simp [value, bit]⟩

/-- Builds and cached prefix writes preserve both actual bits. Thus broadening
the control interval grants no fictitious credit for delayed publication. -/
theorem ordinary_bit_change {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {clock : Bool} {out : Local n}
    (coherent : Coherent (s p)) (band : BeforeThree (s p).pc)
    (step : ordinary cfg s p = some out)
    (changed : bit out.value clock ≠ bit (s p).value clock) :
    ∃ pending, (s p).pc = .tickWrite .maintain clock pending := by
  by_cases maintain : Maintaining (s p).pc
  · exact ordinary_maintenance_bit_change coherent maintain step changed
  cases pc : (s p).pc <;> simp only [pc, BeforeThree] at band
  case' prefixRead level => cases level
  case' prefixWrite pending => cases pending
  case' prefixWrite.live level b0 b1 => cases level
  all_goals try (simp_all [Maintaining]; done)
  case' build rest => cases rest
  all_goals simp only [ordinary, pc] at step
  all_goals repeat (split at step)
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at step
  all_goals subst out
  all_goals try (exact (changed rfl).elim)
  all_goals simp only [Coherent, pc] at coherent
  all_goals obtain ⟨old, new, c0, c1, _, value, pending⟩ := coherent
  all_goals cases pending
  all_goals exact (changed (by simp [value, bit])).elim

theorem next_bit_change {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {p : Proc n} {clock : Bool}
    (coherent : Coherent (s p)) (before : BeforeThree (s p).pc)
    (after : BeforeThree (t p).pc) (step : next cfg s c = some t)
    (changed : bit (t p).value clock ≠ bit (s p).value clock) :
    MaintenanceWrite s c p clock := by
  cases c with
  | stutter => have eq := Option.some.inj step; exact (changed (by rw [← eq])).elim
  | run actor =>
    obtain ⟨out, instruction, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor
      exact ⟨rfl, ordinary_bit_change coherent before instruction (by simpa using changed)⟩
    · exact (changed (by simp [eq])).elim
  | request actor | complete actor | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp_all [reset, BeforeThree, Maintaining])
      | exact (changed (by simp [eq])).elim

theorem next_credit {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {owner peer : Proc n} {clock lower : Bool} {count k : Nat}
    (coherent : ∀ p, Coherent (s p)) (other : owner ≠ peer)
    (phase : ThreePhase (s owner).pc) (phaseAfter : ThreePhase (t owner).pc)
    (maintain : BeforeThree (s peer).pc) (maintainAfter : BeforeThree (t peer).pc)
    (below : (position peer clock).val < (position owner clock).val)
    (peerValue : bit (s peer).value clock = some lower)
    (credit : LocalCredit (s owner) peer clock count k lower)
    (cap : k + (if writeEvent s c peer .maintain clock then 1 else 0) ≤ 1)
    (step : next cfg s c = some t) :
    ∃ newLower, bit (t peer).value clock = some newLower ∧
      LocalCredit (t owner) peer clock
        (count + if writeEvent s c owner .three clock then 1 else 0)
        (k + if writeEvent s c peer .maintain clock then 1 else 0) newLower := by
  by_cases ownRun : c = .run owner
  · subst c
    have unchanged : t peer = s peer := by
      obtain ⟨out, _, rfl⟩ := Option.map_eq_some_iff.mp step
      simp [Ne.symm other]
    refine ⟨lower, by rw [unchanged]; exact peerValue, ?_⟩
    simpa [writeEvent, other] using owner_step (coherent owner) phase below peerValue credit step
  · have unchanged := not_run_keeps (Or.inl phase) (Or.inl phaseAfter) ownRun step
    have ownerEvent : writeEvent s c owner .three clock = false := by simp [writeEvent, ownRun]
    simp only [ownerEvent, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    by_cases event : writeEvent s c peer .maintain clock = true
    · have write := maintenance_event.mp event
      have zero : k = 0 := by simp only [event, ↓reduceIte] at cap; omega
      subst k
      obtain ⟨cmd, pending, pc⟩ := write
      subst c
      refine ⟨!lower, ?_⟩
      simpa [event] using maintenance_write_grants_credit other (coherent peer)
        peerValue ⟨rfl, pending, pc⟩ credit step
    · have sameBit : bit (t peer).value clock = bit (s peer).value clock := by
        by_contra changed
        exact event (maintenance_event.mpr
          (next_bit_change (coherent peer) maintain maintainAfter step changed))
      refine ⟨lower, sameBit.trans peerValue, ?_⟩
      simpa [event, unchanged] using credit

/-- Actual selected-clock write tallies remain valid while the peer builds,
publishes level two, maintains, or delays its level-three publication. -/
theorem history_credit {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a len : Nat} {owner peer : Proc n} {clock : Bool}
    (valid : ValidPrefix cfg trace commands finish)
    (publication : Publication (trace a) (commands a) owner) (af : a < finish)
    (bound : a + 1 + len ≤ finish) (other : owner ≠ peer)
    (below : (position peer clock).val < (position owner clock).val)
    (phase : ∀ i, i ≤ len → ThreePhase (trace (a + 1 + i) owner).pc)
    (maintain : ∀ i, i ≤ len → BeforeThree (trace (a + 1 + i) peer).pc)
    (cap : tally (writes trace commands peer .maintain clock) (a + 1) len ≤ 1) :
    ∃ lower, bit (trace (a + 1 + len) peer).value clock = some lower ∧
      LocalCredit (trace (a + 1 + len) owner) peer clock
        (tally (writes trace commands owner .three clock) (a + 1) len)
        (tally (writes trace commands peer .maintain clock) (a + 1) len) lower := by
  induction len with
  | zero =>
    obtain ⟨pc, _, _, value⟩ := publication_starts publication (valid.2 a af)
    obtain ⟨lower, peerVal⟩ := before_live
      (reachable_coherent valid (by omega) peer) (maintain 0 (by omega)) clock
    refine ⟨lower, by simpa using peerVal, ?_⟩
    simpa [tally] using initial_credit (peer := peer) (clock := clock) value pc
  | succ len ih =>
    obtain ⟨lower, peerValue, credit⟩ := ih (by omega)
      (fun i hi => phase i (by omega)) (fun i hi => maintain i (by omega))
      (le_trans (tally_le_succ _ _ _) cap)
    have result := next_credit (reachable_coherent valid (by omega)) other
      (phase len (by omega)) (phase (len + 1) (by omega))
      (maintain len (by omega)) (maintain (len + 1) (by omega)) below
      peerValue credit cap (valid.2 (a + 1 + len) (by omega))
    simpa only [tally, writes, Nat.add_assoc] using result

/-- A third exposing write still requires two real maintenance writes even
when the peer was initially building or already delaying its next publication. -/
theorem third_requires_two {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a len : Nat} {owner peer : Proc n}
    {clock : Bool} {pending : Value}
    (valid : ValidPrefix cfg trace commands finish)
    (publication : Publication (trace a) (commands a) owner) (af : a < finish)
    (bound : a + 1 + len ≤ finish) (other : owner ≠ peer)
    (below : (position peer clock).val < (position owner clock).val)
    (phase : ∀ i, i ≤ len → ThreePhase (trace (a + 1 + i) owner).pc)
    (maintain : ∀ i, i ≤ len → BeforeThree (trace (a + 1 + i) peer).pc)
    (pc : (trace (a + 1 + len) owner).pc = .tickWrite .three clock pending)
    (third : counter (trace (a + 1 + len) owner) clock = 2) :
    2 ≤ tally (writes trace commands peer .maintain clock) (a + 1) len := by
  by_contra few
  have cap : tally (writes trace commands peer .maintain clock) (a + 1) len ≤ 1 := by omega
  obtain ⟨lower, _, credit⟩ := history_credit valid publication af bound other below phase maintain cap
  have exactCount := history_counter (clock := clock) valid publication af bound phase
  rw [← exactCount, third] at credit
  have needs := pending_third_write_needs_two_credits
    (reachable_coherent valid bound owner) pc credit
  omega

/-- Monotone control rank inside the prepublication interval. -/
def rank : PC n → Nat
  | .prefixRead .three | .prefixWrite (.live .three _ _) => 2
  | .delete _ | .add _ | .attempt .maintain _ _
  | .tickWrite .maintain _ _ | .pairDone .maintain => 1
  | _ => 0

theorem ordinary_rank {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {out : Local n}
    (before : BeforeThree (s p).pc)
    (after : BeforeThree out.pc) (step : ordinary cfg s p = some out) :
    rank (s p).pc ≤ rank out.pc := by
  cases pc : (s p).pc
  case' attempt phase clock cp => cases phase
  case' tickWrite phase clock pending => cases phase
  case' pairDone phase => cases phase
  all_goals try (simp_all [BeforeThree, Maintaining]; done)
  case' prefixRead level => cases level
  case' prefixWrite pending => cases pending
  case' prefixWrite.live level b0 b1 => cases level
  all_goals try (simp [pc, rank, Maintaining]; done)
  case' attempt.maintain => cases cp
  case' delete rest => cases rest
  case' add rest => cases rest
  all_goals simp only [ordinary, pc] at step
  all_goals try (obtain ⟨result, _, rfl⟩ := Option.map_eq_some_iff.mp step)
  all_goals repeat (split at step)
  all_goals try contradiction
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try (simp_all [BeforeThree, Maintaining, rank, afterAttempt]; done)
  all_goals try (cases clock <;> simp_all [BeforeThree, Maintaining, rank, afterAttempt]; done)
  all_goals simp only [bind, Option.bind_eq_some_iff] at step
  all_goals obtain ⟨result, _, step⟩ := step
  all_goals split at step
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at step
  all_goals subst out
  all_goals cases clock <;> simp_all [BeforeThree, Maintaining, rank, afterAttempt]

theorem next_rank {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {p : Proc n} (before : BeforeThree (s p).pc)
    (after : BeforeThree (t p).pc) (step : next cfg s c = some t) :
    rank (s p).pc ≤ rank (t p).pc := by
  cases c with
  | stutter => have eq := Option.some.inj step; rw [← eq]
  | run actor =>
    obtain ⟨out, instruction, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor; simpa using (ordinary_rank (out := out) before (by simpa using after) instruction)
    · simp [eq]
  | request actor | complete actor | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp_all [reset, BeforeThree, Maintaining])
      | simp [eq]

theorem rank_mono {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b : Nat} {p : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (ab : a ≤ b) (bf : b ≤ finish)
    (band : ∀ u, a ≤ u → u ≤ b → BeforeThree (trace u p).pc) :
    rank (trace a p).pc ≤ rank (trace b p).pc := by
  induction b, ab using Nat.le_induction with
  | base => exact le_refl _
  | succ b ab ih =>
    exact le_trans (ih (by omega) (by intro u lo hi; exact band u lo (by omega)))
      (next_rank (band b ab (by omega)) (band (b + 1) (by omega) (by omega))
        (valid.2 b (by omega)))

theorem rank_one_iff {pc : PC n} : rank pc = 1 ↔ Maintaining pc := by
  cases pc <;> simp [rank, Maintaining]
  case attempt phase _ _ | tickWrite phase _ _ | pairDone phase =>
    cases phase <;> simp [rank, Maintaining]
  case prefixRead level => cases level <;> simp [rank, Maintaining]
  case prefixWrite pending =>
    cases pending <;> try simp [rank, Maintaining]
    case live level _ _ => cases level <;> simp [rank, Maintaining]

/-- Two maintenance controls within one broad interval have uninterrupted
maintenance between them: no hidden departure, rebuild or replacement fits. -/
theorem maintenance_between {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b : Nat} {p : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (band : ∀ u, a ≤ u → u ≤ b → BeforeThree (trace u p).pc)
    (first : Maintaining (trace a p).pc) (last : Maintaining (trace b p).pc) :
    ∀ u, a ≤ u → u ≤ b → Maintaining (trace u p).pc := by
  intro u au ub
  have left := rank_mono valid au (by omega) (by intro v lo hi; exact band v lo (by omega))
  have right := rank_mono valid ub bf (by intro v lo hi; exact band v (by omega) hi)
  rw [rank_one_iff.mpr first] at left
  rw [rank_one_iff.mpr last] at right
  exact rank_one_iff.mp (by omega)

/-- The actual third write forces a stage-7 addition, even if the peer
starts as a builder or delays either prefix write. -/
theorem third_forces_addition {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a len : Nat} {owner peer : Proc n}
    {clock : Bool} {pending : Value}
    (valid : ValidPrefix cfg trace commands finish)
    (publication : Publication (trace a) (commands a) owner) (af : a < finish)
    (bound : a + 1 + len ≤ finish) (other : owner ≠ peer)
    (below : (position peer clock).val < (position owner clock).val)
    (phase : ∀ i, i ≤ len → ThreePhase (trace (a + 1 + i) owner).pc)
    (maintain : ∀ i, i ≤ len → BeforeThree (trace (a + 1 + i) peer).pc)
    (pc : (trace (a + 1 + len) owner).pc = .tickWrite .three clock pending)
    (third : counter (trace (a + 1 + len) owner) clock = 2) :
    ∃ r u v, a + 1 ≤ r ∧ r < u ∧ u < a + 1 + len ∧
      MaintenanceWrite (trace r) (commands r) peer clock ∧
      MaintenanceWrite (trace u) (commands u) peer clock ∧
      r < v ∧ v < u ∧ AdditionRead (trace v) (commands v) peer owner ∧
      WaitingFor owner (trace u peer) ∧ ¬ PassedPeer owner (trace u peer).pc := by
  have two := third_requires_two valid publication af bound other below phase maintain pc third
  obtain ⟨r, u, lo, ru, hi, first, second⟩ := tally_two two
  have firstWrite := maintenance_event.mp first
  have secondWrite := maintenance_event.mp second
  have maintenance : ∀ v, r ≤ v → v ≤ u → Maintaining (trace v peer).pc := by
    apply maintenance_between valid (by omega)
    · intro v rv vu
      have h := maintain (v - (a + 1)) (by omega)
      simpa only [Nat.add_sub_of_le (by omega : a + 1 ≤ v)] using h
    · obtain ⟨_, pending, pc⟩ := firstWrite; simp [pc, Maintaining]
    · obtain ⟨_, pending, pc⟩ := secondWrite; simp [pc, Maintaining]
  obtain ⟨v, rv, vu, read, waiting⟩ := two_maintenance_writes_force_waiting valid ru (by omega)
    other firstWrite secondWrite
    (by intro v rv vu; exact maintenance v (by omega) (by omega))
    (by
      intro v rv vu
      have h := three_level (reachable_coherent valid (by omega) owner)
        (phase (v - (a + 1)) (by omega))
      simpa only [Nat.add_sub_of_le (by omega : a + 1 ≤ v), AtLevel] using h)
  exact ⟨r, u, v, lo, ru, hi, firstWrite, secondWrite, rv, vu, read, waiting⟩

/-- At two active requests the peer's original build of the exposer is already
complete before this publication. This supplies the broad credit interval
without a serialization assumption for overlapping builders. -/
theorem peer_built_after_publication {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish a b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (episode : Episode trace commands p a b) (other : p ≠ q)
    (active : Active (trace b q).pc) :
    ∀ u, a < u → u ≤ b → BuiltPeer p (trace u q).pc := by
  obtain ⟨d, db, departure, _, exposed, _⟩ := original_departure_episode valid bf
    (episode.2.2.1 b episode.1 (le_refl _))
  have da : d ≤ a := by
    by_contra bad
    have ownerActive := episode.2.2.1 d (by omega) (by omega)
    simp [departure.2.1, Active] at ownerActive
  obtain ⟨r, rd, _, _, built⟩ := active_build_precedes_exposure valid bf other active
    (a := d + 1) (by intro u lo hi; exact exposed u (by omega) (by omega))
  intro u au ub
  exact built u (by omega) ub

/-- If the exposer is ready earlier and the peer later retains permission
credit, the peer was already active before that earlier ready state. Completed
builds, initial nonmaintenance and delayed empty-list departures cannot evade
the actual clock/list barrier. -/
theorem ready_passed_peer_was_active {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish a c b : Nat}
    {owner peer : Proc n} (valid : ValidPrefix cfg trace commands finish)
    (bf : b ≤ finish) (ac : a < c) (cb : c ≤ b) (other : owner ≠ peer)
    (episode : Episode trace commands owner a b)
    (ready : Ready (trace c owner).pc) (passed : PassedPeer owner (trace b peer).pc) :
    ∃ u, a < u ∧ u < c ∧ Active (trace u peer).pc := by
  classical
  have built := peer_built_after_publication valid bf episode other (passed_active passed)
  have short : Episode trace commands owner a c :=
    ⟨ac, episode.2.1,
      (by intro u au uc; exact episode.2.2.1 u au (by omega)),
      (by intro u au uc; exact episode.2.2.2.1 u au (by omega)),
      (by intro u au uc; exact episode.2.2.2.2 u au (by omega))⟩
  obtain ⟨clock, below⟩ := reversed_pair_order (Ne.symm other)
  obtain ⟨len, pending, beforeReady, pc, _, count, phases⟩ :=
    original_third_writes valid (by omega) short ready clock
  by_contra absent
  have band : ∀ i, i ≤ len → BeforeThree (trace (a + 1 + i) peer).pc := by
    intro i hi
    rcases built_before_or_active (built (a + 1 + i) (by omega) (by omega)) with band | active
    · exact band
    · exact (absent ⟨a + 1 + i, by omega, by omega, active⟩).elim
  have exactCount := history_counter (clock := clock) valid episode.2.1
    (by omega) (by omega : a + 1 + len ≤ finish)
    (by intro i hi; exact phases _ (by omega) (by omega))
  have third : counter (trace (a + 1 + len) owner) clock = 2 := exactCount.trans count
  obtain ⟨r, u, v, lo, ru, hi, _, _, rv, vu, addition, _⟩ :=
    third_forces_addition valid episode.2.1 (by omega) (by omega) other below
      (by intro i hi; exact phases _ (by omega) (by omega)) band pc third
  have barrier := (addition_excludes_permission valid (by omega) bf addition
    (by intro w vw wb; exact episode.2.2.2.2 w (by omega) (by omega))
    (by
      intro w vw wb
      exact built_no_failure (q := owner) (valid.2 w (by omega))
        (built (w + 1) (by omega) (by omega)))).2
  exact barrier passed

/-- An active request can leave its band only by clearing its original build
history. This distinguishes an earlier request from the original endpoint. -/
theorem ordinary_active_kept {n : Nat} {cfg : Config n} {s : State n}
    {p q : Proc n} {out : Local n} (before : Active (s p).pc)
    (after : BuiltPeer q out.pc) (step : ordinary cfg s p = some out) : Active out.pc := by
  cases pc : (s p).pc
  case' attempt phase clock cp => cases phase
  case' tickWrite phase clock pending => cases phase
  case' pairDone phase => cases phase
  all_goals try (simp_all [Active]; done)
  case' attempt.three => cases cp
  case' attempt.eligible => cases cp
  case' eligible rest => cases rest
  all_goals simp only [ordinary, pc] at step
  all_goals try contradiction
  all_goals try (obtain ⟨result, _, rfl⟩ := Option.map_eq_some_iff.mp step)
  all_goals repeat (split at step)
  all_goals try contradiction
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try (simp_all [Active, BuiltPeer, reset, afterAttempt]; done)
  all_goals try (cases clock <;> simp_all [Active, afterAttempt]; done)
  all_goals try (split_ifs <;> simp_all [Active])
  all_goals simp only [bind, Option.bind_eq_some_iff] at step
  all_goals obtain ⟨result, _, step⟩ := step
  all_goals split at step
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at step
  all_goals subst out
  all_goals simp_all [Active]

theorem next_active_kept {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {p q : Proc n} (before : Active (s p).pc)
    (after : BuiltPeer q (t p).pc) (step : next cfg s c = some t) : Active (t p).pc := by
  cases c with
  | stutter => have eq := Option.some.inj step; simpa [← eq] using before
  | run actor =>
    obtain ⟨out, instruction, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor; simpa using (ordinary_active_kept (out := out) before (by simpa using after) instruction)
    · simpa [eq] using before
  | request actor | complete actor | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp_all [reset, Active, BuiltPeer])
      | simpa [eq] using before

theorem active_kept {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (ab : a ≤ b) (bf : b ≤ finish)
    (active : Active (trace a p).pc)
    (built : ∀ u, a < u → u ≤ b → BuiltPeer q (trace u p).pc) :
    Active (trace b p).pc := by
  induction b, ab using Nat.le_induction with
  | base => exact active
  | succ b ab ih =>
    exact next_active_kept
      (ih (by omega) (by intro u lo hi; exact built u lo (by omega)))
      (built (b + 1) (by omega) (by omega)) (valid.2 b (by omega))

theorem passed_ready {pc : PC n} {p : Proc n} (passed : PassedPeer p pc) : Ready pc := by
  cases pc <;> simp_all [PassedPeer, Ready]

/-- Priority and the original histories exclude two retained eligibility
credits. Arbitrarily stale successful reads and delayed cs writes are included. -/
theorem priority_excludes_mutual_credit {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (priority : p.val < q.val)
    (pPassed : PassedPeer q (trace b p).pc) (qPassed : PassedPeer p (trace b q).pc) : False := by
  have other : q ≠ p := by intro eq; subst q; omega
  obtain ⟨ap, pEpisode⟩ := original_episode valid bf (passed_active pPassed)
  obtain ⟨aq, qEpisode⟩ := original_episode valid bf (passed_active qPassed)
  have retained := priority_retains_credit valid bf pEpisode priority qPassed
  have aqBefore : aq < ap + 1 := by
    by_contra bad
    have active := passed_active (retained aq (by omega) (by have := qEpisode.1; omega))
    obtain ⟨_, b0, b1, pc⟩ := qEpisode.2.1
    simp [pc, Active] at active
  have earlierReady := passed_ready
    (retained (ap + 1) (by omega) (by have := pEpisode.1; omega))
  obtain ⟨u, aqu, uap, active⟩ := ready_passed_peer_was_active valid bf aqBefore
    (by have := pEpisode.1; omega) other qEpisode earlierReady pPassed
  have built := peer_built_after_publication valid bf qEpisode other (passed_active pPassed)
  have impossible := active_kept valid (by omega : u ≤ ap)
    (by have := pEpisode.1; omega : ap ≤ finish) active
    (by intro v uv vap; exact built v (by omega) (by have := pEpisode.1; omega))
  obtain ⟨_, b0, b1, pc⟩ := pEpisode.2.1
  simp [pc, Active] at impossible

/-- Full finite-prefix mutual exclusion for the frozen Algorithm 7 interpreter,
for every population and every configured peer enumeration, allowing failures,
restarts, repeated requests and arbitrary instruction delays. -/
theorem mutual_exclusion {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish b : Nat}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish) :
    ∀ p q, (trace b p).pc = .cs → (trace b q).pc = .cs → p = q := by
  intro p q pCS qCS
  by_contra other
  have pPassed : PassedPeer q (trace b p).pc := by simp [pCS, PassedPeer]
  have qPassed : PassedPeer p (trace b q).pc := by simp [qCS, PassedPeer]
  have ne : p.val ≠ q.val := fun eq => other (Fin.ext eq)
  rcases lt_or_gt_of_ne ne with priority | priority
  · exact priority_excludes_mutual_credit valid bf priority pPassed qPassed
  · exact priority_excludes_mutual_credit valid bf priority qPassed pPassed

/-- Every finite state of every initialized infinite run satisfies safety;
no scheduling, ticking or critical-completion premise is needed. -/
theorem run_mutual_exclusion {n : Nat} {cfg : Config n} (run : Run cfg) (b : Nat) :
    ∀ p q, (run.state b p).pc = .cs → (run.state b q).pc = .cs → p = q := by
  exact mutual_exclusion ⟨run.initialized, fun t _ => run.valid t⟩ (le_refl b)

end PrepublicationHistory
end EconomicalSolutions.Algorithm7

#print axioms EconomicalSolutions.Algorithm7.PrepublicationHistory.next_bit_change
#print axioms EconomicalSolutions.Algorithm7.PrepublicationHistory.history_credit
#print axioms EconomicalSolutions.Algorithm7.PrepublicationHistory.third_requires_two
#print axioms EconomicalSolutions.Algorithm7.PrepublicationHistory.maintenance_between
#print axioms EconomicalSolutions.Algorithm7.PrepublicationHistory.third_forces_addition
#print axioms EconomicalSolutions.Algorithm7.PrepublicationHistory.peer_built_after_publication
#print axioms EconomicalSolutions.Algorithm7.PrepublicationHistory.ready_passed_peer_was_active

#print axioms EconomicalSolutions.Algorithm7.PrepublicationHistory.active_kept
#print axioms EconomicalSolutions.Algorithm7.PrepublicationHistory.priority_excludes_mutual_credit
#print axioms EconomicalSolutions.Algorithm7.PrepublicationHistory.mutual_exclusion
#print axioms EconomicalSolutions.Algorithm7.PrepublicationHistory.run_mutual_exclusion
