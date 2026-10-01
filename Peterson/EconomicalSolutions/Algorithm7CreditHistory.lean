import Peterson.EconomicalSolutions.Algorithm7ClockCredit

/-! Actual finite-prefix clock counts during one level-three exposure.
The interval ends explicitly when either participant leaves its required phase. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm7
namespace CreditHistory

def ThreePhase : PC n → Prop
  | .attempt .three _ _ | .tickWrite .three _ _ | .pairDone .three => True
  | _ => False

def writePC (phase : Phase) (clock : Bool) : PC n → Bool
  | .tickWrite active selected _ => active == phase && selected == clock
  | _ => false

def writeEvent {n : Nat} (s : State n) (c : Command n) (p : Proc n)
    (phase : Phase) (clock : Bool) : Bool :=
  c == .run p && writePC phase clock (s p).pc

def tally (event : Nat → Bool) (start : Nat) : Nat → Nat
  | 0 => 0
  | len + 1 => tally event start len + if event (start + len) then 1 else 0

def counter (l : Local n) (clock : Bool) : Nat := if clock then l.count1 else l.count0

def Publication {n : Nat} (s : State n) (c : Command n) (p : Proc n) : Prop :=
  c = .run p ∧ ∃ b0 b1, (s p).pc = .prefixWrite (.live .three b0 b1)

theorem publication_starts {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {p : Proc n} (publication : Publication s c p)
    (step : next cfg s c = some t) :
    (t p).pc = .attempt .three false .attempt ∧ counter (t p) false = 0 ∧
      counter (t p) true = 0 ∧ AtLevel (t p).value .three := by
  obtain ⟨rfl, b0, b1, pc⟩ := publication
  simp only [next, ordinary, pc, Option.map_some, Option.some.injEq] at step
  subst t
  simp [counter, AtLevel]

theorem three_level {n : Nat} {l : Local n} (coherent : Coherent l)
    (phase : ThreePhase l.pc) : AtLevel l.value .three := by
  cases pc : l.pc <;> simp only [pc, ThreePhase] at phase
  case' attempt active clock cp => cases active
  case' tickWrite active clock pending => cases active
  case' pairDone active => cases active
  all_goals simp_all [Coherent, phaseLevel]

theorem maintenance_level {n : Nat} {l : Local n} (coherent : Coherent l)
    (phase : Maintaining l.pc) : AtLevel l.value .two := by
  cases pc : l.pc <;> simp only [pc, Maintaining] at phase
  case' attempt active clock cp => cases active
  case' tickWrite active clock pending => cases active
  case' pairDone active => cases active
  all_goals simp_all [Coherent, phaseLevel]

theorem initial_credit {n : Nat} {l : Local n} {peer : Proc n} {clock lower : Bool}
    (value : AtLevel l.value .three) (pc : l.pc = .attempt .three false .attempt) :
    LocalCredit l peer clock 0 0 lower := by
  obtain ⟨b0, b1, value⟩ := value
  refine ⟨if clock then b1 else b0, by simp [value, bit], by omega, by omega, ?_⟩
  cases clock <;> simp [creditPC, pc, ClockCredit.ScanCredit]

theorem transfer_idle {n : Nat} {l out : Local n} {peer : Proc n}
    {clock lower : Bool} {count k : Nat}
    (credit : LocalCredit l peer clock count k lower)
    (value : bit out.value clock = bit l.value clock)
    (pc : creditPC out clock = .attempt) : LocalCredit out peer clock count k lower := by
  obtain ⟨upper, own, bound, top, _⟩ := credit
  exact ⟨upper, value.trans own, bound, top, by simp [pc, ClockCredit.ScanCredit]⟩

theorem owner_step {n : Nat} {cfg : Config n} {s t : State n}
    {owner peer : Proc n} {clock lower : Bool} {count k : Nat}
    (coherent : Coherent (s owner))
    (phase : ThreePhase (s owner).pc)
    (below : (position peer clock).val < (position owner clock).val)
    (peerValue : bit (s peer).value clock = some lower)
    (credit : LocalCredit (s owner) peer clock count k lower)
    (step : next cfg s (.run owner) = some t) :
    LocalCredit (t owner) peer clock
      (count + if writePC .three clock (s owner).pc then 1 else 0) k lower := by
  cases pc : (s owner).pc <;> simp only [pc, ThreePhase] at phase
  case' attempt active selected cp => cases active
  case' tickWrite active selected pending => cases active
  case' pairDone active => cases active
  all_goals try contradiction
  case attempt.three =>
    simp only [writePC, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    by_cases eq : selected = clock
    · subst selected
      exact attempt_preserves_credit coherent below peerValue pc credit step
    · cases cp
      case tickRead =>
        obtain ⟨b0, b1, own⟩ := three_level coherent (by simp [pc, ThreePhase])
        simp only [next, ordinary, pc, clockInstruction_tickRead own, bind, Option.bind,
          Option.map_some, Option.some.injEq] at step
        subst t
        apply transfer_idle credit
        · simp
        · simp [creditPC, eq]
      all_goals simp only [next, ordinary, pc, Option.map_map] at step
      all_goals obtain ⟨out, _, rfl⟩ := Option.map_eq_some_iff.mp step
      all_goals apply transfer_idle credit
      all_goals try (simp; done)
      all_goals simp only [Function.comp_apply, setLocal_self, creditPC]
      all_goals split_ifs <;> cases selected <;> cases clock <;> simp_all [creditPC, afterAttempt]
  case tickWrite.three =>
    by_cases eq : selected = clock
    · subst selected
      simpa [writePC] using tick_write_consumes_credit coherent pc credit step
    · have info := coherent_tick_write coherent pc step
      simp only [writePC, beq_self_eq_true, Bool.true_and, beq_iff_eq, eq,
        ↓reduceIte, Nat.add_zero]
      apply transfer_idle credit
      · have flip : (!selected) = clock := by cases selected <;> cases clock <;> simp_all
        simpa [flip] using info.choose_spec.choose_spec.2.2.2.1
      · have control := info.choose_spec.choose_spec.2.2.2.2
        cases selected <;> cases clock <;> simp_all [creditPC, afterAttempt]
  case pairDone.three =>
    simp only [writePC, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    simp only [next, ordinary, pc, Option.map_some, Option.some.injEq] at step
    subst t
    apply transfer_idle credit
    · simp
    simp only [setLocal_self]
    split_ifs <;> cases clock <;> simp [creditPC]

theorem maintenance_event {n : Nat} {s : State n} {c : Command n}
    {p : Proc n} {clock : Bool} :
    writeEvent s c p .maintain clock = true ↔ MaintenanceWrite s c p clock := by
  simp only [writeEvent, Bool.and_eq_true, beq_iff_eq, MaintenanceWrite]
  constructor
  · rintro ⟨cmd, h⟩
    cases pc : (s p).pc <;> simp only [pc, writePC] at h
    all_goals try contradiction
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨cmd, _, rfl⟩
  · rintro ⟨cmd, pending, pc⟩
    simp [cmd, pc, writePC]

/-- Outside its own ordinary command, a process in either live band can only
change by leaving that band (failure, followed possibly by a fresh request). -/
theorem not_run_keeps {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    {p : Proc n} (before : ThreePhase (s p).pc ∨ Maintaining (s p).pc)
    (after : ThreePhase (t p).pc ∨ Maintaining (t p).pc)
    (notRun : c ≠ .run p) (step : next cfg s c = some t) : t p = s p := by
  cases c with
  | stutter => have eq := Option.some.inj step; rw [← eq]
  | run actor =>
    obtain ⟨out, _, rfl⟩ := Option.map_eq_some_iff.mp step
    have ne : p ≠ actor := by intro eq; subst actor; exact notRun rfl
    simp [ne]
  | request actor | complete actor | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp_all [ThreePhase, Maintaining, reset])
      | simp [eq]

theorem next_credit {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {owner peer : Proc n} {clock lower : Bool} {count k : Nat}
    (coherent : ∀ p, Coherent (s p)) (other : owner ≠ peer)
    (phase : ThreePhase (s owner).pc) (phaseAfter : ThreePhase (t owner).pc)
    (maintain : Maintaining (s peer).pc) (maintainAfter : Maintaining (t peer).pc)
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
          (next_maintenance_bit_change (coherent peer) maintain maintainAfter step changed))
      refine ⟨lower, sameBit.trans peerValue, ?_⟩
      simpa [event, unchanged] using credit

/-- The interpreter's private exposure counter has precisely the same increment
as the actual selected whole-register event. -/
theorem ordinary_counter {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {clock : Bool} {out : Local n}
    (phase : ThreePhase (s p).pc) (step : ordinary cfg s p = some out) :
    counter out clock = counter (s p) clock + if writePC .three clock (s p).pc then 1 else 0 := by
  cases pc : (s p).pc <;> simp only [pc, ThreePhase] at phase
  case' attempt active selected cp => cases active
  case' tickWrite active selected pending => cases active
  case' pairDone active => cases active
  all_goals try contradiction
  case' attempt.three => cases cp
  all_goals simp only [ordinary, pc] at step
  all_goals try (obtain ⟨out, _, rfl⟩ := Option.map_eq_some_iff.mp step)
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try (simp [counter, writePC]; done)
  all_goals try (cases clock <;> cases selected <;> simp [counter, writePC]; done)
  all_goals simp only [bind, Option.bind_eq_some_iff] at step
  all_goals obtain ⟨result, _, step⟩ := step
  all_goals split at step
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at step
  all_goals subst out
  all_goals simp [counter, writePC]

theorem next_counter {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    {p : Proc n} {clock : Bool} (phase : ThreePhase (s p).pc)
    (after : ThreePhase (t p).pc) (step : next cfg s c = some t) :
    counter (t p) clock = counter (s p) clock + if writeEvent s c p .three clock then 1 else 0 := by
  by_cases own : c = .run p
  · subst c
    obtain ⟨out, instruction, rfl⟩ := Option.map_eq_some_iff.mp step
    simpa [writeEvent] using ordinary_counter (clock := clock) phase instruction
  · have same := not_run_keeps (Or.inl phase) (Or.inl after) own step
    simp [same, writeEvent, own]

def writes {n : Nat} (trace : Nat → State n) (commands : Nat → Command n)
    (p : Proc n) (phase : Phase) (clock : Bool) : Nat → Bool :=
  fun r => writeEvent (trace r) (commands r) p phase clock

theorem tally_le_succ (event : Nat → Bool) (start len : Nat) :
    tally event start len ≤ tally event start (len + 1) := by
  simp only [tally]; split <;> omega

/-- Both credit arguments are the counts of real interpreter write events
since the successor of the original publication. No arbitrary counter remains. -/
theorem history_credit {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a len : Nat} {owner peer : Proc n} {clock : Bool}
    (valid : ValidPrefix cfg trace commands finish)
    (publication : Publication (trace a) (commands a) owner) (af : a < finish)
    (bound : a + 1 + len ≤ finish) (other : owner ≠ peer)
    (below : (position peer clock).val < (position owner clock).val)
    (phase : ∀ i, i ≤ len → ThreePhase (trace (a + 1 + i) owner).pc)
    (maintain : ∀ i, i ≤ len → Maintaining (trace (a + 1 + i) peer).pc)
    (cap : tally (writes trace commands peer .maintain clock) (a + 1) len ≤ 1) :
    ∃ lower, bit (trace (a + 1 + len) peer).value clock = some lower ∧
      LocalCredit (trace (a + 1 + len) owner) peer clock
        (tally (writes trace commands owner .three clock) (a + 1) len)
        (tally (writes trace commands peer .maintain clock) (a + 1) len) lower := by
  induction len with
  | zero =>
    obtain ⟨pc, _, _, value⟩ := publication_starts publication (valid.2 a af)
    obtain ⟨b0, b1, peerVal⟩ := maintenance_level
      (reachable_coherent valid (by omega) peer) (maintain 0 (by omega))
    refine ⟨if clock then b1 else b0, ?_, ?_⟩
    · simpa [Nat.add_zero, bit] using congrArg (fun v => bit v clock) peerVal
    · simpa [tally] using initial_credit (peer := peer) (clock := clock) value pc
  | succ len ih =>
    obtain ⟨lower, peerValue, credit⟩ := ih (by omega)
      (fun i hi => phase i (by omega)) (fun i hi => maintain i (by omega))
      (le_trans (tally_le_succ _ _ _) cap)
    have result := next_credit (reachable_coherent valid (by omega)) other
      (phase len (by omega)) (phase (len + 1) (by omega))
      (maintain len (by omega)) (maintain (len + 1) (by omega)) below
      peerValue credit cap (valid.2 (a + 1 + len) (by omega))
    simpa only [tally, writes, Nat.add_assoc] using result

/-- The private success count equals the event tally, starting at this
publication rather than at an earlier request or level-one exposure. -/
theorem history_counter {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a len : Nat} {owner : Proc n} {clock : Bool}
    (valid : ValidPrefix cfg trace commands finish)
    (publication : Publication (trace a) (commands a) owner) (af : a < finish)
    (bound : a + 1 + len ≤ finish)
    (phase : ∀ i, i ≤ len → ThreePhase (trace (a + 1 + i) owner).pc) :
    counter (trace (a + 1 + len) owner) clock =
      tally (writes trace commands owner .three clock) (a + 1) len := by
  induction len with
  | zero =>
    have start := publication_starts publication (valid.2 a af)
    cases clock
    · simpa [tally] using start.2.1
    · simpa [tally] using start.2.2.1
  | succ len ih =>
    have count := next_counter (clock := clock) (phase len (by omega))
      (phase (len + 1) (by omega)) (valid.2 (a + 1 + len) (by omega))
    rw [ih (by omega) (fun i hi => phase i (by omega))] at count
    simpa only [tally, writes, Nat.add_assoc] using count

/-- Immediately before the original exposure's third selected write, two
actual peer maintenance writes already occurred, provided both bands persisted. -/
theorem third_requires_two {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a len : Nat} {owner peer : Proc n}
    {clock : Bool} {pending : Value}
    (valid : ValidPrefix cfg trace commands finish)
    (publication : Publication (trace a) (commands a) owner) (af : a < finish)
    (bound : a + 1 + len ≤ finish) (other : owner ≠ peer)
    (below : (position peer clock).val < (position owner clock).val)
    (phase : ∀ i, i ≤ len → ThreePhase (trace (a + 1 + i) owner).pc)
    (maintain : ∀ i, i ≤ len → Maintaining (trace (a + 1 + i) peer).pc)
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

theorem tally_positive {event : Nat → Bool} {start len : Nat}
    (positive : 0 < tally event start len) :
    ∃ r, start ≤ r ∧ r < start + len ∧ event r = true := by
  induction len with
  | zero => simp [tally] at positive
  | succ len ih =>
    by_cases last : event (start + len) = true
    · exact ⟨start + len, by omega, by omega, last⟩
    · have previous : 0 < tally event start len := by simpa [tally, last] using positive
      obtain ⟨r, lo, hi, ev⟩ := ih previous
      exact ⟨r, lo, by omega, ev⟩

theorem tally_two {event : Nat → Bool} {start len : Nat}
    (two : 2 ≤ tally event start len) :
    ∃ r u, start ≤ r ∧ r < u ∧ u < start + len ∧ event r = true ∧ event u = true := by
  induction len with
  | zero => simp [tally] at two
  | succ len ih =>
    by_cases previous : 2 ≤ tally event start len
    · obtain ⟨r, u, lo, ru, hi, first, second⟩ := ih previous
      exact ⟨r, u, lo, ru, by omega, first, second⟩
    · have last : event (start + len) = true := by
        by_contra no
        simp only [tally, no, ↓reduceIte, Nat.add_zero] at two
        contradiction
      have positive : 0 < tally event start len := by simp only [tally, last, ↓reduceIte] at two; omega
      obtain ⟨r, lo, hi, ev⟩ := tally_positive positive
      exact ⟨r, start + len, lo, hi, by omega, ev, last⟩

/-- The continuous branch supplies two historical maintenance writes and the
actual stage-7 read between them, before the third exposing write executes. -/
theorem third_forces_addition {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a len : Nat} {owner peer : Proc n}
    {clock : Bool} {pending : Value}
    (valid : ValidPrefix cfg trace commands finish)
    (publication : Publication (trace a) (commands a) owner) (af : a < finish)
    (bound : a + 1 + len ≤ finish) (other : owner ≠ peer)
    (below : (position peer clock).val < (position owner clock).val)
    (phase : ∀ i, i ≤ len → ThreePhase (trace (a + 1 + i) owner).pc)
    (maintain : ∀ i, i ≤ len → Maintaining (trace (a + 1 + i) peer).pc)
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
  obtain ⟨v, rv, vu, read, waiting⟩ := two_maintenance_writes_force_waiting valid ru (by omega)
    other firstWrite secondWrite
    (by
      intro v rv vu
      have h := maintain (v - (a + 1)) (by omega)
      simpa only [Nat.add_sub_of_le (by omega : a + 1 ≤ v)] using h)
    (by
      intro v rv vu
      have h := three_level (reachable_coherent valid (by omega) owner)
        (phase (v - (a + 1)) (by omega))
      simpa only [Nat.add_sub_of_le (by omega : a + 1 ≤ v), AtLevel] using h)
  exact ⟨r, u, v, lo, ru, hi, firstWrite, secondWrite, rv, vu, read, waiting⟩

/-- The only ordinary exit from maintenance is the empty-list decision;
its successor still visibly has level two, before the delayed prefix write. -/
theorem ordinary_maintenance_exit {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {out : Local n} (before : Maintaining (s p).pc)
    (after : ¬ Maintaining out.pc) (step : ordinary cfg s p = some out) :
    (s p).pc = .pairDone .maintain ∧ (s p).behind = ∅ ∧ out.pc = .prefixRead .three := by
  cases pc : (s p).pc <;> simp only [pc, Maintaining] at before
  case' attempt active selected cp => cases active
  case' tickWrite active selected pending => cases active
  case' pairDone active => cases active
  all_goals try contradiction
  case' attempt.maintain => cases cp
  case' delete rest => cases rest
  case' add rest => cases rest
  all_goals simp only [ordinary, pc] at step
  all_goals try (obtain ⟨result, _, rfl⟩ := Option.map_eq_some_iff.mp step)
  all_goals repeat (split at step)
  all_goals try contradiction
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try (simp_all [Maintaining, afterAttempt]; done)
  all_goals try (cases selected <;> simp_all [Maintaining, ThreePhase, afterAttempt]; done)
  all_goals simp only [bind, Option.bind_eq_some_iff] at step
  all_goals obtain ⟨result, _, step⟩ := step
  all_goals split at step
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at step
  all_goals subst out
  all_goals simp_all [Maintaining, afterAttempt]

/-- An exposure exit is failure or the real both-counters-complete test. -/
theorem ordinary_exposure_exit {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {out : Local n} (before : ThreePhase (s p).pc)
    (after : ¬ ThreePhase out.pc) (step : ordinary cfg s p = some out) :
    (s p).pc = .pairDone .three ∧ 3 ≤ (s p).count0 ∧ 3 ≤ (s p).count1 ∧
      out.pc = .attempt .eligible false .attempt := by
  cases pc : (s p).pc <;> simp only [pc, ThreePhase] at before
  case' attempt active selected cp => cases active
  case' tickWrite active selected pending => cases active
  case' pairDone active => cases active
  all_goals try contradiction
  case' attempt.three => cases cp
  all_goals simp only [ordinary, pc] at step
  all_goals try (obtain ⟨result, _, rfl⟩ := Option.map_eq_some_iff.mp step)
  all_goals repeat (split at step)
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try (simp_all [ThreePhase, afterAttempt]; done)
  all_goals try (cases selected <;> simp_all [Maintaining, ThreePhase, afterAttempt]; done)
  all_goals simp only [bind, Option.bind_eq_some_iff] at step
  all_goals obtain ⟨result, _, step⟩ := step
  all_goals split at step
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at step
  all_goals subst out
  all_goals simp_all [ThreePhase, afterAttempt]

def MaintenanceExit {n : Nat} (s : State n) (c : Command n) (t : State n) (p : Proc n) : Prop :=
  c = .fail p ∨ (c = .run p ∧ (s p).pc = .pairDone .maintain ∧
    (s p).behind = ∅ ∧ (t p).pc = .prefixRead .three)

def ExposureExit {n : Nat} (s : State n) (c : Command n) (t : State n) (p : Proc n) : Prop :=
  c = .fail p ∨ (c = .run p ∧ (s p).pc = .pairDone .three ∧
    3 ≤ (s p).count0 ∧ 3 ≤ (s p).count1 ∧ (t p).pc = .attempt .eligible false .attempt)

theorem next_maintenance_exit {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {p : Proc n} (before : Maintaining (s p).pc)
    (after : ¬ Maintaining (t p).pc) (step : next cfg s c = some t) :
    MaintenanceExit s c t p := by
  cases c with
  | stutter => have eq := Option.some.inj step; exact (after (by simpa [← eq] using before)).elim
  | run actor =>
    obtain ⟨out, instruction, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor
      exact Or.inr ⟨rfl, by simpa using ordinary_maintenance_exit before (by simpa using after) instruction⟩
    · exact (after (by simpa [eq] using before)).elim
  | request actor | complete actor | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp_all [Maintaining, MaintenanceExit])
      | exact (after (by simpa [eq] using before)).elim

theorem next_exposure_exit {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {p : Proc n} (before : ThreePhase (s p).pc)
    (after : ¬ ThreePhase (t p).pc) (step : next cfg s c = some t) :
    ExposureExit s c t p := by
  cases c with
  | stutter => have eq := Option.some.inj step; exact (after (by simpa [← eq] using before)).elim
  | run actor =>
    obtain ⟨out, instruction, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor
      exact Or.inr ⟨rfl, by simpa using ordinary_exposure_exit before (by simpa using after) instruction⟩
    · exact (after (by simpa [eq] using before)).elim
  | request actor | complete actor | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp_all [ThreePhase, ExposureExit])
      | exact (after (by simpa [eq] using before)).elim

theorem first_exit {P : Nat → Prop} {start len : Nat} (initial : P start)
    (bad : ¬ ∀ i, i ≤ len → P (start + i)) :
    ∃ i, i < len ∧ P (start + i) ∧ ¬ P (start + i + 1) := by
  classical
  induction len with
  | zero =>
    apply False.elim
    apply bad
    intro i hi
    have eq : i = 0 := by omega
    simpa [eq] using initial
  | succ len ih =>
    by_cases previous : ∀ i, i ≤ len → P (start + i)
    · refine ⟨len, by omega, previous len (le_refl _), ?_⟩
      intro last
      apply bad
      intro i hi
      by_cases eq : i = len + 1
      · simpa [eq, Nat.add_assoc] using last
      · exact previous i (by omega)
    · obtain ⟨i, hi, pre, post⟩ := ih previous
      exact ⟨i, by omega, pre, post⟩

/-- No continuous-maintenance hypothesis is hidden in the disjunction. A peer
already outside maintenance (including a tied builder or delayed prefix) is
separate from a witnessed later empty-list exit or failure. Exposure departure
likewise identifies actual failure or actual completion of both three-tick counts. -/
theorem third_observation_or_departure {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a len : Nat} {owner peer : Proc n}
    {clock : Bool} {pending : Value}
    (valid : ValidPrefix cfg trace commands finish)
    (publication : Publication (trace a) (commands a) owner) (af : a < finish)
    (bound : a + 1 + len ≤ finish) (other : owner ≠ peer)
    (below : (position peer clock).val < (position owner clock).val)
    (pc : (trace (a + 1 + len) owner).pc = .tickWrite .three clock pending)
    (third : counter (trace (a + 1 + len) owner) clock = 2) :
    (¬ Maintaining (trace (a + 1) peer).pc) ∨
    (∃ r, a + 1 ≤ r ∧ r < a + 1 + len ∧
      MaintenanceExit (trace r) (commands r) (trace (r + 1)) peer) ∨
    (∃ r, a + 1 ≤ r ∧ r < a + 1 + len ∧
      ExposureExit (trace r) (commands r) (trace (r + 1)) owner) ∨
    (∃ r u v, a + 1 ≤ r ∧ r < u ∧ u < a + 1 + len ∧
      MaintenanceWrite (trace r) (commands r) peer clock ∧
      MaintenanceWrite (trace u) (commands u) peer clock ∧
      r < v ∧ v < u ∧ AdditionRead (trace v) (commands v) peer owner ∧
      WaitingFor owner (trace u peer) ∧ ¬ PassedPeer owner (trace u peer).pc) := by
  classical
  by_cases start : Maintaining (trace (a + 1) peer).pc
  · right
    by_cases maintain : ∀ i, i ≤ len → Maintaining (trace (a + 1 + i) peer).pc
    · right
      by_cases phase : ∀ i, i ≤ len → ThreePhase (trace (a + 1 + i) owner).pc
      · exact Or.inr (third_forces_addition valid publication af bound other below phase maintain pc third)
      · left
        have initial : ThreePhase (trace (a + 1) owner).pc := by
          have init := (publication_starts publication (valid.2 a af)).1
          simp [init, ThreePhase]
        obtain ⟨i, hi, pre, post⟩ := first_exit (P := fun r => ThreePhase (trace r owner).pc) (start := a + 1) initial phase
        exact ⟨a + 1 + i, by omega, by omega,
          next_exposure_exit pre post (valid.2 _ (by omega))⟩
    · left
      obtain ⟨i, hi, pre, post⟩ := first_exit (P := fun r => Maintaining (trace r peer).pc) (start := a + 1) start maintain
      exact ⟨a + 1 + i, by omega, by omega,
        next_maintenance_exit pre post (valid.2 _ (by omega))⟩
  · exact Or.inl start

theorem tally_mono {event : Nat → Bool} {start i len : Nat} (bound : i ≤ len) :
    tally event start i ≤ tally event start len := by
  induction len, bound using Nat.le_induction with
  | base => exact le_refl _
  | succ len _ ih => exact le_trans ih (tally_le_succ _ _ _)

theorem first_exit_prefix {P : Nat → Prop} {start len : Nat} (initial : P start)
    (bad : ¬ ∀ i, i ≤ len → P (start + i)) :
    ∃ i, i < len ∧ (∀ j, j ≤ i → P (start + j)) ∧ ¬ P (start + i + 1) := by
  classical
  induction len with
  | zero =>
    apply False.elim
    apply bad
    intro i hi
    have eq : i = 0 := by omega
    simpa [eq] using initial
  | succ len ih =>
    by_cases previous : ∀ i, i ≤ len → P (start + i)
    · refine ⟨len, by omega, previous, ?_⟩
      intro last
      apply bad
      intro i hi
      by_cases eq : i = len + 1
      · simpa [eq, Nat.add_assoc] using last
      · exact previous i (by omega)
    · obtain ⟨i, hi, pre, post⟩ := ih previous
      exact ⟨i, by omega, pre, post⟩

/-- Two actual exposure writes so far cannot include a completed earlier
exposure. With no own failure, the original publication's phase persists. -/
theorem two_writes_same_exposure {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a len : Nat} {owner : Proc n} {clock : Bool}
    (valid : ValidPrefix cfg trace commands finish)
    (publication : Publication (trace a) (commands a) owner) (af : a < finish)
    (bound : a + 1 + len ≤ finish)
    (two : tally (writes trace commands owner .three clock) (a + 1) len = 2)
    (noFailure : ∀ r, a + 1 ≤ r → r < a + 1 + len → commands r ≠ .fail owner) :
    ∀ i, i ≤ len → ThreePhase (trace (a + 1 + i) owner).pc := by
  classical
  by_contra bad
  have initial : ThreePhase (trace (a + 1) owner).pc := by
    have init := (publication_starts publication (valid.2 a af)).1
    simp [init, ThreePhase]
  obtain ⟨i, hi, phases, post⟩ := first_exit_prefix
    (P := fun r => ThreePhase (trace r owner).pc) (start := a + 1) initial bad
  have departure := next_exposure_exit (phases i (le_refl _)) post (valid.2 _ (by omega))
  rcases departure with failure | ⟨_, _, complete0, complete1, _⟩
  · exact noFailure _ (by omega) (by omega) failure
  · have count := history_counter (clock := clock) valid publication af (by omega) phases
    have atLeast : 3 ≤ counter (trace (a + 1 + i) owner) clock := by
      cases clock <;> assumption
    have monotone := tally_mono (event := writes trace commands owner .three clock)
      (start := a + 1) (by omega : i ≤ len)
    omega

def Observation {n : Nat} (trace : Nat → State n) (commands : Nat → Command n)
    (owner peer : Proc n) (clock : Bool) (start finish : Nat) : Prop :=
  ∃ r u v, start ≤ r ∧ r < u ∧ u < finish ∧
    MaintenanceWrite (trace r) (commands r) peer clock ∧
    MaintenanceWrite (trace u) (commands u) peer clock ∧
    r < v ∧ v < u ∧ AdditionRead (trace v) (commands v) peer owner ∧
    WaitingFor owner (trace u peer) ∧ ¬ PassedPeer owner (trace u peer).pc

/-- A literal third successful selected-clock write after one actual original
publication. Every finite interpreter history is covered: peer not initially
maintaining, original-owner failure, maintenance departure, or an actual addition
barrier before the third write. The completion alternative is eliminated by the
actual event tally rather than by assuming the private count means this episode. -/
theorem actual_third_observation_or_departure {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish a len : Nat}
    {owner peer : Proc n} {clock : Bool} {pending : Value}
    (valid : ValidPrefix cfg trace commands finish)
    (publication : Publication (trace a) (commands a) owner) (af : a < finish)
    (bound : a + 1 + len < finish) (other : owner ≠ peer)
    (below : (position peer clock).val < (position owner clock).val)
    (pc : (trace (a + 1 + len) owner).pc = .tickWrite .three clock pending)
    (command : commands (a + 1 + len) = .run owner)
    (two : tally (writes trace commands owner .three clock) (a + 1) len = 2) :
    tally (writes trace commands owner .three clock) (a + 1) (len + 1) = 3 ∧
    ((¬ Maintaining (trace (a + 1) peer).pc) ∨
      (∃ r, a + 1 ≤ r ∧ r < a + 1 + len ∧ commands r = .fail owner) ∨
      (∃ r, a + 1 ≤ r ∧ r < a + 1 + len ∧
        MaintenanceExit (trace r) (commands r) (trace (r + 1)) peer) ∨
      Observation trace commands owner peer clock (a + 1) (a + 1 + len)) := by
  classical
  constructor
  · simp [tally, two, writes, writeEvent, command, pc, writePC]
  · by_cases maintainStart : Maintaining (trace (a + 1) peer).pc
    · right
      by_cases noFailure : ∀ r, a + 1 ≤ r → r < a + 1 + len → commands r ≠ .fail owner
      · right
        have phases := two_writes_same_exposure valid publication af (by omega) two noFailure
        by_cases maintain : ∀ i, i ≤ len → Maintaining (trace (a + 1 + i) peer).pc
        · right
          apply third_forces_addition valid publication af (by omega) other below phases maintain pc
          rw [history_counter valid publication af (by omega) phases]
          exact two
        · left
          obtain ⟨i, hi, pre, post⟩ := first_exit
            (P := fun r => Maintaining (trace r peer).pc) (start := a + 1) maintainStart maintain
          exact ⟨a + 1 + i, by omega, by omega,
            next_maintenance_exit pre post (valid.2 _ (by omega))⟩
      · left
        push Not at noFailure
        exact noFailure
    · exact Or.inl maintainStart

end CreditHistory
end EconomicalSolutions.Algorithm7

#print axioms EconomicalSolutions.Algorithm7.CreditHistory.publication_starts
#print axioms EconomicalSolutions.Algorithm7.CreditHistory.history_credit
#print axioms EconomicalSolutions.Algorithm7.CreditHistory.history_counter
#print axioms EconomicalSolutions.Algorithm7.CreditHistory.third_requires_two
#print axioms EconomicalSolutions.Algorithm7.CreditHistory.third_forces_addition
#print axioms EconomicalSolutions.Algorithm7.CreditHistory.next_maintenance_exit
#print axioms EconomicalSolutions.Algorithm7.CreditHistory.next_exposure_exit
#print axioms EconomicalSolutions.Algorithm7.CreditHistory.two_writes_same_exposure
#print axioms EconomicalSolutions.Algorithm7.CreditHistory.actual_third_observation_or_departure
