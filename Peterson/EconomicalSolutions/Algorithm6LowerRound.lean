import Peterson.EconomicalSolutions.Algorithm6Cohort

/-! Finite lower maintenance/attempt return under instruction-or-own-failure
scheduling. Returning to the list test does not imply a successful clock tick. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
namespace EconomicalSolutions.Algorithm6

/-- Work remaining in one clock invocation; `attempt` starts a fresh scan.
The join cases make the descent lemma total even for arbitrary cached controls. -/
def clockRoundRank (m : Nat) : Algorithm3.PC → Nat
  | .joinLower j => m + j + 2
  | .joinUpper j => j + 2
  | .joinWrite _ => 1
  | .attempt => 4 * m + 6
  | .tickLower j _ => 2 * m + 2 * j + 5
  | .lowerOwn j _ => 2 * m + 2 * j + 4
  | .tickUpper j => 2 * j + 4
  | .upperOwn j _ => 2 * j + 3
  | .tickRead => 2
  | .tickWrite _ => 1
  | _ => 0

private theorem lower_scan_rank (i m k : Nat) (b : Bool) :
    clockRoundRank m (Algorithm3.tickLower i m k b) < 2 * m + 2 * k + 4 := by
  unfold Algorithm3.tickLower
  split
  · simp [clockRoundRank]; omega
  · cases m with
    | zero => simp [clockRoundRank]
    | succ m => split <;> dsimp [clockRoundRank] <;> omega

private theorem upper_scan_rank (i m k : Nat) :
    clockRoundRank m (Algorithm3.tickUpper i k) < 2 * k + 3 := by
  unfold Algorithm3.tickUpper
  split <;> dsimp [clockRoundRank] <;> omega

/-- Every real clock instruction either returns or decreases finite work.
Samples may be stale, peers may move, and a return may be a refused guard. -/
theorem clock_round_step {m : Nat} {s : Algorithm3.State m} {i : Fin m}
    {out : Algorithm3.Local} (step : Algorithm3.ordinary s i = some out) :
    out.pc = .attempt ∨ clockRoundRank m out.pc < clockRoundRank m (s i).pc := by
  cases hp : (s i).pc
  case joinLower j | joinUpper j | joinWrite b =>
    have h := clock_join_step (by simp [hp, Joining]) step
    rcases h.1 with joining | done
    · right
      cases ho : out.pc <;> simp only [ho, Joining] at joining
      all_goals simpa [hp, ho, clockRoundRank, joinRank] using h.2
    · exact Or.inl done
  all_goals simp only [Algorithm3.ordinary, hp] at step
  all_goals try contradiction
  all_goals cases hq : (s i).q <;> simp only [hq, Bind.bind, Option.bind] at step
  all_goals try contradiction
  case attempt.some v =>
    simp only [Option.some.injEq] at step; subst out
    right
    have := lower_scan_rank i.val m i.val false
    change clockRoundRank m (Algorithm3.tickLower i.val m i.val false) < 4 * m + 6
    omega
  case tickLower.some j observed v =>
    split at step
    · rename_i valid
      cases sample : (s ⟨j, valid⟩).q <;> simp only [sample, Bind.bind, Option.bind, Option.some.injEq] at step
      · subst out; exact Or.inr (by have := lower_scan_rank i.val m j observed; change clockRoundRank m (Algorithm3.tickLower i.val m j observed) < 2 * m + 2 * j + 5; omega)
      · subst out; exact Or.inr (by simp [clockRoundRank])
    · contradiction
  case lowerOwn.some j sample v =>
    split at step
    · simp only [Bind.bind, Option.bind, Option.some.injEq] at step; subst out; exact Or.inl rfl
    · simp only [Bind.bind, Option.bind, Option.some.injEq] at step; subst out
      exact Or.inr (lower_scan_rank i.val m j true)
  case tickUpper.some j v =>
    split at step
    · rename_i valid
      cases sample : (s ⟨j, valid⟩).q <;> simp only [sample, Bind.bind, Option.bind, Option.some.injEq] at step
      · subst out; exact Or.inr (by have := upper_scan_rank i.val m j; change clockRoundRank m (Algorithm3.tickUpper i.val j) < 2 * j + 4; omega)
      · subst out; exact Or.inr (by simp [clockRoundRank])
    · contradiction
  case upperOwn.some j sample v =>
    split at step
    · simp only [Bind.bind, Option.bind, Option.some.injEq] at step; subst out; exact Or.inl rfl
    · simp only [Bind.bind, Option.bind, Option.some.injEq] at step; subst out
      exact Or.inr (upper_scan_rank i.val m j)
  case tickRead.some v =>
    simp only [Bind.bind, Option.bind, Option.some.injEq] at step; subst out
    exact Or.inr (by simp [clockRoundRank])
  case tickWrite.some b v =>
    split at step
    · simp only [Option.some.injEq] at step; subst out; exact Or.inl rfl
    · contradiction

/-- A possibly partial stage 6 scan followed by one stage 7 invocation. -/
def LowerRound {n : Nat} : PC n → Prop
  | .maintain _ | .lowerTick _ => True
  | _ => False

def lowerRoundRank {n : Nat} : PC n → Nat
  | .maintain rest => 4 * (2 * n) + 7 + rest.length
  | .lowerTick cp => clockRoundRank (2 * n) cp
  | _ => 0

/-- The returned control is the real list test, not a successful-tick label. -/
def LowerRoundOutcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (p : Proc n) (t : Nat) : Prop :=
  (r.command t = .run p ∧ (r.state (t + 1) p).pc = .test) ∨ r.event t = .fail p

theorem lower_round_ordinary {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {out : Local n} (round : LowerRound (s p).pc) (step : ordinary cfg s p = some out) :
    (LowerRound out.pc ∨ out.pc = .test) ∧ lowerRoundRank out.pc < lowerRoundRank (s p).pc := by
  cases hp : (s p).pc <;> simp only [hp, LowerRound] at round
  case maintain rest =>
    cases rest <;> simp only [ordinary, hp, Option.some.injEq] at step
    all_goals subst out; simp [LowerRound, lowerRoundRank, clockRoundRank]
  case lowerTick cp =>
    simp only [ordinary, hp] at step
    obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step
    subst out
    unfold clockInstruction at hc
    have descent := clock_round_step hc
    simp only [ite_true] at descent
    dsimp
    split
    · rename_i returned
      constructor
      · exact Or.inr rfl
      · cases cp <;> simp_all [lowerRoundRank, clockRoundRank, clockInstruction, Algorithm3.ordinary]
    · rename_i continuing
      exact ⟨Or.inl trivial, descent.resolve_left continuing⟩

theorem next_lower_round {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {p : Proc n} (round : LowerRound (s p).pc)
    (step : next cfg s command = some t)
    (noReturn : ¬ (command = .run p ∧ (t p).pc = .test))
    (noFail : label s command ≠ .fail p) :
    LowerRound (t p).pc ∧
      (Acts command p → lowerRoundRank (t p).pc < lowerRoundRank (s p).pc) := by
  by_cases act : Acts command p
  · rcases act with rfl | rfl
    · obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp step
      have result := lower_round_ordinary round ho
      exact ⟨by simpa using result.1.resolve_right (fun h => noReturn ⟨rfl, by simpa using h⟩),
        by intro _; simpa using result.2⟩
    · exact (noFail rfl).elim
  · have live : (s p).pc ≠ .down := by intro eq; simp [eq, LowerRound] at round
    have eq := next_live_unchanged step live act
    exact ⟨by simpa [eq] using round, fun h => (act h).elim⟩

/-- Finite return of any in-flight maintenance/clock round in an initialized
client run. No outer completion, stable bits, or successful ticking is assumed. -/
theorem lower_round_eventually {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (round : LowerRound (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ LowerRoundOutcome r p finish := by
  classical
  by_contra missing
  have noOutcome : ∀ t, start ≤ t → ¬ LowerRoundOutcome r p t := by
    intro t lo outcome; exact missing ⟨t, lo, outcome⟩
  have roundAll : ∀ t, start ≤ t → LowerRound (r.state t p).pc := by
    intro t lo
    induction t, lo using Nat.le_induction with
    | base => exact round
    | succ t lo ih =>
      exact (next_lower_round ih (r.valid t)
        (fun h => noOutcome t lo (Or.inl h)) (fun h => noOutcome t lo (Or.inr h))).1
  apply fair_descent_impossible r fair p start (fun l => lowerRoundRank l.pc)
  · intro t lo
    have := roundAll t lo
    cases hp : (r.state t p).pc <;> simp_all [LowerRound, Protocol]
  · intro t lo act
    exact (next_lower_round (roundAll t lo) (r.valid t)
      (fun h => noOutcome t lo (Or.inl h)) (fun h => noOutcome t lo (Or.inr h))).2 act

/-- The first return-or-failure is in the original lower episode. A failed
attempt and a successful tick both return; a restarted request cannot pay it. -/
theorem lower_round_original_episode {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (round : LowerRound (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
      LowerRoundOutcome r p finish ∧
      (∀ t, start ≤ t → t ≤ finish → LowerRound (r.state t p).pc) := by
  classical
  have ex := lower_round_eventually r fair round
  have first := Nat.find_spec ex
  have noOutcome : ∀ t, start ≤ t → t < Nat.find ex → ¬ LowerRoundOutcome r p t := by
    intro t lo hi outcome
    have := Nat.find_min' ex ⟨lo, outcome⟩
    omega
  refine ⟨Nat.find ex, first.1, ?_, first.2, ?_⟩
  · intro t lo hi bad
    exact noOutcome t lo hi (Or.inr bad)
  · intro t lo hi
    induction t, lo using Nat.le_induction with
    | base => exact round
    | succ t lo ih =>
      exact (next_lower_round (ih (by omega)) (r.valid t)
        (fun h => noOutcome t lo (by omega) (Or.inl h))
        (fun h => noOutcome t lo (by omega) (Or.inr h))).1

private theorem lower_control {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) {p : Proc n} (lower : IsLower (s p).value.clock) :
    LowerRound (s p).pc ∨ (s p).pc = .test ∨ (s p).pc = .publish := by
  have facts := (reachable_invariant reach).localFacts p
  cases hp : (s p).pc <;> simp_all [LowerRound, LocalFacts]
  all_goals cases tag : (s p).value.clock <;> simp_all [IsLower, visible]

private theorem lower_after_no_fail {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {p : Proc n} (step : next cfg s command = some t)
    (lower : IsLower (t p).value.clock) : label s command ≠ .fail p := by
  intro eq
  cases command with
  | run q => simp only [label] at eq; split at eq <;> contradiction
  | fail q =>
    simp only [label, Label.fail.injEq] at eq; subst q
    simp only [next] at step
    split at step <;> try contradiction
    simp only [Option.some.injEq] at step; subst t
    simp [reset, dead, IsLower] at lower
  | restart q => simp [label] at eq
  | stutter => simp [label] at eq

/-- A continuously occupied lower position cannot stall in the publication
control: its owed action would either leave lower or erase the episode. -/
private theorem continuous_lower_no_publish {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (lower : ∀ t, start ≤ t → IsLower (r.state t p).value.clock)
    {t : Nat} (lo : start ≤ t) : (r.state t p).pc ≠ .publish := by
  intro pub
  obtain ⟨u, hi, act, old⟩ := first_scheduled_action r fair (p := p) (start := t)
    (by simp [pub, Protocol])
  have step := r.valid u
  rcases act with run | fail
  · rw [run] at step
    have pc : (r.state u p).pc = .publish := by rw [old, pub]
    simp only [next, ordinary, pc, Option.map_some, Option.some.injEq] at step
    have low := lower (u + 1) (by omega)
    rw [← step] at low
    simp [IsLower] at low
  · exact lower_after_no_fail step (lower (u + 1) (by omega)) (by simp [fail, label])

/-- From a list test, continuous lower occupancy forces the next full stage 6
round. An empty list would instead lead to publication and contradict occupancy. -/
private theorem continuous_lower_test_starts_round {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start t : Nat}
    (lower : ∀ u, start ≤ u → IsLower (r.state u p).value.clock)
    (lo : start ≤ t) (test : (r.state t p).pc = .test) :
    ∃ begin, t < begin ∧ (r.state begin p).pc = .maintain (cfg.order p) := by
  obtain ⟨u, hi, act, old⟩ := first_scheduled_action r fair (p := p) (start := t)
    (by simp [test, Protocol])
  have step := r.valid u
  rcases act with run | fail
  · rw [run] at step
    have pc : (r.state u p).pc = .test := by rw [old, test]
    simp only [next, ordinary, pc, Option.map_some, Option.some.injEq] at step
    by_cases empty : (r.state u p).behind = ∅
    · have pub : (r.state (u + 1) p).pc = .publish := by rw [← step]; simp [empty]
      exact (continuous_lower_no_publish r fair lower (by omega) pub).elim
    · refine ⟨u + 1, by omega, ?_⟩
      rw [← step]; simp [empty]
  · exact (lower_after_no_fail step (lower (u + 1) (by omega)) (by simp [fail, label])).elim

/-- Every continuously lower peer executes full maintenance/attempt rounds
arbitrarily late. This is conditional on occupancy, not a new fairness premise;
it applies to each surviving member of the previously derived fixed cohort. -/
theorem continuous_lower_rounds {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (lower : ∀ t, start ≤ t → IsLower (r.state t p).value.clock) :
    ∀ t, start ≤ t → ∃ begin finish, t < begin ∧ begin ≤ finish ∧
      (r.state begin p).pc = .maintain (cfg.order p) ∧
      SameEpisodeUntil r p t finish ∧ r.command finish = .run p ∧
      (r.state (finish + 1) p).pc = .test := by
  intro t lo
  have noFail : ∀ u, start ≤ u → r.event u ≠ .fail p := by
    intro u hi; exact lower_after_no_fail (r.valid u) (lower (u + 1) (by omega))
  have testLater : ∃ u, t ≤ u ∧ (r.state u p).pc = .test := by
    rcases lower_control (r.reachable t) (lower t lo) with round | test | pub
    · obtain ⟨finish, hi, outcome⟩ := lower_round_eventually r fair round
      rcases outcome with returned | failed
      · exact ⟨finish + 1, by omega, returned.2⟩
      · exact (noFail finish (by omega) failed).elim
    · exact ⟨t, le_rfl, test⟩
    · exact (continuous_lower_no_publish r fair lower lo pub).elim
  obtain ⟨u, hi, test⟩ := testLater
  obtain ⟨begin, ub, fresh⟩ := continuous_lower_test_starts_round r fair lower (by omega) test
  obtain ⟨finish, bf, _, outcome, _⟩ := lower_round_original_episode r fair
    (p := p) (start := begin) (by simp [fresh, LowerRound])
  rcases outcome with returned | failed
  · exact ⟨begin, finish, by omega, bf, fresh,
      by intro v tv _; exact noFail v (by omega), returned.1, returned.2⟩
  · exact (noFail finish (by omega) failed).elim

/-- Combine the reviewed finite-departure reduction with concrete round return.
Every member retained in the fixed cohort keeps completing fresh rounds. -/
theorem held_cohort_rounds {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (owner : Proc n) (start : Nat)
    (held : ∀ t, start ≤ t → Holding (r.state t owner).pc) :
    ∃ stable, start ≤ stable ∧ ∀ peer, peer ≠ owner →
      IsLower (r.state stable peer).value.clock →
      ∀ t, stable ≤ t → ∃ begin finish, t < begin ∧ begin ≤ finish ∧
        (r.state begin peer).pc = .maintain (cfg.order peer) ∧
        SameEpisodeUntil r peer t finish ∧ r.command finish = .run peer ∧
        (r.state (finish + 1) peer).pc = .test := by
  obtain ⟨stable, lo, cohort⟩ := held_cohort_stabilizes r owner start held
  refine ⟨stable, lo, ?_⟩
  intro peer other member
  exact continuous_lower_rounds r fair
    (fun t hi => ((cohort t hi peer other).1).mpr member)

end EconomicalSolutions.Algorithm6

#print axioms EconomicalSolutions.Algorithm6.clock_round_step
#print axioms EconomicalSolutions.Algorithm6.lower_round_original_episode

#print axioms EconomicalSolutions.Algorithm6.continuous_lower_rounds

#print axioms EconomicalSolutions.Algorithm6.held_cohort_rounds
