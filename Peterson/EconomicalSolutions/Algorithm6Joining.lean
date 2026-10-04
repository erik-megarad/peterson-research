module

public import Peterson.EconomicalSolutions.Algorithm6History

@[expose] public section

/-! Finite upper joining under the frozen instruction-or-failure scheduling.
This does not assert successful ticking or tournament completion. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm6

def Protocol {n : Nat} : PC n → Prop
  | .down | .idle | .cs => False
  | _ => True

structure Run {n : Nat} (cfg : Config n) where
  state : Nat → State n
  command : Nat → Command n
  initialized : state 0 = initial n
  valid : ∀ t, next cfg (state t) (command t) = some (state (t + 1))

def Run.event {n : Nat} {cfg : Config n} (r : Run cfg) (t : Nat) : Label n :=
  label (r.state t) (r.command t)

def Acts {n : Nat} (c : Command n) (p : Proc n) : Prop := c = .run p ∨ c = .fail p

/-- Only protocol instructions are owed; a process in outer `cs` may stay
there forever. Neither local tournament completion nor vacancy is a premise. -/
def ProtocolScheduling {n : Nat} {cfg : Config n} (r : Run cfg) : Prop :=
  ∀ t p, Protocol (r.state t p).pc → ∃ u, t ≤ u ∧ Acts (r.command u) p

theorem Run.reachable {n : Nat} {cfg : Config n} (r : Run cfg) (t : Nat) :
    Reachable cfg (r.state t) := by
  induction t with
  | zero => rw [r.initialized]; exact .initial
  | succ t ih => exact .step ih ⟨r.command t, r.valid t, rfl⟩

theorem next_live_unchanged {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    {p : Proc n} (step : next cfg s c = some t) (live : (s p).pc ≠ .down)
    (noAct : ¬ Acts c p) : t p = s p := by
  cases c with
  | stutter => simp only [next, Option.some.injEq] at step; subst t; rfl
  | run q =>
    have other : p ≠ q := by intro h; subst q; exact noAct (Or.inl rfl)
    simp only [next] at step
    cases h : ordinary cfg s q <;> simp only [h, Option.map_none, Option.map_some, Option.some.injEq] at step
    · contradiction
    · subst t; simp [other]
  | fail q =>
    have other : p ≠ q := by intro h; subst q; exact noAct (Or.inr rfl)
    simp only [next] at step
    split at step <;> try contradiction
    simp only [Option.some.injEq] at step; subst t; simp [other]
  | restart q =>
    simp only [next] at step
    split at step
    · rename_i down
      have other : p ≠ q := by intro h; subst q; exact live down
      simp only [Option.some.injEq] at step; subst t; simp [other]
    · contradiction

theorem first_scheduled_action {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (owed : Protocol (r.state start p).pc) :
    ∃ t, start ≤ t ∧ Acts (r.command t) p ∧ r.state t p = r.state start p := by
  classical
  have ex := fair start p owed
  have spec := Nat.find_spec ex
  have live : (r.state start p).pc ≠ .down := by intro h; simp [h, Protocol] at owed
  have unchanged : ∀ t, start ≤ t → t ≤ Nat.find ex → r.state t p = r.state start p := by
    intro t lo hi
    induction t, lo using Nat.le_induction with
    | base => rfl
    | succ t lo ih =>
      have old := ih (by omega)
      have noAct : ¬ Acts (r.command t) p := by
        intro act
        have := Nat.find_min' ex ⟨lo, act⟩
        omega
      exact (next_live_unchanged (r.valid t) (by simpa [old] using live) noAct).trans old
  exact ⟨Nat.find ex, spec.1, spec.2, unchanged _ spec.1 (le_refl _)⟩

/-- Every minimum local rank eventually faces its own real run/failure.
The applications below prove descent directly from `ordinary`/`next`. -/
theorem fair_descent_impossible {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (p : Proc n) (start : Nat) (rank : Local n → Nat)
    (owed : ∀ t, start ≤ t → Protocol (r.state t p).pc)
    (decrease : ∀ t, start ≤ t → Acts (r.command t) p →
      rank (r.state (t + 1) p) < rank (r.state t p)) : False := by
  classical
  have ex : ∃ v, ∃ t, start ≤ t ∧ rank (r.state t p) = v :=
    ⟨rank (r.state start p), start, le_rfl, rfl⟩
  obtain ⟨t, lo, value⟩ := Nat.find_spec ex
  obtain ⟨u, tu, act, unchanged⟩ := first_scheduled_action r fair (owed t lo)
  have less := decrease u (by omega) act
  have min := Nat.find_min' ex
    (show ∃ k, start ≤ k ∧ rank (r.state k p) = rank (r.state (u + 1) p) from
      ⟨u + 1, by omega, rfl⟩)
  rw [unchanged, value] at less
  omega


def Joining : Algorithm3.PC → Prop
  | .joinLower _ | .joinUpper _ | .joinWrite _ => True
  | _ => False

def joinRank (width : Nat) : Algorithm3.PC → Nat
  | .joinLower j => width + j + 2
  | .joinUpper j => j + 2
  | .joinWrite _ => 1
  | _ => 0

theorem startJoin_joining {n : Nat} (p : Proc n) (upper : Bool) : Joining (startJoin p upper) := by
  dsimp [startJoin, Algorithm3.joinLower]
  split
  · trivial
  · split <;> trivial

/-- Only finite descending scans or the cached publication belong to joining. -/
theorem clock_join_step {m : Nat} {s : Algorithm3.State m} {i : Fin m}
    {out : Algorithm3.Local} (joining : Joining (s i).pc)
    (step : Algorithm3.ordinary s i = some out) :
    (Joining out.pc ∨ out.pc = .attempt) ∧
      joinRank m out.pc < joinRank m (s i).pc := by
  cases hp : (s i).pc <;> simp only [hp, Joining] at joining
  all_goals simp only [Algorithm3.ordinary, hp] at step
  case joinLower j =>
    split at step
    · rename_i valid
      cases sample : (s ⟨j, valid⟩).q <;> simp only [sample, Option.some.injEq] at step
      · subst out
        unfold Algorithm3.joinLower
        split
        · simp [Joining, joinRank, hp]; omega
        · split <;> simp [Joining, joinRank, hp]
          all_goals omega
      · subst out; simp [Joining, joinRank, hp]
    · contradiction
  case joinUpper j =>
    split at step
    · rename_i valid
      cases sample : (s ⟨j, valid⟩).q <;> simp only [sample, Option.some.injEq] at step
      · subst out
        split <;> simp [Joining, joinRank, hp]
        all_goals omega
      · subst out; simp [Joining, joinRank, hp]
    · contradiction
  case joinWrite b =>
    split at step
    · simp only [Option.some.injEq] at step; subst out; simp [Joining, joinRank, hp]
    · contradiction

def JoinFacts {n : Nat} (pc : PC n) : Prop :=
  match pc with | .upperJoin cp => Joining cp | _ => True

theorem ordinary_joinFacts {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {l : Local n} (facts : JoinFacts (s p).pc) (step : ordinary cfg s p = some l) :
    JoinFacts l.pc := by
  cases hp : (s p).pc
  case' build rest => cases rest
  case' maintain rest => cases rest
  case' lowerJoin cp => cases cp
  all_goals simp only [ordinary, hp] at step
  all_goals try contradiction
  case request | acquire =>
    unfold tournamentInstruction at step
    obtain ⟨t, _, eq⟩ := Option.map_eq_some_iff.mp step
    subst l
    split
    · exact startJoin_joining p true
    · trivial
  case upperJoin cp =>
    obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step
    subst l
    have joined := (clock_join_step (s := fun j => ⟨clockValue s j,
      if j = position p true then cp else .idle⟩) (i := position p true)
      (by simpa [JoinFacts, hp] using facts) hc).1
    dsimp
    split
    · trivial
    · rename_i notAttempt
      exact joined.resolve_right notAttempt
  all_goals try (obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step; subst l)
  all_goals try (simp only [Option.some.injEq] at step; subst l)
  all_goals dsimp
  all_goals repeat first | split | trivial

theorem reachable_joinFacts {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) : ∀ p, JoinFacts (s p).pc := by
  induction reach with
  | initial => intro p; trivial
  | @step s t a _ edge ih =>
    obtain ⟨command, step, _⟩ := edge
    cases command with
    | stutter => have eq : s = t := Option.some.inj step; simpa [← eq] using ih
    | run p =>
      obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp step
      intro q
      by_cases eq : q = p
      · subst q; simpa using ordinary_joinFacts (ih p) hl
      · simpa [eq] using ih q
    | fail p | restart p =>
      simp only [next] at step
      split at step <;> try contradiction
      all_goals simp only [Option.some.injEq] at step; subst t; intro q
      all_goals by_cases eq : q = p
      all_goals first | (subst q; simp [reset, JoinFacts]) | simpa [eq] using ih q

def UpperJoining {n : Nat} : PC n → Prop
  | .upperJoin _ => True
  | _ => False

def upperJoinRank {n : Nat} : PC n → Nat
  | .upperJoin cp => joinRank (2 * n) cp
  | _ => 0

def JoinOutcome {n : Nat} {cfg : Config n} (r : Run cfg) (p : Proc n) (t : Nat) : Prop :=
  r.event t = .upperJoin p ∨ r.event t = .fail p

theorem upper_join_ordinary {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {l : Local n} (facts : JoinFacts (s p).pc) (joining : UpperJoining (s p).pc)
    (step : ordinary cfg s p = some l) :
    upperJoinRank l.pc < upperJoinRank (s p).pc ∧
      (label s (.run p) ≠ .upperJoin p → UpperJoining l.pc) := by
  cases hp : (s p).pc <;> simp only [hp, UpperJoining] at joining
  rename_i cp
  simp only [ordinary, hp] at step
  obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step
  subst l
  have cj : Joining cp := by simpa [JoinFacts, hp] using facts
  have cs := clock_join_step (s := fun j => ⟨clockValue s j,
    if j = position p true then cp else .idle⟩) (i := position p true) (by simpa using cj) hc
  simp only [ite_true] at cs
  constructor
  · dsimp
    split
    · simpa [upperJoinRank, joinRank, *] using cs.2
    · exact cs.2
  · intro noJoin
    have noAttempt : c.pc ≠ .attempt := by
      cases cp <;> simp only [Joining] at cj
      all_goals try (simp [label, hp] at noJoin)
      all_goals unfold clockInstruction at hc
      all_goals simp only [Algorithm3.ordinary, ↓reduceIte] at hc
      all_goals split at hc <;> try contradiction
      all_goals rename_i valid
      all_goals cases sample : clockValue s ⟨_, valid⟩
      all_goals simp only [sample, Option.some.injEq] at hc
      all_goals subst c
      all_goals simp only [Algorithm3.joinLower]
      all_goals repeat first | split | simp
    simp [noAttempt, UpperJoining]

theorem next_upper_joining {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {p : Proc n} (reach : Reachable cfg s)
    (joining : UpperJoining (s p).pc) (step : next cfg s command = some t)
    (noJoin : label s command ≠ .upperJoin p) (noFail : label s command ≠ .fail p) :
    UpperJoining (t p).pc ∧
      (Acts command p → upperJoinRank (t p).pc < upperJoinRank (s p).pc) := by
  by_cases act : Acts command p
  · rcases act with rfl | rfl
    · obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp step
      have result := upper_join_ordinary (reachable_joinFacts reach p) joining hl
      exact ⟨by simpa using result.2 noJoin, by intro _; simpa using result.1⟩
    · exact (noFail rfl).elim
  · have live : (s p).pc ≠ .down := by intro eq; simp [eq, UpperJoining] at joining
    have eq := next_live_unchanged step live act
    exact ⟨by simpa [eq] using joining, fun h => (act h).elim⟩

/-- Each upper-join occurrence reaches its actual publication or its own abort.
The theorem has no outer critical-completion or successful-tick premise. -/
theorem upper_join_eventually {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (joining : UpperJoining (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ JoinOutcome r p finish := by
  classical
  by_contra missing
  have noOutcome : ∀ t, start ≤ t → ¬ JoinOutcome r p t := by
    intro t lo outcome; exact missing ⟨t, lo, outcome⟩
  have joiningAll : ∀ t, start ≤ t → UpperJoining (r.state t p).pc := by
    intro t lo
    induction t, lo using Nat.le_induction with
    | base => exact joining
    | succ t lo ih =>
      exact (next_upper_joining (r.reachable t) ih (r.valid t)
        (fun h => noOutcome t lo (Or.inl h)) (fun h => noOutcome t lo (Or.inr h))).1
  apply fair_descent_impossible r fair p start (fun l => upperJoinRank l.pc)
  · intro t lo
    have := joiningAll t lo
    cases hp : (r.state t p).pc <;> simp_all [UpperJoining, Protocol]
  · intro t lo act
    exact (next_upper_joining (r.reachable t) (joiningAll t lo) (r.valid t)
      (fun h => noOutcome t lo (Or.inl h)) (fun h => noOutcome t lo (Or.inr h))).2 act

/-- History labels keep failure/restart from satisfying an older occurrence. -/
def SameEpisodeUntil {n : Nat} {cfg : Config n} (r : Run cfg)
    (p : Proc n) (start finish : Nat) : Prop :=
  ∀ t, start ≤ t → t < finish → r.event t ≠ .fail p

/-- The first publication-or-failure belongs to the original joining episode;
its prestate is still joining, including on a failure endpoint. -/
theorem upper_join_original_episode {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (joining : UpperJoining (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
      JoinOutcome r p finish ∧
      (∀ t, start ≤ t → t ≤ finish → UpperJoining (r.state t p).pc) := by
  classical
  have ex := upper_join_eventually r fair joining
  have first := Nat.find_spec ex
  have noOutcome : ∀ t, start ≤ t → t < Nat.find ex → ¬ JoinOutcome r p t := by
    intro t lo hi outcome
    have := Nat.find_min' ex ⟨lo, outcome⟩
    omega
  refine ⟨Nat.find ex, first.1, ?_, first.2, ?_⟩
  · intro t lo hi bad
    exact noOutcome t lo hi (Or.inr bad)
  · intro t lo hi
    induction t, lo using Nat.le_induction with
    | base => exact joining
    | succ t lo ih =>
      exact (next_upper_joining (r.reachable t) (ih (by omega)) (r.valid t)
        (fun h => noOutcome t lo (by omega) (Or.inl h))
        (fun h => noOutcome t lo (by omega) (Or.inr h))).1

/-- Frozen obligation (1), still open: these are admitted controls before
completion of the third upper write, including the finite initial join. -/
def BeforeThird {n : Nat} : PC n → Prop
  | .upperJoin _ => True
  | .upperTick count _ => count < 3
  | _ => False

def ThirdUpperWrite {n : Nat} {cfg : Config n} (r : Run cfg) (p : Proc n) (t : Nat) : Prop :=
  r.command t = .run p ∧ ∃ b, (r.state t p).pc = .upperTick 2 (.tickWrite b)

def UpperTerminationTarget : Prop :=
  ∀ n (cfg : Config n) (r : Run cfg), ProtocolScheduling r →
    ∀ p start, BeforeThird (r.state start p).pc →
      ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
        (ThirdUpperWrite r p finish ∨ r.event finish = .fail p)

end EconomicalSolutions.Algorithm6

#print axioms EconomicalSolutions.Algorithm6.reachable_joinFacts
#print axioms EconomicalSolutions.Algorithm6.upper_join_original_episode
