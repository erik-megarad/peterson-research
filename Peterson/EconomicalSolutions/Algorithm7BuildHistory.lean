import Peterson.EconomicalSolutions.Algorithm7Episode

/-! Original list-building histories and barriers before level-three publication.
These are finite-history lemmas for the unchanged Algorithm 7 interpreter. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm7
namespace BuildHistory
open EpisodeHistory CreditHistory

/-- The peer has been read in stage 3 of this request. All subsequent controls
retain this history; leaving the request clears it. -/
def BuiltPeer (q : Proc n) : PC n → Prop
  | .build rest => q ∉ rest
  | .prefixRead _ | .prefixWrite _ | .delete _ | .add _ => True
  | .attempt .maintain _ _ | .tickWrite .maintain _ _ | .pairDone .maintain => True
  | pc => Active pc

def BuildRead {n : Nat} (s : State n) (c : Command n) (p q : Proc n) : Prop :=
  c = .run p ∧ ∃ rest, (s p).pc = .build (q :: rest)

theorem active_built {pc : PC n} (active : Active pc) (q : Proc n) : BuiltPeer q pc := by
  cases pc <;> simp_all [Active, BuiltPeer]
  case attempt phase _ _ | tickWrite phase _ _ | pairDone phase =>
    cases phase <;> simp_all [Active, BuiltPeer]

theorem ordinary_built_peer {n : Nat} {cfg : Config n} {s : State n} {p q : Proc n}
    {out : Local n} (other : q ≠ p) (step : ordinary cfg s p = some out)
    (after : BuiltPeer q out.pc) : BuiltPeer q (s p).pc ∨ BuildRead s (.run p) p q := by
  cases pc : (s p).pc
  case' join clock first cp => cases cp
  case' attempt phase clock cp => cases phase
  case' tickWrite phase clock pending => cases phase
  case' pairDone phase => cases phase
  case' build rest => cases rest
  all_goals try (left; simp [pc, BuiltPeer, Active]; done)
  case build.cons head rest =>
    by_cases eq : q = head
    · subst head; exact Or.inr ⟨rfl, rest, pc⟩
    · left
      simp only [ordinary, pc, Option.some.injEq] at step
      subst out
      simpa [pc, BuiltPeer, eq] using after
  case' attempt.one => cases clock <;> cases cp
  case' tickWrite.one => cases clock
  all_goals simp only [ordinary, pc] at step
  all_goals try contradiction
  all_goals try (obtain ⟨result, _, rfl⟩ := Option.map_eq_some_iff.mp step)
  all_goals repeat (split at step)
  all_goals try contradiction
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try (simp_all [BuiltPeer, Active, afterAttempt, cfg.complete]; done)
  all_goals simp only [bind, Option.bind_eq_some_iff] at step
  all_goals obtain ⟨result, _, step⟩ := step
  all_goals split at step
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at step
  all_goals subst out
  all_goals contradiction

theorem next_built_peer {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    {p q : Proc n} (other : q ≠ p) (step : next cfg s c = some t)
    (after : BuiltPeer q (t p).pc) : BuiltPeer q (s p).pc ∨ BuildRead s c p q := by
  cases c with
  | stutter => have eq := Option.some.inj step; exact Or.inl (by simpa [← eq] using after)
  | run actor =>
    obtain ⟨out, instruction, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor; exact ordinary_built_peer other instruction (by simpa using after)
    · exact Or.inl (by simpa [eq] using after)
  | request actor | complete actor | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp_all [BuiltPeer, Active, reset])
      | exact Or.inl (by simpa [eq] using after)

/-- An actual stage-3 read from the endpoint's request, with uninterrupted
control history afterwards. Overlapping builders may read each other at level one. -/
theorem original_build_read {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (other : q ≠ p) (built : BuiltPeer q (trace b p).pc) :
    ∃ r, r < b ∧ BuildRead (trace r) (commands r) p q ∧
      ∀ u, r < u → u ≤ b → BuiltPeer q (trace u p).pc := by
  induction b with
  | zero => simp [valid.1, initial, reset, BuiltPeer, Active] at built
  | succ b ih =>
    rcases next_built_peer other (valid.2 b (by omega)) built with before | read
    · obtain ⟨r, rb, read, kept⟩ := ih (by omega) before
      refine ⟨r, by omega, read, ?_⟩
      intro u ru ub
      by_cases last : u = b + 1
      · simpa [last] using built
      · exact kept u ru (by omega)
    · refine ⟨b, by omega, read, ?_⟩
      intro u bu ub
      have eq : u = b + 1 := by omega
      simpa [eq] using built

/-- A listed peer blocks both the unfinished builder and its ensuing
maintenance. The delayed level-two prefix operations are included. -/
def BuildingOrMaintaining : PC n → Prop
  | .build _ | .prefixRead .two | .prefixWrite (.live .two _ _) => True
  | pc => Maintaining pc

def Listed (q : Proc n) (l : Local n) : Prop :=
  BuildingOrMaintaining l.pc ∧ q ∈ l.behind

theorem ordinary_listed {n : Nat} {cfg : Config n} {s : State n} {p q : Proc n}
    {out : Local n} (before : Listed q (s p)) (peer : exposed (s q).value = true)
    (step : ordinary cfg s p = some out) : Listed q out := by
  obtain ⟨band, member⟩ := before
  by_cases maintain : Maintaining (s p).pc
  · have waiting := ordinary_waiting_for ⟨maintain, member⟩ peer step
    refine ⟨?_, waiting.2⟩
    have h := waiting.1
    cases pc : out.pc <;> simp_all [Maintaining, BuildingOrMaintaining]
  · cases pc : (s p).pc <;> simp only [pc, BuildingOrMaintaining] at band
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
    all_goals simp_all [Listed, BuildingOrMaintaining, Maintaining]

theorem next_listed {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    {p q : Proc n} (before : Listed q (s p)) (peer : exposed (s q).value = true)
    (noAbort : c ≠ .fail p) (step : next cfg s c = some t) : Listed q (t p) := by
  cases c with
  | stutter => have eq := Option.some.inj step; simpa [← eq] using before
  | run actor =>
    obtain ⟨out, instruction, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor; simpa using ordinary_listed before peer instruction
    · simpa [eq] using before
  | request actor | complete actor | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp_all [Listed, BuildingOrMaintaining, Maintaining])
      | simpa [eq] using before

theorem listed_persists {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (ab : a ≤ b) (bf : b ≤ finish)
    (before : Listed q (trace a p))
    (peer : ∀ r, a ≤ r → r < b → exposed (trace r q).value = true)
    (noAbort : ∀ r, a ≤ r → r < b → commands r ≠ .fail p) :
    Listed q (trace b p) := by
  induction b, ab using Nat.le_induction with
  | base => exact before
  | succ b ab ih =>
    exact next_listed
      (ih (by omega) (by intro r lo hi; exact peer r lo (by omega))
        (by intro r lo hi; exact noAbort r lo (by omega)))
      (peer b ab (by omega)) (noAbort b ab (by omega)) (valid.2 b (by omega))

theorem listed_not_active {n : Nat} {l : Local n} {q : Proc n}
    (listed : Listed q l) (active : Active l.pc) : False := by
  have band := listed.1
  cases pc : l.pc <;> simp_all [BuildingOrMaintaining, Maintaining, Active]
  case attempt phase _ _ | tickWrite phase _ _ | pairDone phase =>
    cases phase <;> simp_all [Maintaining, Active]

theorem build_starts_listed {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {p q : Proc n} (read : BuildRead s c p q)
    (peer : exposed (s q).value = true) (step : next cfg s c = some t) : Listed q (t p) := by
  obtain ⟨rfl, rest, pc⟩ := read
  simp only [next, ordinary, pc, peer, ↓reduceIte, Option.map_some, Option.some.injEq] at step
  subst t
  simp [Listed, BuildingOrMaintaining]

theorem built_no_failure {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {p q : Proc n} (step : next cfg s c = some t)
    (after : BuiltPeer q (t p).pc) : c ≠ .fail p := by
  intro eq
  subst c
  simp only [next] at step
  split at step
  · contradiction
  · simp only [Option.some.injEq] at step
    subst t
    simp [reset, BuiltPeer, Active] at after

/-- The original stage-3 read is while the owner is visibly level one.
A later active request requires a nonexposed peer state somewhere from that
read through the endpoint. The witness may be the build read itself, or a
later loss of exposure; it is never assumed to be a maintenance read. -/
theorem active_build_requires_nonexposure {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (other : q ≠ p) (active : Active (trace b p).pc) :
    ∃ r u, r < b ∧ BuildRead (trace r) (commands r) p q ∧
      AtLevel (trace r p).value .one ∧ r ≤ u ∧ u < b ∧
      exposed (trace u q).value = false ∧
      (∀ v, r < v → v ≤ b → BuiltPeer q (trace v p).pc) ∧
      (∀ v, r < v → v < b → commands v ≠ .fail p) := by
  classical
  obtain ⟨r, rb, read, kept⟩ := original_build_read valid bf other (active_built active q)
  have live : AtLevel (trace r p).value .one := by
    have coh := reachable_coherent valid (by omega : r ≤ finish) p
    obtain ⟨_, rest, pc⟩ := read
    simpa [Coherent, pc] using coh
  have noAbort : ∀ v, r < v → v < b → commands v ≠ .fail p := by
    intro v rv vb
    exact built_no_failure (valid.2 v (by omega)) (kept (v + 1) (by omega) (by omega))
  suffices loss : ∃ u, r ≤ u ∧ u < b ∧ exposed (trace u q).value = false by
    obtain ⟨u, ru, ub, off⟩ := loss
    exact ⟨r, u, rb, read, live, ru, ub, off, kept, noAbort⟩
  by_contra noLoss
  have peer : ∀ u, r ≤ u → u < b → exposed (trace u q).value = true := by
    intro u ru ub
    cases eq : exposed (trace u q).value
    · exact (noLoss ⟨u, ru, ub, eq⟩).elim
    · rfl
  exact listed_not_active (listed_persists valid (by omega) bf
    (build_starts_listed read (peer r (le_refl _) rb) (valid.2 r (by omega)))
    (by intro u lo hi; exact peer u (by omega) hi)
    (by intro u lo hi; exact noAbort u (by omega) hi)) active

/-- An entrant's original build of a continuously exposed peer must precede
that exposure interval. This covers arbitrary enumeration and tied builders
without declaring their mixed-time scans to be simultaneous. -/
theorem active_build_precedes_exposure {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish a b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (other : q ≠ p) (active : Active (trace b p).pc)
    (peer : ∀ u, a ≤ u → u < b → exposed (trace u q).value = true) :
    ∃ r, r < a ∧ BuildRead (trace r) (commands r) p q ∧
      AtLevel (trace r p).value .one ∧
      (∀ v, r < v → v ≤ b → BuiltPeer q (trace v p).pc) := by
  obtain ⟨r, u, _, read, live, ru, ub, off, kept, _⟩ :=
    active_build_requires_nonexposure valid bf other active
  have ua : u < a := by
    by_contra h
    have on := peer u (by omega) ub
    simp_all
  exact ⟨r, by omega, read, live, kept⟩

/-- The control interval after the actual empty-list decision, including its
arbitrarily delayed prefix read and cached write. -/
def Departed : PC n → Prop
  | .prefixRead .three | .prefixWrite (.live .three _ _) => True
  | pc => Active pc

def EmptyDeparture {n : Nat} (s : State n) (c : Command n) (p : Proc n) : Prop :=
  c = .run p ∧ (s p).pc = .pairDone .maintain ∧ (s p).behind = ∅

theorem ordinary_departed {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {out : Local n} (coherent : Coherent (s p)) (step : ordinary cfg s p = some out)
    (after : Departed out.pc) : Departed (s p).pc ∨ EmptyDeparture s (.run p) p := by
  cases pc : (s p).pc
  case' join clock first cp => cases cp
  case' attempt phase clock cp => cases phase
  case' tickWrite phase clock pending => cases phase
  case' pairDone phase => cases phase
  case' build rest => cases rest
  case' delete rest => cases rest
  case' add rest => cases rest
  case' eligible rest => cases rest
  case' prefixRead level => cases level
  case' prefixWrite pending => cases pending
  case' prefixWrite.live level b0 b1 => cases level
  all_goals try (left; simp [pc, Departed, Active]; done)
  case pairDone.maintain =>
    simp only [ordinary, pc] at step
    split at step
    · right; exact ⟨rfl, pc, by assumption⟩
    · simp only [Option.some.injEq] at step
      subst out
      contradiction
  case prefixRead.one =>
    simp [Coherent, pc, PrefixPair] at coherent
  case' attempt.one => cases cp
  case' attempt.maintain => cases cp
  all_goals simp only [ordinary, pc] at step
  all_goals try contradiction
  all_goals try (obtain ⟨result, _, rfl⟩ := Option.map_eq_some_iff.mp step)
  all_goals repeat (split at step)
  all_goals try contradiction
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try (simp_all [Departed, Active, afterAttempt]; done)
  all_goals try (cases clock <;> simp_all [Departed, Active, afterAttempt]; done)
  all_goals simp only [bind, Option.bind_eq_some_iff] at step
  all_goals obtain ⟨result, _, step⟩ := step
  all_goals split at step
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at step
  all_goals subst out
  all_goals contradiction

theorem next_departed {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    {p : Proc n} (coherent : Coherent (s p)) (step : next cfg s c = some t)
    (after : Departed (t p).pc) : Departed (s p).pc ∨ EmptyDeparture s c p := by
  cases c with
  | stutter => have eq := Option.some.inj step; exact Or.inl (by simpa [← eq] using after)
  | run actor =>
    obtain ⟨out, instruction, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor; exact ordinary_departed coherent instruction (by simpa using after)
    · exact Or.inl (by simpa [eq] using after)
  | request actor | complete actor | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp_all [Departed, Active, reset])
      | exact Or.inl (by simpa [eq] using after)

/-- Every later departed control has an original empty-list decision with a
continuous suffix. Earlier request failures cannot be substituted for this exit. -/
theorem original_empty_departure {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish b : Nat} {p : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (departed : Departed (trace b p).pc) :
    ∃ d, d < b ∧ EmptyDeparture (trace d) (commands d) p ∧
      ∀ u, d < u → u ≤ b → Departed (trace u p).pc := by
  induction b with
  | zero => simp [valid.1, initial, reset, Departed, Active] at departed
  | succ b ih =>
    rcases next_departed (reachable_coherent valid (by omega) p)
      (valid.2 b (by omega)) departed with before | exit
    · obtain ⟨d, db, exit, kept⟩ := ih (by omega) before
      refine ⟨d, by omega, exit, ?_⟩
      intro u du ub
      by_cases last : u = b + 1
      · simpa [last] using departed
      · exact kept u du (by omega)
    · refine ⟨b, by omega, exit, ?_⟩
      intro u bu ub
      have eq : u = b + 1 := by omega
      simpa [eq] using departed

theorem active_departed {pc : PC n} (active : Active pc) : Departed pc := by
  cases pc <;> simp_all [Departed, Active]

theorem departed_built {pc : PC n} (departed : Departed pc) (q : Proc n) : BuiltPeer q pc := by
  cases pc <;> simp_all [Departed, BuiltPeer, Active]
  case attempt phase _ _ | tickWrite phase _ _ | pairDone phase =>
    cases phase <;> simp_all [Departed, BuiltPeer, Active]

theorem departed_not_maintaining {pc : PC n} (departed : Departed pc) : ¬ Maintaining pc := by
  cases pc <;> simp_all [Departed, Active, Maintaining]
  case attempt phase _ _ | tickWrite phase _ _ | pairDone phase =>
    cases phase <;> simp_all [Departed, Active, Maintaining]

theorem departed_exposed {l : Local n} (coherent : Coherent l)
    (departed : Departed l.pc) : exposed l.value = true := by
  by_cases active : Active l.pc
  · exact active_exposed coherent active
  · cases pc : l.pc <;> simp only [pc, Departed] at departed
    case' prefixRead level => cases level
    case' prefixWrite pending => cases pending
    case' prefixWrite.live level b0 b1 => cases level
    all_goals try (simp_all [Active]; done)
    all_goals simp only [Coherent, pc] at coherent
    case prefixRead.three =>
      obtain ⟨old, pair, b0, b1, value⟩ := coherent
      simp only [PrefixPair] at pair
      rcases pair with ⟨_, impossible⟩ | ⟨rfl, _⟩
      · contradiction
      · simp [value, exposed]
    case prefixWrite.live.three =>
      obtain ⟨old, new, c0, c1, pair, value, pending⟩ := coherent
      cases pending
      simp only [PrefixPair] at pair
      rcases pair with ⟨_, impossible⟩ | ⟨rfl, _⟩
      · contradiction
      · simp [value, exposed]

/-- Before original level-three publication, the empty-list decision already
starts a continuous exposed suffix. Its delayed read/write controls cannot be
mistaken for an unexposed builder or for fresh maintenance in a replacement. -/
theorem original_departure_episode {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish b : Nat} {p : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (active : Active (trace b p).pc) :
    ∃ d, d < b ∧ EmptyDeparture (trace d) (commands d) p ∧
      (∀ u, d < u → u ≤ b → Departed (trace u p).pc) ∧
      (∀ u, d < u → u ≤ b → exposed (trace u p).value = true) ∧
      (∀ u, d < u → u < b → commands u ≠ .fail p) := by
  obtain ⟨d, db, exit, kept⟩ := original_empty_departure valid bf (active_departed active)
  refine ⟨d, db, exit, kept, ?_, ?_⟩
  · intro u du ub
    exact departed_exposed (reachable_coherent valid (by omega) p) (kept u du ub)
  · intro u du ub
    exact built_no_failure (q := p) (valid.2 u (by omega))
      (departed_built (kept (u + 1) (by omega) (by omega)) p)

/-- At two active original requests, either process's level-one list sample
predates the other's original empty-list departure successor. This is an order
constraint, not mutual exclusion: overlapping builders may satisfy both sides. -/
theorem active_pair_build_departure_order {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (other : q ≠ p) (pa : Active (trace b p).pc) (qa : Active (trace b q).pc) :
    ∃ r d, r < d ∧ d < b ∧ BuildRead (trace r) (commands r) p q ∧
      AtLevel (trace r p).value .one ∧ EmptyDeparture (trace d) (commands d) q ∧
      (∀ u, d < u → u ≤ b → Departed (trace u q).pc) := by
  obtain ⟨d, db, exit, kept, exposed, _⟩ := original_departure_episode valid bf qa
  obtain ⟨r, rd, read, level, _⟩ := active_build_precedes_exposure valid bf other pa
    (a := d + 1) (by intro u lo hi; exact exposed u (by omega) (by omega))
  have ne : r ≠ d := by
    intro eq
    have commandsEqual : Command.run p = .run q := by
      rw [← read.1, eq, exit.1]
    exact other (Command.run.inj commandsEqual).symm
  exact ⟨r, d, by omega, db, read, level, exit, kept⟩

/-- The completed level-one counter test that begins stage 3. -/
def BuildStart {n : Nat} (s : State n) (c : Command n) (p : Proc n) : Prop :=
  c = .run p ∧ (s p).pc = .pairDone .one ∧ 3 ≤ (s p).count0 ∧ 3 ≤ (s p).count1

def Building : PC n → Prop | .build _ => True | _ => False

theorem ordinary_building {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {out : Local n} (step : ordinary cfg s p = some out) (after : Building out.pc) :
    Building (s p).pc ∨ BuildStart s (.run p) p := by
  cases pc : (s p).pc
  case' join clock first cp => cases cp
  case' attempt phase clock cp => cases clock <;> cases cp
  case' tickWrite phase clock pending => cases clock
  case' pairDone phase => cases phase
  case' build rest => cases rest
  case' delete rest => cases rest
  case' add rest => cases rest
  case' eligible rest => cases rest
  all_goals try (left; simp [pc, Building]; done)
  case pairDone.one =>
    simp only [ordinary, pc] at step
    split at step
    · right
      rename_i counts
      simp only [Bool.and_eq_true, decide_eq_true_eq] at counts
      exact ⟨rfl, pc, counts⟩
    · simp only [Option.some.injEq] at step
      subst out
      contradiction
  all_goals simp only [ordinary, pc] at step
  all_goals try contradiction
  all_goals try (obtain ⟨result, _, rfl⟩ := Option.map_eq_some_iff.mp step)
  all_goals repeat (split at step)
  all_goals try contradiction
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try (simp_all [Building, afterAttempt, reset]; done)
  all_goals try (split_ifs at after <;> simp_all [Building])
  all_goals simp only [bind, Option.bind_eq_some_iff] at step
  all_goals obtain ⟨result, _, step⟩ := step
  all_goals split at step
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at step
  all_goals subst out
  all_goals contradiction

theorem next_building {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    {p : Proc n} (step : next cfg s c = some t) (after : Building (t p).pc) :
    Building (s p).pc ∨ BuildStart s c p := by
  cases c with
  | stutter => have eq := Option.some.inj step; exact Or.inl (by simpa [← eq] using after)
  | run actor =>
    obtain ⟨out, instruction, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor; exact ordinary_building instruction (by simpa using after)
    · exact Or.inl (by simpa [eq] using after)
  | request actor | complete actor | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp_all [Building, reset])
      | exact Or.inl (by simpa [eq] using after)

/-- A stage-3 control has a real preceding successful both-counter test.
The suffix remains in the original list build, so it cannot borrow an earlier
request's completion or a later replacement's scan. -/
theorem original_build_start {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish b : Nat} {p : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (building : Building (trace b p).pc) :
    ∃ a, a < b ∧ BuildStart (trace a) (commands a) p ∧
      ∀ u, a < u → u ≤ b → Building (trace u p).pc := by
  induction b with
  | zero => simp [valid.1, initial, reset, Building] at building
  | succ b ih =>
    rcases next_building (valid.2 b (by omega)) building with before | start
    · obtain ⟨a, ab, start, kept⟩ := ih (by omega) before
      refine ⟨a, by omega, start, ?_⟩
      intro u au ub
      by_cases last : u = b + 1
      · simpa [last] using building
      · exact kept u au (by omega)
    · refine ⟨b, by omega, start, ?_⟩
      intro u bu ub
      have eq : u = b + 1 := by omega
      simpa [eq] using building

theorem passed_active {n : Nat} {pc : PC n} {q : Proc n}
    (passed : PassedPeer q pc) : Active pc := by
  cases pc <;> simp_all [PassedPeer, Active]

/-- Against an original smaller identifier's continuous level-three/cs band,
a larger peer's final credit must have been retained at every earlier suffix
state. A failure and replacement cannot hide between these retained samples. -/
theorem priority_retains_credit {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish a b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (episode : Episode trace commands q a b) (priority : q.val < p.val)
    (passed : PassedPeer q (trace b p).pc) :
    ∀ u, a < u → u ≤ b → PassedPeer q (trace u p).pc := by
  classical
  intro u au ub
  by_contra absent
  have other : q ≠ p := by intro eq; subst p; omega
  exact (stable_blocker_exclusion valid ub bf other absent
    (by
      intro r ur rb
      exact active_blocks (reachable_coherent valid (by omega) q)
        (episode.2.2.1 r (by omega) (by omega)) priority)) passed

/-- Priority resolves the initial-nonmaintenance alternative for this oriented
pair: the larger peer had already made its original empty-list departure before
the smaller publication. Its continuous departed suffix excludes intervening
maintenance departures, failures and replacement requests. -/
theorem priority_original_departure {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish a b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (episode : Episode trace commands q a b) (priority : q.val < p.val)
    (passed : PassedPeer q (trace b p).pc) :
    ∃ d, d < a ∧ EmptyDeparture (trace d) (commands d) p ∧
      (∀ u, d < u → u ≤ b → Departed (trace u p).pc) ∧
      (∀ u, d < u → u ≤ b → exposed (trace u p).value = true) ∧
      (∀ u, d < u → u < b → commands u ≠ .fail p) := by
  have credit := priority_retains_credit valid bf episode priority passed
  have active := passed_active (credit (a + 1) (by omega) (by have := episode.1; omega))
  obtain ⟨d, da, exit, earlier⟩ := original_empty_departure valid
    (by have := episode.1; omega : a + 1 ≤ finish) (active_departed active)
  have kept : ∀ u, d < u → u ≤ b → Departed (trace u p).pc := by
    intro u du ub
    by_cases before : u ≤ a + 1
    · exact earlier u du before
    · exact active_departed (passed_active (credit u (by omega) ub))
  have ne : d ≠ a := by
    intro eq
    have commandsEqual : Command.run p = .run q := by
      rw [← exit.1, eq, episode.2.1.1]
    have same := Command.run.inj commandsEqual
    subst p
    omega
  refine ⟨d, by omega, exit, kept, ?_, ?_⟩
  · intro u du ub
    exact departed_exposed (reachable_coherent valid (by omega) p) (kept u du ub)
  · intro u du ub
    exact built_no_failure (q := q) (valid.2 u (by omega))
      (departed_built (kept (u + 1) (by omega) (by omega)) q)

end BuildHistory
end EconomicalSolutions.Algorithm7

#print axioms EconomicalSolutions.Algorithm7.BuildHistory.original_build_read
#print axioms EconomicalSolutions.Algorithm7.BuildHistory.listed_persists
#print axioms EconomicalSolutions.Algorithm7.BuildHistory.active_build_requires_nonexposure
#print axioms EconomicalSolutions.Algorithm7.BuildHistory.active_build_precedes_exposure
#print axioms EconomicalSolutions.Algorithm7.BuildHistory.original_departure_episode
#print axioms EconomicalSolutions.Algorithm7.BuildHistory.active_pair_build_departure_order
#print axioms EconomicalSolutions.Algorithm7.BuildHistory.original_build_start
#print axioms EconomicalSolutions.Algorithm7.BuildHistory.priority_original_departure
