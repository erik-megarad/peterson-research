import Peterson.EconomicalSolutions.Algorithm6LowerRound
import Peterson.EconomicalSolutions.Algorithm6Observation

/-! Successful clock attempts and next upper write-or-failure under concrete
instruction scheduling. Finite lower activity derives a settled snapshot in
the no-outcome contradiction; arbitrary in-flight upper attempts are flushed
by finite rank before the fresh enabled attempt forces its actual write. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm6

/-- The actual proceedings guards for a fresh attempt. When no lower position
is occupied, every occupied upper position must agree with the caller. -/
def LowerPass {m : Nat} (q : Fin m → Option Bool) (i : Fin m) (b : Bool) : Prop :=
  ∀ j, j.val < i.val → ∀ v, q j = some v → v ≠ b

def UpperPass {m : Nat} (q : Fin m → Option Bool) (i : Fin m) (b : Bool) : Prop :=
  ∀ j, i.val < j.val → ∀ v, q j = some v → v = b

def EnabledSnapshot {m : Nat} (q : Fin m → Option Bool) (i : Fin m) (b : Bool) : Prop :=
  LowerPass q i b ∧ ((∃ j, j.val < i.val ∧ q j ≠ none) ∨ UpperPass q i b)

/-- Scan evidence after stale work has been flushed by starting a fresh attempt.
The Boolean cached by an own-read control is tied to the fixed snapshot. -/
def FreshScan {m : Nat} (q : Fin m → Option Bool) (i : Fin m) (b : Bool) : Algorithm3.PC → Prop
  | .attempt => EnabledSnapshot q i b
  | .tickLower j observed => j < i.val ∧ LowerPass q i b ∧
      (observed = true ∨ UpperPass q i b ∨ ∃ k, k.val ≤ j ∧ q k ≠ none)
  | .lowerOwn j sample => j < i.val ∧ LowerPass q i b ∧ sample ≠ b
  | .tickUpper j => i.val < j ∧ UpperPass q i b
  | .upperOwn j sample => i.val < j ∧ UpperPass q i b ∧ sample = b
  | .tickRead => True
  | .tickWrite v => v ≠ b
  | _ => False

private theorem fresh_lower {m : Nat} {q : Fin m → Option Bool} {i : Fin m} {b observed : Bool}
    {k : Nat} (bound : k ≤ i.val) (lower : LowerPass q i b)
    (witness : observed = true ∨ UpperPass q i b ∨ ∃ j, j.val < k ∧ q j ≠ none) :
    FreshScan q i b (Algorithm3.tickLower i.val m k observed) ∧
      Algorithm3.tickLower i.val m k observed ≠ .attempt := by
  unfold Algorithm3.tickLower
  split
  · constructor
    · refine ⟨by omega, lower, ?_⟩
      rcases witness with seen | upper | ⟨j, hi, occ⟩
      · exact Or.inl seen
      · exact Or.inr (Or.inl upper)
      · exact Or.inr (Or.inr ⟨j, by omega, occ⟩)
    · simp
  · split
    · exact ⟨trivial, by simp⟩
    · rename_i noRead
      have upper : UpperPass q i b := by
        rcases witness with seen | upper | ⟨j, hi, _⟩
        · simp [seen] at noRead
        · exact upper
        · omega
      have hi : i.val + 1 < m := by by_contra h; simp [h] at noRead
      exact ⟨⟨by omega, upper⟩, by simp⟩

private theorem fresh_upper {m : Nat} {q : Fin m → Option Bool} {i : Fin m} {b : Bool}
    {k : Nat} (upper : UpperPass q i b) :
    FreshScan q i b (Algorithm3.tickUpper i.val k) ∧
      Algorithm3.tickUpper i.val k ≠ .attempt := by
  unfold Algorithm3.tickUpper
  split
  · exact ⟨⟨by omega, upper⟩, by simp⟩
  · exact ⟨trivial, by simp⟩

/-- Every instruction of an enabled fresh attempt continues toward its cached
complement write; it cannot return via either refused guard. -/
theorem fixed_snapshot_step {m : Nat} {s : Algorithm3.State m} {i : Fin m}
    {q : Fin m → Option Bool} {b : Bool} {out : Algorithm3.Local}
    (snapshot : ∀ j, (s j).q = q j) (own : q i = some b)
    (fresh : FreshScan q i b (s i).pc)
    (notWrite : ∀ v, (s i).pc ≠ .tickWrite v)
    (step : Algorithm3.ordinary s i = some out) :
    FreshScan q i b out.pc ∧ out.pc ≠ .attempt := by
  have own' : (s i).q = some b := (snapshot i).trans own
  cases hp : (s i).pc <;> simp only [hp, FreshScan] at fresh
  all_goals simp only [Algorithm3.ordinary, hp, own', bind, pure, Option.bind] at step
  case attempt =>
    simp only [Option.some.injEq] at step; subst out
    exact fresh_lower le_rfl fresh.1 (by rcases fresh.2 with ex | upper; exact Or.inr (Or.inr ex); exact Or.inr (Or.inl upper))
  case tickLower j observed =>
    split at step
    · rename_i valid
      cases sample : (s ⟨j, valid⟩).q with
      | none =>
        simp only [sample, Option.some.injEq] at step; subst out
        apply fresh_lower (by omega) fresh.2.1
        rcases fresh.2.2 with seen | upper | ⟨k, bound, occ⟩
        · exact Or.inl seen
        · exact Or.inr (Or.inl upper)
        · refine Or.inr (Or.inr ⟨k, ?_, occ⟩)
          have ne : k.val ≠ j := by
            intro eq
            have keq : k = ⟨j, valid⟩ := Fin.ext eq
            exact occ (by rw [keq, ← snapshot]; exact sample)
          omega
      | some v =>
        simp only [sample, Option.some.injEq] at step; subst out
        exact ⟨⟨fresh.1, fresh.2.1, fresh.2.1 _ fresh.1 v ((snapshot _).symm.trans sample)⟩, by simp⟩
    · contradiction
  case lowerOwn j sample =>
    simp only [fresh.2.2, ↓reduceIte, Option.some.injEq] at step; subst out
    exact fresh_lower (by omega) fresh.2.1 (Or.inl rfl)
  case tickUpper j =>
    split at step
    · rename_i valid
      cases sample : (s ⟨j, valid⟩).q with
      | none =>
        simp only [sample, Option.some.injEq] at step; subst out
        exact fresh_upper fresh.2
      | some v =>
        simp only [sample, Option.some.injEq] at step; subst out
        exact ⟨⟨fresh.1, fresh.2, fresh.2 _ fresh.1 v ((snapshot _).symm.trans sample)⟩, by simp⟩
    · contradiction
  case upperOwn j sample =>
    simp only [fresh.2.2, ne_eq, not_true_eq_false, ↓reduceIte, Option.some.injEq] at step; subst out
    exact fresh_upper fresh.2.1
  case tickRead =>
    simp only [Option.some.injEq] at step; subst out
    exact ⟨by cases b <;> simp [FreshScan], by simp⟩
  case tickWrite v => exact (notWrite v hp).elim

/-- Maintenance flushes prior cached clock work and begins a fresh attempt. -/
def FreshLower {n : Nat} (q : Fin (2 * n) → Option Bool) (p : Proc n) (b : Bool) : PC n → Prop
  | .maintain _ => True
  | .lowerTick cp => FreshScan q (position p false) b cp
  | _ => False

theorem fresh_lower_ordinary {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {q : Fin (2 * n) → Option Bool} {b : Bool} {out : Local n}
    (snapshot : ∀ j, clockValue s j = q j) (own : q (position p false) = some b)
    (enabled : EnabledSnapshot q (position p false) b)
    (fresh : FreshLower q p b (s p).pc) (noTick : label s (.run p) ≠ .lowerTick p)
    (step : ordinary cfg s p = some out) : FreshLower q p b out.pc := by
  cases hp : (s p).pc <;> simp only [hp, FreshLower] at fresh
  case maintain rest =>
    cases rest <;> simp only [ordinary, hp, Option.some.injEq] at step
    all_goals subst out
    · exact enabled
    · trivial
  case lowerTick cp =>
    simp only [ordinary, hp] at step
    obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step
    subst out
    have result := fixed_snapshot_step (s := fun j => ⟨clockValue s j,
      if j = position p false then cp else .idle⟩) (i := position p false)
      snapshot own (by simpa using fresh)
      (by intro v eq; have pc : cp = .tickWrite v := by simpa using eq
          simp [label, hp, pc] at noTick) hc
    simp only [result.2, ↓reduceIte]
    exact result.1

theorem fresh_lower_next {n : Nat} {cfg : Config n} {s t : State n} {command : Command n}
    {p : Proc n} {q : Fin (2 * n) → Option Bool} {b : Bool}
    (snapshot : ∀ j, clockValue s j = q j) (own : q (position p false) = some b)
    (enabled : EnabledSnapshot q (position p false) b)
    (fresh : FreshLower q p b (s p).pc) (step : next cfg s command = some t)
    (noTick : label s command ≠ .lowerTick p) (noFail : label s command ≠ .fail p) :
    FreshLower q p b (t p).pc := by
  by_cases act : Acts command p
  · rcases act with rfl | rfl
    · obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp step
      simpa using fresh_lower_ordinary snapshot own enabled fresh noTick ho
    · exact (noFail rfl).elim
  · have live : (s p).pc ≠ .down := by intro eq; simp [eq, FreshLower] at fresh
    rw [next_live_unchanged step live act]
    exact fresh

/-- A completed fresh maintenance/attempt round against an enabled fixed
snapshot contains a real successful write. The snapshot is required only in
prestates through the return event, so the final complement write is allowed
to change it. Cached work before `begin` is unrestricted. -/
theorem fixed_snapshot_lower_round_ticks {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {begin finish : Nat} {q : Fin (2 * n) → Option Bool} {b : Bool}
    (order : begin ≤ finish) (fresh : (r.state begin p).pc = .maintain (cfg.order p))
    (snapshot : ∀ t, begin ≤ t → t ≤ finish → ∀ j, clockValue (r.state t) j = q j)
    (own : q (position p false) = some b) (enabled : EnabledSnapshot q (position p false) b)
    (episode : SameEpisodeUntil r p begin (finish + 1))
    (_command : r.command finish = .run p) (returned : (r.state (finish + 1) p).pc = .test) :
    ∃ tick, begin ≤ tick ∧ tick ≤ finish ∧ r.event tick = .lowerTick p := by
  classical
  by_contra missing
  have noTick : ∀ t, begin ≤ t → t ≤ finish → r.event t ≠ .lowerTick p := by
    intro t lo hi tick; exact missing ⟨t, lo, hi, tick⟩
  have monitor : ∀ t, begin ≤ t → t ≤ finish + 1 → FreshLower q p b (r.state t p).pc := by
    intro t lo hi
    induction t, lo using Nat.le_induction with
    | base => simp [fresh, FreshLower]
    | succ t lo ih =>
      exact fresh_lower_next (snapshot t lo (by omega)) own enabled (ih (by omega))
        (r.valid t) (noTick t lo (by omega)) (episode t lo (by omega))
  have impossible := monitor (finish + 1) (by omega) le_rfl
  simp [returned, FreshLower] at impossible

/-- A continuously lower peer cannot keep the same enabled clock snapshot
forever: an arbitrarily late fresh round forces its own successful tick.
This derives the necessary tick from instruction scheduling; it does not add
successful-guard fairness or erase an initially stale cached attempt. -/
theorem continuous_lower_enabled_ticks {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    {q : Fin (2 * n) → Option Bool} {b : Bool}
    (lower : ∀ t, start ≤ t → IsLower (r.state t p).value.clock)
    (snapshot : ∀ t, start ≤ t → ∀ j, clockValue (r.state t) j = q j)
    (own : q (position p false) = some b) (enabled : EnabledSnapshot q (position p false) b) :
    ∀ t, start ≤ t → ∃ tick, t < tick ∧ r.event tick = .lowerTick p := by
  intro t lo
  obtain ⟨begin, finish, tb, bf, fresh, episode, command, returned⟩ :=
    continuous_lower_rounds r fair lower t lo
  have noFail : r.event finish ≠ .fail p := by simp [Run.event, command, label]; split <;> simp
  obtain ⟨tick, bt, tf, event⟩ := fixed_snapshot_lower_round_ticks r bf fresh
    (by intro u bu _; exact snapshot u (by omega)) own enabled
    (by intro u bu uf; by_cases eq : u = finish; simpa [eq] using noFail
        exact episode u (by omega) (by omega)) command returned
  exact ⟨tick, by omega, event⟩

/-- A nonempty fixed clock vector always has an enabled fresh attempt under
ALL-upper ticking. The first occupied position can move when all agree;
otherwise the first position with a different bit can move. -/
theorem snapshot_has_enabled {m : Nat} (q : Fin m → Option Bool)
    (occupied : ∃ i b, q i = some b) :
    ∃ i b, q i = some b ∧ EnabledSnapshot q i b := by
  classical
  have ex : ∃ k, ∃ i : Fin m, i.val = k ∧ ∃ b, q i = some b := by
    obtain ⟨i, b, hi⟩ := occupied
    exact ⟨i.val, i, rfl, b, hi⟩
  obtain ⟨first, firstIndex, bit, firstBit⟩ := Nat.find_spec ex
  have minimal : ∀ j v, q j = some v → first.val ≤ j.val := by
    intro j v hj
    have := Nat.find_min' ex ⟨j, rfl, v, hj⟩
    omega
  by_cases different : ∃ j v, q j = some v ∧ v ≠ bit
  · have dex : ∃ k, ∃ j : Fin m, j.val = k ∧ ∃ v, q j = some v ∧ v ≠ bit := by
      obtain ⟨j, v, hj, ne⟩ := different
      exact ⟨j.val, j, rfl, v, hj, ne⟩
    obtain ⟨other, otherIndex, v, otherBit, ne⟩ := Nat.find_spec dex
    have before : first.val < other.val := by
      have le := minimal other v otherBit
      have neq : first.val ≠ other.val := by
        intro eq
        have eq' : first = other := Fin.ext eq
        have : bit = v := Option.some.inj (firstBit.symm.trans (eq' ▸ otherBit))
        exact ne this.symm
      omega
    refine ⟨other, v, otherBit, ?_, Or.inl ⟨first, before, by simp [firstBit]⟩⟩
    intro j hi w hj
    have same : w = bit := by
      by_contra nw
      have := Nat.find_min' dex ⟨j, rfl, w, hj, nw⟩
      omega
    exact fun eq => ne (eq ▸ same)
  · refine ⟨first, bit, firstBit, ?_, Or.inr ?_⟩
    · intro j hi v hj
      have := minimal j v hj
      omega
    · intro j _ v hj
      by_contra ne
      exact different ⟨j, v, hj, ne⟩

/-- If the top occupied caller is blocked on a fixed vector, a lower occupied
position has an enabled attempt. This includes mixed lower bits and the
proceedings all-upper test at the first occupied position. -/
theorem blocked_top_has_enabled_lower {m : Nat} {q : Fin m → Option Bool}
    {top : Fin m} {b : Bool} (own : q top = some b)
    (highest : ∀ j, top.val < j.val → q j = none)
    (blocked : ¬ EnabledSnapshot q top b) :
    ∃ i v, i.val < top.val ∧ q i = some v ∧ EnabledSnapshot q i v := by
  obtain ⟨i, v, value, enabled⟩ := snapshot_has_enabled q ⟨top, b, own⟩
  refine ⟨i, v, ?_, value, enabled⟩
  have notHigher : ¬ top.val < i.val := by intro hi; simp [highest i hi] at value
  have notSame : i.val ≠ top.val := by
    intro eq
    have eq' : i = top := Fin.ext eq
    subst i
    have bv : b = v := Option.some.inj (own.symm.trans value)
    exact blocked (by simpa [bv] using enabled)
  omega

/-- Under concrete admission exclusion, every occupied clock position other
than the owner's upper position is a real lower peer. -/
theorem held_clock_position {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) {owner : Proc n} {b : Bool}
    (held : Holding (s owner).pc) (upper : (s owner).value.clock = .upper b)
    {i : Fin (2 * n)} {v : Bool} (value : clockValue s i = some v) :
    i = position owner true ∨ ∃ peer, peer ≠ owner ∧
      i = position peer false ∧ (s peer).value.clock = .lower v := by
  unfold clockValue at value
  split at value
  · rename_i low
    let peer : Proc n := ⟨i.val, low⟩
    have tag : (s peer).value.clock = .lower v := by
      cases eq : (s peer).value.clock <;> simp_all [peer]
    have other : peer ≠ owner := by intro eq; simp [eq, upper] at tag
    exact Or.inr ⟨peer, other, Fin.ext (by simp [position, peer]), tag⟩
  · rename_i high
    let peer : Proc n := ⟨i.val - n, by omega⟩
    have tag : (s peer).value.clock = .upper v := by
      cases eq : (s peer).value.clock <;> simp_all [peer]
    have same : peer = owner := by
      by_contra ne
      exact held_peer_not_upper reach held ne (by simp [tag, IsUpper])
    left
    have vals : i.val - n = owner.val := congrArg Fin.val same
    apply Fin.ext
    simp only [position, ↓reduceIte]
    omega

/-- A blocked admitted upper snapshot has a concrete lower peer whose next
fresh clock attempt passes every guard if the snapshot remains unchanged. -/
theorem held_blocked_has_enabled_peer {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) {owner : Proc n} {b : Bool}
    (held : Holding (s owner).pc) (upper : (s owner).value.clock = .upper b)
    (blocked : ¬ EnabledSnapshot (clockValue s) (position owner true) b) :
    ∃ peer v, peer ≠ owner ∧ (s peer).value.clock = .lower v ∧
      EnabledSnapshot (clockValue s) (position peer false) v := by
  have own : clockValue s (position owner true) = some b := by
    simp [clockValue, position, upper]
  have highest : ∀ j, (position owner true).val < j.val → clockValue s j = none := by
    intro j hi
    cases value : clockValue s j with
    | none => rfl
    | some v =>
      rcases held_clock_position reach held upper value with eq | ⟨peer, _, eq, _⟩
      · subst j; omega
      · subst j
        simp [position] at hi
        have := peer.isLt
        omega
  obtain ⟨i, v, below, value, enabled⟩ := blocked_top_has_enabled_lower own highest blocked
  rcases held_clock_position reach held upper value with eq | ⟨peer, other, eq, tag⟩
  · subst i; omega
  · exact ⟨peer, v, other, tag, by simpa [eq] using enabled⟩

/-- An actual lower tick changes that physical position; cached writes are
checked against the current own bit by the unmodified interpreter. -/
theorem lower_tick_changes {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {p : Proc n} (step : next cfg s command = some t)
    (tick : label s command = .lowerTick p) :
    clockValue t (position p false) ≠ clockValue s (position p false) := by
  cases command with
  | stutter | fail q | restart q => simp [label] at tick
  | run actor =>
    cases hp : (s actor).pc <;> simp only [label, hp] at tick
    all_goals try contradiction
    case upperJoin cp => cases cp <;> simp at tick
    case upperTick count cp => cases cp <;> simp at tick
    case lowerTick cp =>
      cases cp <;> simp only at tick
      all_goals try contradiction
      rename_i v
      simp only [Label.lowerTick.injEq] at tick
      subst actor
      simp only [next, ordinary, hp] at step
      obtain ⟨out, hc, rfl⟩ := Option.map_eq_some_iff.mp step
      unfold clockInstruction at hc
      simp only [Algorithm3.ordinary, ↓reduceIte] at hc
      cases own : clockValue s (position p false) <;> simp only [own, bind, pure, Option.bind] at hc
      · contradiction
      · rename_i b
        split at hc <;> try contradiction
        rename_i ne
        simp only [Option.map_some, Option.some.injEq] at hc
        subst out
        simpa [clockValue, position, clockTag] using ne

/-- Concrete progress diagnostic: a held upper snapshot that fails its fresh
attempt guard cannot remain unchanged forever under protocol scheduling.
Some peer's fully fresh lower round forces a successful tick or an earlier
snapshot change. No eventual bit stability is assumed or concluded. -/
theorem held_blocked_snapshot_changes {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {owner : Proc n} {start : Nat} {b : Bool}
    (held : Holding (r.state start owner).pc)
    (upper : (r.state start owner).value.clock = .upper b)
    (blocked : ¬ EnabledSnapshot (clockValue (r.state start)) (position owner true) b) :
    ∃ finish, start ≤ finish ∧ ∃ j, clockValue (r.state finish) j ≠ clockValue (r.state start) j := by
  classical
  by_contra missing
  have snapshot : ∀ t, start ≤ t → ∀ j, clockValue (r.state t) j = clockValue (r.state start) j := by
    intro t lo j
    by_contra ne
    exact missing ⟨t, lo, j, ne⟩
  obtain ⟨peer, v, _, tag, enabled⟩ := held_blocked_has_enabled_peer (r.reachable start) held upper blocked
  have own : clockValue (r.state start) (position peer false) = some v := by
    simp [clockValue, position, tag]
  have lower : ∀ t, start ≤ t → IsLower (r.state t peer).value.clock := by
    intro t lo
    have value := (snapshot t lo (position peer false)).trans own
    simp only [clockValue, position, ↓reduceIte] at value
    cases ht : (r.state t peer).value.clock <;> simp_all [IsLower]
  obtain ⟨tick, lo, event⟩ := continuous_lower_enabled_ticks r fair lower snapshot own enabled start le_rfl
  have change := lower_tick_changes (r.valid tick) event
  exact change ((snapshot (tick + 1) (by omega) _).trans (snapshot tick (by omega) _).symm)

/-- With occupancy retained, a clock tag cannot change without its own
successful write. Joining controls retain their reviewed reachable shape. -/
theorem ordinary_retained_bit {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {out : Local n} {upper : Bool} {b c : Bool}
    (joins : JoinFacts (s p).pc) (facts : LocalFacts (s p))
    (before : (s p).value.clock = clockTag upper (some b))
    (after : out.value.clock = clockTag upper (some c))
    (step : ordinary cfg s p = some out)
    (noUpper : label s (.run p) ≠ .upperTick p)
    (noLower : label s (.run p) ≠ .lowerTick p) : b = c := by
  have tagInject : ∀ x y, clockTag upper (some x) = clockTag upper (some y) → x = y := by
    cases upper <;> simp [clockTag]
  cases hp : (s p).pc
  case' build rest => cases rest
  case' maintain rest => cases rest
  case' lowerJoin cp => cases cp
  all_goals simp only [ordinary, hp] at step
  all_goals try contradiction
  case request | acquire =>
    exact tagInject b c (before.symm.trans ((tournamentInstruction_fields step).1.symm.trans after))
  case upperJoin cp | upperTick count cp | lowerTick cp =>
    obtain ⟨outClock, hc, eq⟩ := Option.map_eq_some_iff.mp step
    subst out
    have own : clockValue s (position p upper) = some b := by
      cases upper <;> simp_all [clockValue, position, clockTag]
    have noWrite : ∀ v, cp ≠ .tickWrite v := by
      intro v eq
      first
      | (have j : Joining cp := by simpa [JoinFacts, hp] using joins
         simp [eq, Joining] at j)
      | (solve | simp [label, hp, eq] at noUpper)
      | (solve | simp [label, hp, eq] at noLower)
    all_goals cases upper
    all_goals simp only [clockTag, Bool.false_eq_true, ↓reduceIte] at before after own
    all_goals try (cases hq : outClock.q <;> simp_all [clockTag])
    all_goals have change := clock_change_is_write (s := fun j => ⟨clockValue s j,
      if j = position p _ then cp else .idle⟩) (i := position p _) (by simpa using own) hc
    all_goals rcases change with same | ⟨v, _, _, eq, _⟩
    all_goals first
      | exact (noWrite v eq).elim
      | (simp_all [clockTag])
  all_goals try (obtain ⟨outClock, hc, eq⟩ := Option.map_eq_some_iff.mp step; subst out)
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals first
    | exact tagInject b c (before.symm.trans after)
    | (cases upper <;> simp_all [clockTag, dead, LocalFacts, visible])

theorem next_retained_bit {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {p : Proc n} {upper : Bool} {b c : Bool}
    (reach : Reachable cfg s)
    (before : (s p).value.clock = clockTag upper (some b))
    (after : (t p).value.clock = clockTag upper (some c))
    (step : next cfg s command = some t)
    (noUpper : label s command ≠ .upperTick p)
    (noLower : label s command ≠ .lowerTick p) : b = c := by
  have tagInject : ∀ x y, clockTag upper (some x) = clockTag upper (some y) → x = y := by
    cases upper <;> simp [clockTag]
  cases command with
  | stutter =>
    have eq : s = t := Option.some.inj step
    exact tagInject b c (before.symm.trans (by simpa [eq] using after))
  | run actor =>
    obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor
      exact ordinary_retained_bit (reachable_joinFacts reach p) ((reachable_invariant reach).localFacts p)
        before (by simpa using after) ho noUpper noLower
    · exact tagInject b c (before.symm.trans (by simpa [eq] using after))
  | fail actor | restart actor =>
    simp only [next] at step
    split at step <;> try contradiction
    all_goals simp only [Option.some.injEq] at step; subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; cases upper <;> simp [clockTag, reset, dead] at after)
      | exact tagInject b c (before.symm.trans (by simpa [eq] using after))

private theorem position_value {n : Nat} {s : State n} {p : Proc n} {upper b : Bool}
    (value : clockValue s (position p upper) = some b) :
    (s p).value.clock = clockTag upper (some b) := by
  have high : ¬ n + p.val < n := by omega
  cases upper <;> simp [clockValue, position, high] at value
  all_goals cases tag : (s p).value.clock <;> simp_all [clockTag]

/-- Fixed occupancy plus absence of successful clock events preserves the
whole clock vector. Arbitrary stale controls are covered by real instructions. -/
theorem next_fixed_occupancy_no_ticks {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} (reach : Reachable cfg s) (step : next cfg s command = some t)
    (occupancy : ∀ j, clockValue t j = none ↔ clockValue s j = none)
    (noTicks : ∀ p, label s command ≠ .upperTick p ∧ label s command ≠ .lowerTick p) :
    ∀ j, clockValue t j = clockValue s j := by
  intro j
  have represented : ∃ p upper, j = position p upper := by
    by_cases low : j.val < n
    · exact ⟨⟨j.val, low⟩, false, Fin.ext (by simp [position])⟩
    · exact ⟨⟨j.val - n, by omega⟩, true, Fin.ext (by simp [position]; omega)⟩
  obtain ⟨p, upper, rfl⟩ := represented
  cases old : clockValue s (position p upper) with
  | none => exact (occupancy _).mpr old
  | some b =>
    cases new : clockValue t (position p upper) with
    | none => have := (occupancy _).mp new; simp [old] at this
    | some c =>
      have eq := next_retained_bit reach (position_value old) (position_value new) step (noTicks p).1 (noTicks p).2
      simp [eq]

/-- In the concrete retained occupied cohort, a blocked upper owner forces
some successful clock write at or after this time. The writer may be lower:
this does not yet prove the upper owner's next tick or its third tick. -/
theorem fixed_cohort_blocked_eventually_ticks {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {owner : Proc n} {start : Nat} {b : Bool}
    (held : Holding (r.state start owner).pc)
    (upper : (r.state start owner).value.clock = .upper b)
    (occupancy : ∀ t, start ≤ t → ∀ j,
      clockValue (r.state t) j = none ↔ clockValue (r.state start) j = none)
    (blocked : ¬ EnabledSnapshot (clockValue (r.state start)) (position owner true) b) :
    ∃ tick, start ≤ tick ∧ ∃ p, r.event tick = .upperTick p ∨ r.event tick = .lowerTick p := by
  classical
  by_contra missing
  have noTicks : ∀ t, start ≤ t → ∀ p,
      r.event t ≠ .upperTick p ∧ r.event t ≠ .lowerTick p := by
    intro t lo p
    exact ⟨fun event => missing ⟨t, lo, p, Or.inl event⟩,
      fun event => missing ⟨t, lo, p, Or.inr event⟩⟩
  have fixed : ∀ t, start ≤ t → ∀ j, clockValue (r.state t) j = clockValue (r.state start) j := by
    intro t lo
    induction t, lo using Nat.le_induction with
    | base => intro j; rfl
    | succ t lo ih =>
      intro j
      exact (next_fixed_occupancy_no_ticks (r.reachable t) (r.valid t)
        (by intro k; exact (occupancy (t + 1) (by omega) k).trans (occupancy t lo k).symm)
        (noTicks t lo) j).trans (ih j)
  obtain ⟨finish, lo, j, changed⟩ := held_blocked_snapshot_changes r fair held upper blocked
  exact changed (fixed finish lo j)

private theorem lower_position_none {n : Nat} (s : State n) (p : Proc n) :
    clockValue s (position p false) = none ↔ ¬ IsLower (s p).value.clock := by
  cases tag : (s p).value.clock <;> simp [clockValue, position, tag, IsLower]

private theorem upper_position_none {n : Nat} (s : State n) (p : Proc n) :
    clockValue s (position p true) = none ↔ ¬ IsUpper (s p).value.clock := by
  have high : ¬ n + p.val < n := by omega
  cases tag : (s p).value.clock <;> simp [clockValue, position, high, tag, IsUpper]

/-- The reviewed physical-peer stabilization yields fixed occupancy at every
virtual clock position while the admitted owner remains upper. Bits are free. -/
theorem held_upper_cohort_occupancy {n : Nat} {cfg : Config n} (r : Run cfg)
    (owner : Proc n) (start : Nat)
    (held : ∀ t, start ≤ t → Holding (r.state t owner).pc)
    (upper : ∀ t, start ≤ t → IsUpper (r.state t owner).value.clock) :
    ∃ stable, start ≤ stable ∧ ∀ t, stable ≤ t → ∀ j,
      clockValue (r.state t) j = none ↔ clockValue (r.state stable) j = none := by
  obtain ⟨stable, lo, cohort⟩ := held_cohort_stabilizes r owner start held
  refine ⟨stable, lo, ?_⟩
  intro t hi j
  have represented : ∃ p direction, j = position p direction := by
    by_cases low : j.val < n
    · exact ⟨⟨j.val, low⟩, false, Fin.ext (by simp [position])⟩
    · exact ⟨⟨j.val - n, by omega⟩, true, Fin.ext (by simp [position]; omega)⟩
  obtain ⟨p, direction, rfl⟩ := represented
  cases direction
  · rw [lower_position_none, lower_position_none]
    by_cases eq : p = owner
    · subst p
      have now := upper t (by omega)
      have old := upper stable lo
      cases ht : (r.state t owner).value.clock <;> cases hs : (r.state stable owner).value.clock
      all_goals simp_all [IsUpper, IsLower]
    · exact not_congr (cohort t hi p eq).1
  · rw [upper_position_none, upper_position_none]
    by_cases eq : p = owner
    · subst p; simp [upper t (by omega), upper stable lo]
    · simp [(cohort t hi p eq).2, (cohort stable le_rfl p eq).2]

/-- Restricted successful ticking for the actual retained-admission client.
After finitely many departures, every blocked upper snapshot is followed by
some real upper/lower tick. Peers outside the cohort may fail/restart freely.
The theorem does not identify the writer with the owner or rule out infinite
lower ticking while the owner is starved. -/
theorem held_blocked_cohort_ticks {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (owner : Proc n) (start : Nat)
    (held : ∀ t, start ≤ t → Holding (r.state t owner).pc)
    (upper : ∀ t, start ≤ t → IsUpper (r.state t owner).value.clock) :
    ∃ stable, start ≤ stable ∧ ∀ t, stable ≤ t → ∀ b,
      (r.state t owner).value.clock = .upper b →
      ¬ EnabledSnapshot (clockValue (r.state t)) (position owner true) b →
      ∃ tick, t ≤ tick ∧ ∃ p, r.event tick = .upperTick p ∨ r.event tick = .lowerTick p := by
  obtain ⟨stable, lo, occupancy⟩ := held_upper_cohort_occupancy r owner start held upper
  refine ⟨stable, lo, ?_⟩
  intro t hi b tag blocked
  exact fixed_cohort_blocked_eventually_ticks r fair (held t (by omega)) tag
    (by intro u tu j; exact (occupancy u (by omega) j).trans (occupancy t hi j).symm) blocked

/-- A fixed occupied peer constrains every fresh successful write to `target`.
For a lower barrier its bit is `target`; for an upper barrier its bit differs
from `target` and every position below the caller is empty. -/
def BarrierScan (i j : Nat) (below target bit : Bool) : Algorithm3.PC → Prop
  | .attempt => True
  | .tickLower cursor observed => cursor < i ∧
      (if below then cursor < j → bit ≠ target else observed = false)
  | .lowerOwn cursor sample => below = true ∧ cursor < i ∧
      (cursor < j → bit ≠ target) ∧ (cursor = j → sample = target)
  | .tickUpper cursor => if below then bit ≠ target else cursor < j → bit ≠ target
  | .upperOwn cursor sample => if below then bit ≠ target else
      (cursor < j → bit ≠ target) ∧ (cursor = j → sample ≠ target)
  | .tickRead | .tickWrite _ => bit ≠ target
  | _ => False

private theorem barrier_lower {m : Nat} {i j : Fin m} {below target bit observed : Bool}
    {cursor : Nat} (order : if below then j.val < i.val else i.val < j.val)
    (bound : cursor ≤ i.val)
    (remaining : if below then j.val < cursor ∨ bit ≠ target else observed = false) :
    BarrierScan i.val j.val below target bit (Algorithm3.tickLower i.val m cursor observed) := by
  unfold Algorithm3.tickLower
  split
  · refine ⟨by omega, ?_⟩
    cases below <;> simp_all
    intro h
    rcases remaining with h' | h'
    · omega
    · exact h'
  · rename_i zero
    cases below
    · simp only [Bool.false_eq_true, ↓reduceIte] at order remaining ⊢
      have wide : i.val + 1 < m := by have := j.isLt; omega
      simp [remaining, wide, BarrierScan]
      intro h
      have := j.isLt
      omega
    · simp only [↓reduceIte] at remaining
      have different : bit ≠ target := by rcases remaining with h | h; omega; exact h
      split <;> simpa [BarrierScan] using different

private theorem barrier_upper {m : Nat} {i j : Fin m} {below target bit : Bool}
    {cursor : Nat} (order : if below then j.val < i.val else i.val < j.val)
    (remaining : if below then bit ≠ target else j.val < cursor ∨ bit ≠ target) :
    BarrierScan i.val j.val below target bit (Algorithm3.tickUpper i.val cursor) := by
  unfold Algorithm3.tickUpper
  split
  · cases below <;> simp_all [BarrierScan]
    intro h
    rcases remaining with h' | h'
    · omega
    · exact h'
  · cases below <;> simp_all [BarrierScan]
    rcases remaining with h | h
    · omega
    · exact h

/-- The monitor follows actual separate peer reads, own reads and cached
writes. It allows arbitrary changes at every position other than the barrier. -/
theorem clock_barrier_step {m : Nat} {s : Algorithm3.State m} {i j : Fin m}
    {below target bit : Bool} {out : Algorithm3.Local}
    (order : if below then j.val < i.val else i.val < j.val)
    (own : (s i).q = some bit)
    (peer : (s j).q = some (if below then target else !target))
    (empty : below = false → ∀ k : Fin m, k.val < i.val → (s k).q = none)
    (monitor : BarrierScan i.val j.val below target bit (s i).pc)
    (step : Algorithm3.ordinary s i = some out) :
    ∃ b, out.q = some b ∧ BarrierScan i.val j.val below target b out.pc ∧
      (∀ v, (s i).pc = .tickWrite v → b = target) := by
  cases hp : (s i).pc <;> simp only [hp, BarrierScan] at monitor
  all_goals simp only [Algorithm3.ordinary, hp, own, bind, pure, Option.bind] at step
  case attempt =>
    simp only [Option.some.injEq] at step; subst out
    refine ⟨bit, rfl, barrier_lower order le_rfl ?_, by simp⟩
    cases below <;> simp_all
  case tickLower cursor observed =>
    split at step
    · rename_i valid
      cases sample : (s ⟨cursor, valid⟩).q with
      | none =>
        simp only [sample, Option.some.injEq] at step; subst out
        refine ⟨bit, rfl, barrier_lower order (by omega) ?_, by simp⟩
        cases below
        · exact monitor.2
        · simp only [↓reduceIte] at monitor ⊢
          by_cases h : j.val < cursor
          · exact Or.inl h
          · right
            have ne : cursor ≠ j.val := by
              intro eq
              have eq' : (⟨cursor, valid⟩ : Fin m) = j := Fin.ext eq
              simp [eq', peer] at sample
            exact monitor.2 (by omega)
      | some v =>
        simp only [sample, Option.some.injEq] at step; subst out
        have low : below = true := by
          cases below
          · have := empty rfl ⟨cursor, valid⟩ monitor.1
            simp [sample] at this
          · rfl
        subst below
        refine ⟨bit, rfl, ⟨rfl, monitor.1, monitor.2, ?_⟩, by simp⟩
        intro eq
        have eq' : (⟨cursor, valid⟩ : Fin m) = j := Fin.ext eq
        simpa [eq', peer] using sample.symm
    · contradiction
  case lowerOwn cursor sample =>
    have low := monitor.1
    subst below
    by_cases same : sample = bit
    · simp only [same, ↓reduceIte, Option.some.injEq] at step; subst out
      exact ⟨bit, rfl, trivial, by simp⟩
    · simp only [same, ↓reduceIte, Option.some.injEq] at step; subst out
      refine ⟨bit, rfl, barrier_lower order (by have := monitor.2.1; omega) ?_, by simp⟩
      simp only [↓reduceIte]
      by_cases before : j.val < cursor
      · exact Or.inl before
      · right
        by_cases eq : cursor = j.val
        · intro bad; exact same ((monitor.2.2.2 eq).trans bad.symm)
        · exact monitor.2.2.1 (by omega)
  case tickUpper cursor =>
    split at step
    · rename_i valid
      cases sample : (s ⟨cursor, valid⟩).q with
      | none =>
        simp only [sample, Option.some.injEq] at step; subst out
        refine ⟨bit, rfl, barrier_upper order ?_, by simp⟩
        cases below
        · simp only [Bool.false_eq_true, ↓reduceIte] at monitor ⊢
          by_cases h : j.val < cursor
          · exact Or.inl h
          · right
            have ne : cursor ≠ j.val := by
              intro eq
              have eq' : (⟨cursor, valid⟩ : Fin m) = j := Fin.ext eq
              simp [eq', peer] at sample
            exact monitor (by omega)
        · exact monitor
      | some v =>
        simp only [sample, Option.some.injEq] at step; subst out
        refine ⟨bit, rfl, ?_, by simp⟩
        cases below
        · refine ⟨monitor, ?_⟩
          intro eq
          have eq' : (⟨cursor, valid⟩ : Fin m) = j := Fin.ext eq
          have veq : v = !target := by simpa [eq', peer] using sample.symm
          cases target <;> simp_all
        · exact monitor
    · contradiction
  case upperOwn cursor sample =>
    by_cases same : sample = bit
    · simp only [same, ne_eq, not_true_eq_false, ↓reduceIte, Option.some.injEq] at step; subst out
      refine ⟨bit, rfl, barrier_upper order ?_, by simp⟩
      cases below
      · simp only [Bool.false_eq_true, ↓reduceIte] at monitor ⊢
        by_cases h : j.val < cursor
        · exact Or.inl h
        · right
          by_cases eq : cursor = j.val
          · simpa [same] using monitor.2 eq
          · exact monitor.1 (by omega)
      · exact monitor
    · simp only [same, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq] at step; subst out
      exact ⟨bit, rfl, trivial, by simp⟩
  case tickRead =>
    simp only [Option.some.injEq] at step; subst out
    exact ⟨bit, rfl, monitor, by simp⟩
  case tickWrite v =>
    split at step
    · rename_i ne
      simp only [Option.some.injEq] at step; subst out
      have eq : v = target := by
        cases v <;> cases bit <;> cases target
        all_goals simp_all only [ne_eq, Bool.false_eq_true, Bool.true_eq_false, not_true_eq_false, not_false_eq_true]
      exact ⟨v, rfl, trivial, by intro _ _; exact eq⟩
    · contradiction

/-- The barrier monitor extends over the concrete maintenance/test cycle. -/
def LowerBarrier {n : Nat} (p : Proc n) (j : Fin (2 * n))
    (below target bit : Bool) : PC n → Prop
  | .maintain _ | .test | .publish => True
  | .lowerTick cp => BarrierScan (position p false).val j.val below target bit cp
  | _ => False

private theorem lower_barrier_ordinary {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {j : Fin (2 * n)} {below target bit : Bool} {out : Local n}
    (order : if below then j.val < (position p false).val else (position p false).val < j.val)
    (own : (s p).value.clock = .lower bit)
    (peer : clockValue s j = some (if below then target else !target))
    (empty : below = false → ∀ k : Fin (2 * n), k.val < (position p false).val → clockValue s k = none)
    (monitor : LowerBarrier p j below target bit (s p).pc)
    (step : ordinary cfg s p = some out) (retained : IsLower out.value.clock) :
    ∃ b, out.value.clock = .lower b ∧ LowerBarrier p j below target b out.pc ∧
      (bit = target → b = target) ∧ (label s (.run p) = .lowerTick p → b = target) := by
  cases hp : (s p).pc <;> simp only [hp, LowerBarrier] at monitor
  case maintain rest =>
    cases rest <;> simp only [ordinary, hp, Option.some.injEq] at step
    all_goals subst out; exact ⟨bit, own, trivial, id, by simp [label, hp]⟩
  case test =>
    simp only [ordinary, hp, Option.some.injEq] at step; subst out
    refine ⟨bit, own, ?_, id, by simp [label, hp]⟩
    split <;> trivial
  case publish =>
    simp only [ordinary, hp, Option.some.injEq] at step; subst out
    simp [IsLower] at retained
  case lowerTick cp =>
    simp only [ordinary, hp] at step
    obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step
    subst out
    let clock : Algorithm3.State (2 * n) := fun k =>
      ⟨clockValue s k, if k = position p false then cp else .idle⟩
    have clockOwn : (clock (position p false)).q = some bit := by simp [clock, clockValue, position, own]
    have ci : Algorithm3.ordinary clock (position p false) = some c := hc
    obtain ⟨b, value, monitored, ticked⟩ := clock_barrier_step order clockOwn peer empty
      (by simpa [clock] using monitor) ci
    refine ⟨b, by simp [value, clockTag], ?_, ?_, ?_⟩
    · split
      · trivial
      · exact monitored
    · intro same
      rcases clock_change_is_write clockOwn ci with unchanged | ⟨v, _, _, write, _⟩
      · have : b = bit := Option.some.inj (value.symm.trans unchanged)
        exact this.trans same
      · exact ticked v write
    · intro event
      have write : ∃ v, cp = .tickWrite v := by
        cases cp <;> simp_all [label]
      obtain ⟨v, eq⟩ := write
      exact ticked v (by simp [clock, eq])

/-- After a fresh round starts, a fixed barrier permits at most one new
successful lower write: the monitor is preserved and its target is absorbing. -/
theorem lower_barrier_next {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {p : Proc n} {j : Fin (2 * n)} {below target bit : Bool}
    (order : if below then j.val < (position p false).val else (position p false).val < j.val)
    (own : (s p).value.clock = .lower bit)
    (peer : clockValue s j = some (if below then target else !target))
    (empty : below = false → ∀ k : Fin (2 * n), k.val < (position p false).val → clockValue s k = none)
    (monitor : LowerBarrier p j below target bit (s p).pc)
    (step : next cfg s command = some t) (retained : IsLower (t p).value.clock) :
    ∃ b, (t p).value.clock = .lower b ∧ LowerBarrier p j below target b (t p).pc ∧
      (bit = target → b = target) ∧ (label s command = .lowerTick p → b = target) := by
  by_cases act : Acts command p
  · rcases act with rfl | rfl
    · obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp step
      simpa using lower_barrier_ordinary order own peer empty monitor ho (by simpa using retained)
    · simp only [next] at step
      split at step <;> try contradiction
      simp only [Option.some.injEq] at step; subst t
      simp [reset, dead, IsLower] at retained
  · have live : (s p).pc ≠ .down := by intro eq; simp [eq, LowerBarrier] at monitor
    have unchanged := next_live_unchanged step live act
    refine ⟨bit, by simpa [unchanged] using own, by simpa [unchanged] using monitor, id, ?_⟩
    intro event
    have acting : Acts command p := by
      cases command with
      | stutter | fail q | restart q => simp [label] at event
      | run q =>
        left
        cases hp : (s q).pc <;> simp only [label, hp] at event
        all_goals try contradiction
        case upperJoin cp | upperTick k cp => cases cp <;> simp at event
        case lowerTick cp =>
          cases cp <;> simp at event
          subst q; rfl
    exact (act acting).elim

/-- A continuously lower caller with a fixed occupied barrier eventually
stops ticking. All stale work before an arbitrarily late fresh maintenance
round is unrestricted. Other peers may keep changing. -/
theorem continuous_lower_barrier_finitely_ticks {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {j : Fin (2 * n)}
    {below target : Bool} {start : Nat}
    (order : if below then j.val < (position p false).val else (position p false).val < j.val)
    (lower : ∀ t, start ≤ t → IsLower (r.state t p).value.clock)
    (peer : ∀ t, start ≤ t → clockValue (r.state t) j = some (if below then target else !target))
    (empty : below = false → ∀ t, start ≤ t → ∀ k : Fin (2 * n),
      k.val < (position p false).val → clockValue (r.state t) k = none) :
    ∃ stop, start ≤ stop ∧ ∀ t, stop ≤ t → r.event t ≠ .lowerTick p := by
  classical
  obtain ⟨begin, finish, sb, _, fresh, _, _, _⟩ := continuous_lower_rounds r fair lower start le_rfl
  have monitored : ∀ t, begin ≤ t → ∃ bit,
      (r.state t p).value.clock = .lower bit ∧ LowerBarrier p j below target bit (r.state t p).pc := by
    intro t lo
    induction t, lo using Nat.le_induction with
    | base =>
      have tag := lower begin (by omega)
      cases ht : (r.state begin p).value.clock <;> simp only [ht, IsLower] at tag
      exact ⟨_, rfl, by simp [fresh, LowerBarrier]⟩
    | succ t lo ih =>
      obtain ⟨bit, tag, mon⟩ := ih
      obtain ⟨b, value, monitor, _, _⟩ := lower_barrier_next order tag (peer t (by omega))
        (by intro h; exact empty h t (by omega)) mon (r.valid t) (lower (t + 1) (by omega))
      exact ⟨b, value, monitor⟩
  by_cases ticks : ∃ t, begin ≤ t ∧ r.event t = .lowerTick p
  · obtain ⟨tick, bt, event⟩ := ticks
    obtain ⟨bit, tag, mon⟩ := monitored tick bt
    obtain ⟨b, value, _, _, targetWrite⟩ := lower_barrier_next order tag (peer tick (by omega))
      (by intro h; exact empty h tick (by omega)) mon (r.valid tick) (lower (tick + 1) (by omega))
    have stable : ∀ t, tick + 1 ≤ t → (r.state t p).value.clock = .lower target := by
      intro t lo
      induction t, lo using Nat.le_induction with
      | base => simpa [targetWrite event] using value
      | succ t lo ih =>
        obtain ⟨v, tag, mon⟩ := monitored t (by omega)
        have eq : v = target := Tag.lower.inj (tag.symm.trans ih)
        obtain ⟨w, value, _, absorb, _⟩ := lower_barrier_next order tag (peer t (by omega))
          (by intro h; exact empty h t (by omega)) mon (r.valid t) (lower (t + 1) (by omega))
        simpa [absorb eq] using value
    refine ⟨tick + 1, by omega, ?_⟩
    intro t lo event
    have changed := lower_tick_changes (r.valid t) event
    apply changed
    simp [clockValue, position, stable t lo, stable (t + 1) (by omega)]
  · exact ⟨begin, by omega, fun t lo event => ticks ⟨t, lo, event⟩⟩

private theorem lower_tick_control {n : Nat} {s : State n} {command : Command n} {p : Proc n}
    (event : label s command = .lowerTick p) :
    command = .run p ∧ ∃ v, (s p).pc = .lowerTick (.tickWrite v) := by
  cases command with
  | stutter | fail q | restart q => simp [label] at event
  | run q =>
    cases hp : (s q).pc <;> simp only [label, hp] at event
    all_goals try contradiction
    case upperJoin cp | upperTick k cp => cases cp <;> simp at event
    case lowerTick cp =>
      cases cp <;> simp at event
      subst q
      exact ⟨rfl, _, hp⟩

private theorem lower_no_upper_tick {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) {command : Command n} {p : Proc n}
    (lower : IsLower (s p).value.clock) : label s command ≠ .upperTick p := by
  intro event
  cases command with
  | stutter | fail q | restart q => simp [label] at event
  | run q =>
    cases hp : (s q).pc <;> simp only [label, hp] at event
    all_goals try contradiction
    case upperJoin cp | lowerTick cp => cases cp <;> simp at event
    case upperTick k cp =>
      cases cp <;> simp at event
      subst q
      have facts := (reachable_invariant reach).localFacts p
      simp only [LocalFacts, hp] at facts
      cases tag : (s p).value.clock <;> simp_all [IsLower, visible]

private theorem continuous_lower_fixed {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {start : Nat}
    (lower : ∀ t, start ≤ t → IsLower (r.state t p).value.clock)
    (noTicks : ∀ t, start ≤ t → r.event t ≠ .lowerTick p) :
    ∀ t, start ≤ t → (r.state t p).value.clock = (r.state start p).value.clock := by
  intro t lo
  induction t, lo using Nat.le_induction with
  | base => rfl
  | succ t lo ih =>
    have before := lower t lo
    have after := lower (t + 1) (by omega)
    cases hb : (r.state t p).value.clock <;> simp only [hb, IsLower] at before
    cases ha : (r.state (t + 1) p).value.clock <;> simp only [ha, IsLower] at after
    rename_i b c
    have eq := next_retained_bit (upper := false) (r.reachable t) hb ha (r.valid t)
      (lower_no_upper_tick (r.reachable t) (lower t lo)) (noTicks t lo)
    exact (congrArg Tag.lower eq.symm).trans (hb.symm.trans ih)

/-- Fixed occupancy and an unchanging admitted upper bit rule out infinitely
many lower writes. The proof derives each lower bit's eventual stability in
position order, including the empty-cohort case; it assumes no stable lower bits. -/
theorem fixed_upper_lower_ticks_stop {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {owner : Proc n} {start : Nat} {bit : Bool}
    (upper : ∀ t, start ≤ t → (r.state t owner).value.clock = .upper bit)
    (occupancy : ∀ t, start ≤ t → ∀ j,
      clockValue (r.state t) j = none ↔ clockValue (r.state start) j = none) :
    ∃ stop, start ≤ stop ∧ ∀ t, stop ≤ t → ∀ p, r.event t ≠ .lowerTick p := by
  classical
  have lowerAt : ∀ p t, start ≤ t → (IsLower (r.state t p).value.clock ↔
      IsLower (r.state start p).value.clock) := by
    intro p t lo
    have h := occupancy t lo (position p false)
    simp only [lower_position_none] at h
    simpa only [not_iff_not] using h
  have stops : ∀ k, k ≤ n → ∃ stop, start ≤ stop ∧ ∀ t, stop ≤ t →
      ∀ p : Proc n, p.val < k → r.event t ≠ .lowerTick p := by
    intro k bound
    induction k with
    | zero => exact ⟨start, le_rfl, by intro t lo p h; omega⟩
    | succ k ih =>
      obtain ⟨cut, sc, previous⟩ := ih (by omega)
      let p : Proc n := ⟨k, by omega⟩
      by_cases occupied : IsLower (r.state start p).value.clock
      · have lower : ∀ t, start ≤ t → IsLower (r.state t p).value.clock :=
          fun t lo => (lowerAt p t lo).mpr occupied
        have result : ∃ stop, cut ≤ stop ∧ ∀ t, stop ≤ t → r.event t ≠ .lowerTick p := by
          by_cases smaller : ∃ q : Proc n, q.val < p.val ∧ IsLower (r.state start q).value.clock
          · obtain ⟨q, qp, qlow⟩ := smaller
            have qlower : ∀ t, cut ≤ t → IsLower (r.state t q).value.clock :=
              fun t lo => (lowerAt q t (by omega)).mpr qlow
            have fixed := continuous_lower_fixed r qlower (fun t lo => previous t lo q qp)
            have tag := qlower cut le_rfl
            cases hq : (r.state cut q).value.clock <;> simp only [hq, IsLower] at tag
            rename_i b
            apply continuous_lower_barrier_finitely_ticks r fair (j := position q false)
              (below := true) (target := b) (by simpa [position] using qp)
              (fun t lo => lower t (by omega))
            · intro t lo
              simp [clockValue, position, fixed t lo, hq]
            · simp
          · apply continuous_lower_barrier_finitely_ticks r fair (j := position owner true)
              (below := false) (target := !bit) (by simp [position]; omega)
              (fun t lo => lower t (by omega))
            · intro t lo
              have hi : ¬ n + owner.val < n := by omega
              simp [clockValue, position, hi, upper t (by omega)]
            · intro _ t lo j jp
              have small : j.val < n := by simp [position] at jp; omega
              let q : Proc n := ⟨j.val, small⟩
              have empty : ¬ IsLower (r.state t q).value.clock := by
                intro qlow
                exact smaller ⟨q, jp, (lowerAt q t (by omega)).mp qlow⟩
              have eq : j = position q false := Fin.ext (by simp [position, q])
              rw [eq, lower_position_none]
              exact empty
        obtain ⟨stop, cs, done⟩ := result
        refine ⟨stop, by omega, ?_⟩
        intro t lo q qk
        by_cases eq : q = p
        · simpa [eq] using done t lo
        · have ne : q.val ≠ k := by intro h; exact eq (Fin.ext h)
          exact previous t (by omega) q (by omega)
      · refine ⟨cut, sc, ?_⟩
        intro t lo q qk
        by_cases eq : q = p
        · subst q
          intro tick
          obtain ⟨_, v, pc⟩ := lower_tick_control tick
          have facts := (reachable_invariant (r.reachable t)).localFacts p
          simp only [LocalFacts, pc] at facts
          obtain ⟨b, tag⟩ := facts
          exact occupied ((lowerAt p t (by omega)).mp (by simp [tag, IsLower]))
        · have ne : q.val ≠ k := by intro h; exact eq (Fin.ext h)
          exact previous t lo q (by omega)
  obtain ⟨stop, lo, done⟩ := stops n le_rfl
  exact ⟨stop, lo, fun t hi p => done t hi p p.isLt⟩

private theorem continuous_upper_fixed {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {start : Nat}
    (upper : ∀ t, start ≤ t → IsUpper (r.state t p).value.clock)
    (noTicks : ∀ t, start ≤ t → r.event t ≠ .upperTick p) :
    ∀ t, start ≤ t → (r.state t p).value.clock = (r.state start p).value.clock := by
  intro t lo
  induction t, lo using Nat.le_induction with
  | base => rfl
  | succ t lo ih =>
    have before := upper t lo
    have after := upper (t + 1) (by omega)
    cases hb : (r.state t p).value.clock <;> simp only [hb, IsUpper] at before
    cases ha : (r.state (t + 1) p).value.clock <;> simp only [ha, IsUpper] at after
    rename_i b c
    have noLower : r.event t ≠ .lowerTick p := by
      intro event
      obtain ⟨_, v, pc⟩ := lower_tick_control event
      have facts := (reachable_invariant (r.reachable t)).localFacts p
      simp only [LocalFacts, pc] at facts
      obtain ⟨v, tag⟩ := facts
      simp [hb] at tag
    have eq := next_retained_bit (upper := true) (r.reachable t) hb ha (r.valid t) (noTicks t lo) noLower
    exact (congrArg Tag.upper eq.symm).trans (hb.symm.trans ih)

/-- There is no infinite lower-only ticking suffix beneath a retained,
occupied upper owner that never ticks. Both the occupied cohort and its bit
stability are derived; failures/restarts outside that cohort remain allowed.
This does not yet prove the owner's next write or third-write termination. -/
theorem held_no_upper_ticks_lower_stop {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (owner : Proc n) (start : Nat)
    (held : ∀ t, start ≤ t → Holding (r.state t owner).pc)
    (upper : ∀ t, start ≤ t → IsUpper (r.state t owner).value.clock)
    (noOwnerTicks : ∀ t, start ≤ t → r.event t ≠ .upperTick owner) :
    ∃ stop, start ≤ stop ∧ ∀ t, stop ≤ t → ∀ p, r.event t ≠ .lowerTick p := by
  obtain ⟨stable, ss, occupancy⟩ := held_upper_cohort_occupancy r owner start held upper
  have fixed := continuous_upper_fixed r upper noOwnerTicks
  have tag := upper start le_rfl
  cases hu : (r.state start owner).value.clock <;> simp only [hu, IsUpper] at tag
  rename_i bit
  obtain ⟨stop, lo, done⟩ := fixed_upper_lower_ticks_stop r fair (owner := owner) (start := stable)
    (bit := bit) (fun t hi => (fixed t (by omega)).trans hu) occupancy
  exact ⟨stop, by omega, done⟩


/-- Until its next successful write or failure, an upper ticking occurrence
keeps its original count and bit. The embedded clock control may be stale. -/
theorem next_upper_wait {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {p : Proc n} {count : Nat} {cp : Algorithm3.PC} {b : Bool}
    (pc : (s p).pc = .upperTick count cp) (own : (s p).value.clock = .upper b)
    (step : next cfg s command = some t)
    (noTick : label s command ≠ .upperTick p) (noFail : label s command ≠ .fail p) :
    (t p).value.clock = .upper b ∧ ∃ cp', (t p).pc = .upperTick count cp' ∧
      (Acts command p → cp' = .attempt ∨ clockRoundRank (2 * n) cp' < clockRoundRank (2 * n) cp) := by
  by_cases act : Acts command p
  · rcases act with rfl | rfl
    · obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp step
      simp only [ordinary, pc] at ho
      obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp ho
      subst out
      have noWrite : ∀ v, cp ≠ .tickWrite v := by
        intro v eq
        simp [label, pc, eq] at noTick
      have notSuccess : (match cp with | .tickWrite _ => true | _ => false) = false := by
        cases cp <;> first | rfl | exact (noWrite _ rfl).elim
      have same : c.q = some b := by
        have ownClock : clockValue s (position p true) = some b := by simp [clockValue, position, own]
        rcases clock_change_is_write (s := fun j => ⟨clockValue s j,
          if j = position p true then cp else .idle⟩) (i := position p true)
          (by simpa using ownClock) hc with same | ⟨v, _, _, write, _⟩
        · exact same
        · exact (noWrite v (by simpa using write)).elim
      refine ⟨by simp [same, clockTag], c.pc, by simp [notSuccess], ?_⟩
      intro _
      simpa using clock_round_step (s := fun j => ⟨clockValue s j,
        if j = position p true then cp else .idle⟩) (i := position p true) hc
    · exact (noFail rfl).elim
  · have unchanged := next_live_unchanged step (by simp [pc]) act
    exact ⟨by simpa [unchanged] using own, cp, by simpa [unchanged] using pc,
      fun h => (act h).elim⟩

/-- The embedded clock rank, used only while a fixed upper invocation remains. -/
def upperAttemptRank {n : Nat} : PC n → Nat
  | .upperTick _ cp => clockRoundRank (2 * n) cp
  | _ => 0

/-- An indefinitely waiting upper invocation reaches a fresh attempt after
any chosen cutoff. Its old cached attempt may return through a refused guard. -/
theorem continuous_upper_fresh_attempt {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {count start : Nat} {b : Bool}
    (waiting : ∀ t, start ≤ t → (r.state t p).value.clock = .upper b ∧
      ∃ cp, (r.state t p).pc = .upperTick count cp)
    (noTicks : ∀ t, start ≤ t → r.event t ≠ .upperTick p)
    (noFails : ∀ t, start ≤ t → r.event t ≠ .fail p) :
    ∃ fresh, start ≤ fresh ∧ (r.state fresh p).pc = .upperTick count .attempt := by
  classical
  by_contra missing
  apply fair_descent_impossible r fair p start (fun l => upperAttemptRank l.pc)
  · intro t lo
    obtain ⟨_, cp, pc⟩ := waiting t lo
    simp [pc, Protocol]
  · intro t lo act
    obtain ⟨own, cp, pc⟩ := waiting t lo
    obtain ⟨_, cp', nextpc, descent⟩ := next_upper_wait pc own (r.valid t) (noTicks t lo) (noFails t lo)
    rcases descent act with done | less
    · exact (missing ⟨t + 1, by omega, by simpa [done] using nextpc⟩).elim
    · simpa [pc, nextpc, upperAttemptRank] using less

/-- A fresh enabled upper attempt cannot wait forever on a fixed snapshot.
This is a contradiction helper; the final progress result derives the snapshot. -/
theorem fixed_snapshot_upper_cannot_wait {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {count start : Nat} {b : Bool}
    {q : Fin (2 * n) → Option Bool}
    (waiting : ∀ t, start ≤ t → (r.state t p).value.clock = .upper b ∧
      ∃ cp, (r.state t p).pc = .upperTick count cp)
    (fresh : (r.state start p).pc = .upperTick count .attempt)
    (snapshot : ∀ t, start ≤ t → ∀ j, clockValue (r.state t) j = q j)
    (own : q (position p true) = some b) (enabled : EnabledSnapshot q (position p true) b)
    (noTicks : ∀ t, start ≤ t → r.event t ≠ .upperTick p)
    (noFails : ∀ t, start ≤ t → r.event t ≠ .fail p) : False := by
  have advance : ∀ t, start ≤ t → ∀ cp,
      (r.state t p).pc = .upperTick count cp → FreshScan q (position p true) b cp →
      ∃ cp', (r.state (t + 1) p).pc = .upperTick count cp' ∧
        FreshScan q (position p true) b cp' ∧
        (Acts (r.command t) p → upperAttemptRank (r.state (t + 1) p).pc <
          upperAttemptRank (r.state t p).pc) := by
    intro t lo cp pc monitor
    by_cases act : Acts (r.command t) p
    · rcases act with run | fail
      · have step := r.valid t
        rw [run] at step
        obtain ⟨out, ho, eq⟩ := Option.map_eq_some_iff.mp step
        simp only [ordinary, pc] at ho
        obtain ⟨c, hc, outEq⟩ := Option.map_eq_some_iff.mp ho
        have noWrite : ∀ v, cp ≠ .tickWrite v := by
          intro v cpEq
          have no := noTicks t lo
          simp [Run.event, run, label, pc, cpEq] at no
        have notSuccess : (match cp with | .tickWrite _ => true | _ => false) = false := by
          cases cp <;> first | rfl | exact (noWrite _ rfl).elim
        have nextpc : (r.state (t + 1) p).pc = .upperTick count c.pc := by
          rw [← eq, ← outEq]; simp [notSuccess]
        have result := fixed_snapshot_step (s := fun j => ⟨clockValue (r.state t) j,
          if j = position p true then cp else .idle⟩) (i := position p true)
          (snapshot t lo) own (by simpa using monitor) (by simpa using noWrite) hc
        refine ⟨c.pc, nextpc, result.1, ?_⟩
        intro _
        have descent := (clock_round_step (s := fun j => ⟨clockValue (r.state t) j,
          if j = position p true then cp else .idle⟩) (i := position p true) hc).resolve_left result.2
        simpa [pc, nextpc, upperAttemptRank] using descent
      · exact (noFails t lo (by simp [Run.event, fail, label])).elim
    · have unchanged := next_live_unchanged (r.valid t) (by simp [pc]) act
      exact ⟨cp, by simpa [unchanged] using pc, monitor, fun h => (act h).elim⟩
  have monitored : ∀ t, start ≤ t → ∃ cp,
      (r.state t p).pc = .upperTick count cp ∧ FreshScan q (position p true) b cp := by
    intro t lo
    induction t, lo using Nat.le_induction with
    | base => exact ⟨.attempt, fresh, enabled⟩
    | succ t lo ih =>
      obtain ⟨cp, pc, mon⟩ := ih
      obtain ⟨cp', nextpc, nextmon, _⟩ := advance t lo cp pc mon
      exact ⟨cp', nextpc, nextmon⟩
  apply fair_descent_impossible r fair p start (fun l => upperAttemptRank l.pc)
  · intro t lo
    obtain ⟨_, cp, pc⟩ := waiting t lo
    simp [pc, Protocol]
  · intro t lo act
    obtain ⟨cp, pc, mon⟩ := monitored t lo
    obtain ⟨_, _, _, descent⟩ := advance t lo cp pc mon
    exact descent act


private theorem upper_tick_control {n : Nat} {s : State n} {command : Command n} {p : Proc n}
    (event : label s command = .upperTick p) :
    command = .run p ∧ ∃ count v, (s p).pc = .upperTick count (.tickWrite v) := by
  cases command with
  | stutter | fail q | restart q => simp [label] at event
  | run q =>
    cases hp : (s q).pc <;> simp only [label, hp] at event
    all_goals try contradiction
    case upperJoin cp | lowerTick cp => cases cp <;> simp at event
    case upperTick k cp =>
      cases cp <;> simp at event
      subst q
      exact ⟨rfl, k, _, hp⟩

def UpperWriteOutcome {n : Nat} {cfg : Config n} (r : Run cfg) (p : Proc n) (t : Nat) : Prop :=
  r.event t = .upperTick p ∨ r.event t = .fail p

/-- An occupied upper ticking occurrence reaches its own actual successful
write or failure. No fresh-attempt, stable-bit or successful-guard premise is
added. The stored count and initially cached control are unrestricted. -/
theorem upper_next_write_eventually {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {count start : Nat} {cp : Algorithm3.PC} {b : Bool}
    (pc : (r.state start p).pc = .upperTick count cp)
    (own : (r.state start p).value.clock = .upper b) :
    ∃ finish, start ≤ finish ∧ UpperWriteOutcome r p finish := by
  classical
  by_contra missing
  have noTicks : ∀ t, start ≤ t → r.event t ≠ .upperTick p := by
    intro t lo event; exact missing ⟨t, lo, Or.inl event⟩
  have noFails : ∀ t, start ≤ t → r.event t ≠ .fail p := by
    intro t lo event; exact missing ⟨t, lo, Or.inr event⟩
  have waiting : ∀ t, start ≤ t → (r.state t p).value.clock = .upper b ∧
      ∃ cp, (r.state t p).pc = .upperTick count cp := by
    intro t lo
    induction t, lo using Nat.le_induction with
    | base => exact ⟨own, cp, pc⟩
    | succ t lo ih =>
      obtain ⟨tag, cp', pc'⟩ := ih
      obtain ⟨tag', cp'', pc'', _⟩ := next_upper_wait pc' tag (r.valid t) (noTicks t lo) (noFails t lo)
      exact ⟨tag', cp'', pc''⟩
  have held : ∀ t, start ≤ t → Holding (r.state t p).pc := by
    intro t lo
    obtain ⟨_, cp', pc'⟩ := waiting t lo
    simp [pc', Holding]
  have upper : ∀ t, start ≤ t → IsUpper (r.state t p).value.clock := by
    intro t lo; simp [(waiting t lo).1, IsUpper]
  obtain ⟨stop, ss, stopped⟩ := held_no_upper_ticks_lower_stop r fair p start held upper noTicks
  obtain ⟨stable, sb, occupancy⟩ := held_upper_cohort_occupancy r p start held upper
  let cut := max stop stable
  have sc : start ≤ cut := ss.trans (Nat.le_max_left _ _)
  have noWrites : ∀ t, cut ≤ t → ∀ peer,
      r.event t ≠ .upperTick peer ∧ r.event t ≠ .lowerTick peer := by
    intro t lo peer
    refine ⟨?_, stopped t (by dsimp [cut] at lo; omega) peer⟩
    intro event
    obtain ⟨_, k, v, peerpc⟩ := upper_tick_control event
    have same : peer = p := holding_unique (r.reachable t)
      (by simp [peerpc, Holding]) (held t (by omega))
    subst peer
    exact noTicks t (by omega) event
  have fixed : ∀ t, cut ≤ t → ∀ j, clockValue (r.state t) j = clockValue (r.state cut) j := by
    intro t lo
    induction t, lo using Nat.le_induction with
    | base => intro j; rfl
    | succ t lo ih =>
      intro j
      exact (next_fixed_occupancy_no_ticks (r.reachable t) (r.valid t)
        (by intro k
            exact (occupancy (t + 1) (by dsimp [cut] at lo; omega) k).trans
              (occupancy t (by dsimp [cut] at lo; omega) k).symm)
        (noWrites t lo) j).trans (ih j)
  have enabled : EnabledSnapshot (clockValue (r.state cut)) (position p true) b := by
    by_contra blocked
    obtain ⟨finish, lo, j, changed⟩ := held_blocked_snapshot_changes r fair
      (held cut sc) (waiting cut sc).1 blocked
    exact changed (fixed finish lo j)
  obtain ⟨fresh, cf, freshpc⟩ := continuous_upper_fresh_attempt r fair (start := cut)
    (fun t lo => waiting t (by omega)) (fun t lo => noTicks t (by omega))
    (fun t lo => noFails t (by omega))
  exact fixed_snapshot_upper_cannot_wait r fair (start := fresh)
    (fun t lo => waiting t (by omega)) freshpc (fun t lo => fixed t (by omega))
    (by simp [clockValue, position, (waiting cut sc).1]) enabled
    (fun t lo => noTicks t (by omega)) (fun t lo => noFails t (by omega))

/-- The first upper write-or-failure belongs to the observed invocation and
original episode. Every prestate through the endpoint keeps the same count
and upper bit; earlier in-flight work is preserved, not restarted by fiat. -/
theorem upper_next_write_original_episode {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {count start : Nat} {cp : Algorithm3.PC} {b : Bool}
    (pc : (r.state start p).pc = .upperTick count cp)
    (own : (r.state start p).value.clock = .upper b) :
    ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
      UpperWriteOutcome r p finish ∧
      (∀ t, start ≤ t → t < finish → r.event t ≠ .upperTick p) ∧
      (∀ t, start ≤ t → t ≤ finish → (r.state t p).value.clock = .upper b ∧
        ∃ cp', (r.state t p).pc = .upperTick count cp') ∧
      (r.event finish = .upperTick p → r.command finish = .run p ∧
        ∃ v, (r.state finish p).pc = .upperTick count (.tickWrite v)) := by
  classical
  have ex := upper_next_write_eventually r fair pc own
  have first := Nat.find_spec ex
  have noOutcome : ∀ t, start ≤ t → t < Nat.find ex → ¬ UpperWriteOutcome r p t := by
    intro t lo hi outcome
    have := Nat.find_min' ex ⟨lo, outcome⟩
    omega
  have waiting : ∀ t, start ≤ t → t ≤ Nat.find ex → (r.state t p).value.clock = .upper b ∧
      ∃ cp', (r.state t p).pc = .upperTick count cp' := by
    intro t lo hi
    induction t, lo using Nat.le_induction with
    | base => exact ⟨own, cp, pc⟩
    | succ t lo ih =>
      obtain ⟨tag, cp', pc'⟩ := ih (by omega)
      obtain ⟨tag', cp'', pc'', _⟩ := next_upper_wait pc' tag (r.valid t)
        (fun h => noOutcome t lo (by omega) (Or.inl h))
        (fun h => noOutcome t lo (by omega) (Or.inr h))
      exact ⟨tag', cp'', pc''⟩
  refine ⟨Nat.find ex, first.1, ?_, first.2, ?_, waiting, ?_⟩
  · intro t lo hi bad; exact noOutcome t lo hi (Or.inr bad)
  · intro t lo hi bad; exact noOutcome t lo hi (Or.inl bad)
  · intro tick
    obtain ⟨run, k, v, write⟩ := upper_tick_control tick
    obtain ⟨_, cp', pc'⟩ := waiting _ first.1 le_rfl
    have eq : k = count := (PC.upperTick.inj (write.symm.trans pc')).1
    exact ⟨run, v, by simpa [eq] using write⟩

end EconomicalSolutions.Algorithm6

#print axioms EconomicalSolutions.Algorithm6.fixed_snapshot_step
#print axioms EconomicalSolutions.Algorithm6.fixed_snapshot_lower_round_ticks
#print axioms EconomicalSolutions.Algorithm6.held_blocked_has_enabled_peer
#print axioms EconomicalSolutions.Algorithm6.held_blocked_snapshot_changes




#print axioms EconomicalSolutions.Algorithm6.fixed_cohort_blocked_eventually_ticks

#print axioms EconomicalSolutions.Algorithm6.held_blocked_cohort_ticks

#print axioms EconomicalSolutions.Algorithm6.clock_barrier_step
#print axioms EconomicalSolutions.Algorithm6.continuous_lower_barrier_finitely_ticks
#print axioms EconomicalSolutions.Algorithm6.fixed_upper_lower_ticks_stop
#print axioms EconomicalSolutions.Algorithm6.held_no_upper_ticks_lower_stop

#print axioms EconomicalSolutions.Algorithm6.next_upper_wait
#print axioms EconomicalSolutions.Algorithm6.continuous_upper_fresh_attempt
#print axioms EconomicalSolutions.Algorithm6.fixed_snapshot_upper_cannot_wait
#print axioms EconomicalSolutions.Algorithm6.upper_next_write_eventually
#print axioms EconomicalSolutions.Algorithm6.upper_next_write_original_episode

namespace EconomicalSolutions.Algorithm6

/-- Reaching the attempt control from joining means an occupied publication
has actually executed in the proceedings interpreter. -/
private theorem clock_join_attempt_occupied {m : Nat} {s : Algorithm3.State m}
    {i : Fin m} {out : Algorithm3.Local} (joining : Joining (s i).pc)
    (step : Algorithm3.ordinary s i = some out) (attempt : out.pc = .attempt) :
    ∃ b, out.q = some b := by
  cases hp : (s i).pc <;> simp only [hp, Joining] at joining
  all_goals simp only [Algorithm3.ordinary, hp] at step
  case joinWrite b =>
    split at step
    · simp only [Option.some.injEq] at step; subst out; exact ⟨b, rfl⟩
    · contradiction
  case joinLower j =>
    split at step
    · rename_i valid
      cases sample : (s ⟨j, valid⟩).q <;> simp only [sample, Option.some.injEq] at step
      all_goals subst out
      all_goals simp only [Algorithm3.joinLower] at attempt
      all_goals (try split_ifs at attempt) <;> contradiction
    · contradiction
  case joinUpper j =>
    split at step
    · rename_i valid
      cases sample : (s ⟨j, valid⟩).q <;> simp only [sample, Option.some.injEq] at step
      all_goals subst out
      all_goals (try split_ifs at attempt) <;> contradiction
    · contradiction

private def UpperTickOccupied {n : Nat} (l : Local n) : Prop :=
  ∀ count cp, l.pc = .upperTick count cp → ∃ b, l.value.clock = .upper b

private theorem ordinary_upper_tick_occupied {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {out : Local n} (joining : JoinFacts (s p).pc)
    (occupied : UpperTickOccupied (s p)) (step : ordinary cfg s p = some out) :
    UpperTickOccupied out := by
  intro count cp pc
  cases hp : (s p).pc
  case' build rest => cases rest
  case' maintain rest => cases rest
  case' lowerJoin clock => cases clock
  all_goals simp only [ordinary, hp] at step
  all_goals try contradiction
  case request | acquire =>
    obtain ⟨_, _, dest⟩ := tournamentInstruction_fields step
    rcases dest with dest | ⟨clock, dest⟩ <;> simp [dest] at pc
  case upperJoin clock =>
    obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step
    subst out
    dsimp at pc
    split at pc
    · rename_i attempt
      obtain ⟨b, tag⟩ := clock_join_attempt_occupied
        (s := fun j => ⟨clockValue s j, if j = position p true then clock else .idle⟩)
        (i := position p true) (by simpa [JoinFacts, hp] using joining) hc attempt
      exact ⟨b, by simp [tag, clockTag]⟩
    · contradiction
  case upperTick k clock =>
    obtain ⟨b, own⟩ := occupied k clock hp
    obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step
    subst out
    obtain ⟨v, tag⟩ := clock_occupied
      (s := fun j => ⟨clockValue s j, if j = position p true then clock else .idle⟩)
      (i := position p true) (b := b) (by simp [clockValue, position, own]) hc
    exact ⟨v, by simp [tag, clockTag]⟩
  all_goals try (obtain ⟨c, hc, eq⟩ := Option.map_eq_some_iff.mp step; subst out)
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals dsimp at pc
  all_goals repeat (split at pc)
  all_goals contradiction

/-- Occupancy needed by the next-write result is a reachability fact, including
when the chosen starting occurrence is partway through a cached attempt. -/
theorem reachable_upper_tick_occupied {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) {p : Proc n} {count : Nat} {cp : Algorithm3.PC}
    (pc : (s p).pc = .upperTick count cp) : ∃ b, (s p).value.clock = .upper b := by
  suffices all : ∀ p, UpperTickOccupied (s p) from all p count cp pc
  clear pc
  induction reach with
  | initial => intro p count cp pc; simp [initial, reset] at pc
  | @step s t a reach edge ih =>
    obtain ⟨command, step, _⟩ := edge
    cases command with
    | stutter => have eq : s = t := Option.some.inj step; simpa [← eq] using ih
    | run p =>
      obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp step
      intro q
      by_cases eq : q = p
      · subst q; simpa using ordinary_upper_tick_occupied (reachable_joinFacts reach p) (ih p) ho
      · simpa [eq] using ih q
    | fail p | restart p =>
      simp only [next] at step
      split at step <;> try contradiction
      all_goals simp only [Option.some.injEq] at step; subst t; intro q
      all_goals by_cases eq : q = p
      all_goals first
        | (subst q; simp [UpperTickOccupied, reset])
        | simpa [eq] using ih q

/-- A real first or second cached write publishes its candidate and advances
exactly one count. The next attempt is read from its actual poststate. -/
theorem upper_write_advances {n : Nat} {cfg : Config n} {s t : State n}
    {p : Proc n} {count : Nat} {bit old : Bool}
    (pc : (s p).pc = .upperTick count (.tickWrite bit))
    (own : (s p).value.clock = .upper old) (early : count < 2)
    (step : next cfg s (.run p) = some t) :
    (t p).pc = .upperTick (count + 1) .attempt ∧ (t p).value.clock = .upper bit := by
  have ownClock : clockValue s (position p true) = some old := by
    simp [clockValue, position, own]
  simp only [next, ordinary, pc, clockInstruction, Algorithm3.ordinary, ite_true,
    ownClock, bind, pure, Option.bind] at step
  have ne : count + 1 ≠ 3 := by omega
  simp only [ne, decide_false, Bool.and_false, Bool.false_eq_true, ite_false] at step
  split at step
  · simp only [Option.map_some, Option.some.injEq] at step
    subst t
    simp [clockTag]
  · simp at step

/-- Glue the two half-open failure-free intervals across the real intervening
publication/write event; its poststate is at the successor index. -/
private theorem same_episode_across_event {n : Nat} {cfg : Config n} (r : Run cfg)
    (p : Proc n) {a middle finish : Nat} (before : SameEpisodeUntil r p a middle)
    (noFail : r.event middle ≠ .fail p)
    (after : SameEpisodeUntil r p (middle + 1) finish) : SameEpisodeUntil r p a finish := by
  intro t lo hi
  by_cases lt : t < middle
  · exact before t lo lt
  · by_cases eq : t = middle
    · subst t; exact noFail
    · exact after t (by omega) hi

/-- At most the remaining three actual writes are composed. Own failure at
any stage closes this occurrence, and can never be replaced by a later request. -/
theorem upper_ticks_terminate {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {count start : Nat} {cp : Algorithm3.PC}
    (pc : (r.state start p).pc = .upperTick count cp) (bound : count < 3) :
    ∃ finish, start ≤ finish ∧ SameEpisodeUntil r p start finish ∧
      (ThirdUpperWrite r p finish ∨ r.event finish = .fail p) := by
  obtain ⟨b, own⟩ := reachable_upper_tick_occupied (r.reachable start) pc
  obtain ⟨write, lo, episode, outcome, _, waiting, written⟩ :=
    upper_next_write_original_episode r fair pc own
  rcases outcome with tick | fail
  · obtain ⟨command, bit, writepc⟩ := written tick
    by_cases last : count = 2
    · exact ⟨write, lo, episode, Or.inl ⟨command, bit, by simpa [last] using writepc⟩⟩
    · have early : count < 2 := by omega
      have post := upper_write_advances writepc (waiting write lo le_rfl).1 early
        (by simpa [command] using r.valid write)
      obtain ⟨finish, hi, rest, done⟩ := upper_ticks_terminate r fair post.1 (by omega)
      refine ⟨finish, by omega, ?_, done⟩
      exact same_episode_across_event r p episode (by simp [tick]) rest
  · exact ⟨write, lo, episode, Or.inr fail⟩
termination_by 3 - count

private theorem upper_join_control {n : Nat} {s : State n} {command : Command n} {p : Proc n}
    (event : label s command = .upperJoin p) :
    command = .run p ∧ ∃ bit, (s p).pc = .upperJoin (.joinWrite bit) := by
  cases command with
  | run q =>
    cases hp : (s q).pc
    case' upperJoin clock => cases clock
    case' upperTick count clock => cases clock
    case' lowerTick clock => cases clock
    all_goals simp [label, hp] at event
    all_goals subst q; exact ⟨rfl, _, hp⟩
  | fail q | restart q | stutter => simp [label] at event

/-- Frozen obligation (1): every original pre-third occurrence reaches its
actual third cached write or its own first failure, under protocol scheduling
alone. Initial joining, partial attempts and both intervening poststates are
included; no outer critical completion or tournament completion is assumed. -/
theorem upper_termination : UpperTerminationTarget := by
  intro n cfg r fair p start before
  cases hp : (r.state start p).pc <;> simp only [hp, BeforeThird] at before
  case upperTick count cp => exact upper_ticks_terminate r fair hp before
  case upperJoin cp =>
    obtain ⟨join, lo, episode, outcome, _⟩ := upper_join_original_episode r fair (p := p) (start := start)
      (by simp [hp, UpperJoining])
    rcases outcome with published | fail
    · obtain ⟨command, bit, joinpc⟩ := upper_join_control published
      have post := upper_publication_starts joinpc (by simpa [command] using r.valid join)
      obtain ⟨finish, hi, rest, done⟩ := upper_ticks_terminate r fair post.1 (by omega)
      refine ⟨finish, by omega, ?_, done⟩
      exact same_episode_across_event r p episode (by simp [published]) rest
    · exact ⟨join, lo, episode, Or.inr fail⟩

end EconomicalSolutions.Algorithm6

#print axioms EconomicalSolutions.Algorithm6.reachable_upper_tick_occupied
#print axioms EconomicalSolutions.Algorithm6.upper_write_advances
#print axioms EconomicalSolutions.Algorithm6.upper_ticks_terminate
#print axioms EconomicalSolutions.Algorithm6.upper_termination
