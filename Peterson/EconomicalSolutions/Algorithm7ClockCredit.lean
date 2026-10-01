import Peterson.EconomicalSolutions.Algorithm7History

/-! Register coherence for the actual two-clock client. Pending writes retain
the other bit and prefix even after arbitrary interleavings. This is a prerequisite
for transporting clock credit, not a three-tick observation theorem. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm7

@[simp] theorem position_involution {n : Nat} (p : Proc n) (clock : Bool) :
    position (position p clock) clock = p := by
  cases clock <;> apply Fin.ext <;> simp [position]
  omega

theorem reversed_pair_order {n : Nat} {p q : Proc n} (other : p ≠ q) :
    ∃ clock, (position p clock).val < (position q clock).val := by
  by_cases less : p.val < q.val
  · exact ⟨false, less⟩
  · refine ⟨true, ?_⟩
    have ne : p.val ≠ q.val := fun eq => other (Fin.ext eq)
    simp only [position, ↓reduceIte]
    omega

def phaseLevel : Phase → Level
  | .one => .one | .maintain => .two | .three | .eligible => .three

def AtLevel (v : Value) (level : Level) : Prop := ∃ b0 b1, v = .live level b0 b1

def flipBit (v : Value) (clock : Bool) : Value :=
  match v with
  | .live _ b0 b1 => replaceBit v clock (!(if clock then b1 else b0))
  | _ => v

def PrefixPair (old new : Level) : Prop :=
  (old = .one ∧ new = .two) ∨ (old = .two ∧ new = .three)

/-- The reachable phase/register relation includes exact whole-value caches.
In particular a cached level-three prefix can still have a visible level two. -/
def Coherent (l : Local n) : Prop :=
  match l.pc with
  | .down | .idle | .join _ _ _ | .joinPublish _ _ => l.value = .dead
  | .attempt phase _ _ | .pairDone phase => AtLevel l.value (phaseLevel phase)
  | .tickWrite phase clock pending =>
      AtLevel l.value (phaseLevel phase) ∧ pending = flipBit l.value clock
  | .build _ => AtLevel l.value .one
  | .prefixRead level => ∃ old, PrefixPair old level ∧ AtLevel l.value old
  | .prefixWrite pending => ∃ old new b0 b1,
      PrefixPair old new ∧ l.value = .live old b0 b1 ∧ pending = .live new b0 b1
  | .delete _ | .add _ => AtLevel l.value .two
  | .eligible _ | .publish => AtLevel l.value .three
  | .enter | .cs | .release => l.value = .cs

@[simp] theorem coherent_reset {n : Nat} (down : Bool) : Coherent (reset (n := n) down) := by
  cases down <;> simp [Coherent, reset]

theorem coherent_afterAttempt {n : Nat} {v : Value} {phase : Phase} {clock : Bool}
    {l : Local n} (live : AtLevel v (phaseLevel phase)) :
    Coherent { l with value := v, pc := afterAttempt phase clock } := by
  cases clock <;> exact live

theorem clockInstruction_tickRead {n : Nat} {s : State n} {p : Proc n}
    {clock : Bool} {level : Level} {b0 b1 : Bool}
    (own : (s p).value = .live level b0 b1) :
    clockInstruction s p clock .tickRead =
      some ⟨some (if clock then b1 else b0), .tickWrite (!(if clock then b1 else b0))⟩ := by
  simp [clockInstruction, Algorithm3.ordinary, own, bit]

theorem ordinary_coherent {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {out : Local n} (before : Coherent (s p)) (step : ordinary cfg s p = some out) :
    Coherent out := by
  cases pc : (s p).pc
  all_goals simp only [Coherent, pc] at before
  case attempt phase clock cp =>
    cases cp
    case tickRead =>
      obtain ⟨b0, b1, own⟩ := before
      simp only [ordinary, pc, clockInstruction_tickRead own, bind, Option.bind,
        Option.some.injEq] at step
      subst out
      exact ⟨⟨b0, b1, own⟩, by rw [own]; rfl⟩
    all_goals simp only [ordinary, pc] at step
    all_goals obtain ⟨result, _, rfl⟩ := Option.map_eq_some_iff.mp step
    all_goals split <;> first | exact coherent_afterAttempt before | exact before
  case tickWrite phase clock pending =>
    obtain ⟨⟨b0, b1, own⟩, cached⟩ := before
    simp only [ordinary, pc, Option.some.injEq] at step
    subst out
    cases clock <;> simp [Coherent, afterAttempt, cached, own, flipBit, replaceBit, AtLevel]
  case prefixRead level =>
    obtain ⟨old, pair, b0, b1, own⟩ := before
    simp only [ordinary, pc, own, Option.some.injEq] at step
    subst out
    exact ⟨old, level, b0, b1, pair, rfl, rfl⟩
  case prefixWrite pending =>
    obtain ⟨old, new, b0, b1, pair, own, rfl⟩ := before
    rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals simp only [ordinary, pc, Option.some.injEq] at step
    all_goals subst out
    all_goals exact ⟨b0, b1, rfl⟩
  case' join clock first cp => cases cp
  case' pairDone phase => cases phase
  case' build rest => cases rest
  case' delete rest => cases rest
  case' add rest => cases rest
  case' eligible rest => cases rest
  all_goals simp only [ordinary, pc] at step
  all_goals try contradiction
  all_goals try (obtain ⟨result, _, rfl⟩ := Option.map_eq_some_iff.mp step)
  all_goals repeat (split at step)
  all_goals try contradiction
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try (exact coherent_reset false)
  all_goals simp_all [Coherent, phaseLevel, AtLevel, PrefixPair]
  all_goals split_ifs <;> simp_all [Coherent, phaseLevel, AtLevel, PrefixPair]

theorem next_coherent {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    (before : ∀ p, Coherent (s p)) (step : next cfg s c = some t) :
    ∀ p, Coherent (t p) := by
  intro p
  cases c with
  | stutter => have eq := Option.some.inj step; simpa [← eq] using before p
  | run actor =>
    obtain ⟨out, ordinaryStep, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor
      simpa using ordinary_coherent (before p) ordinaryStep
    · simpa [eq] using before p
  | request actor | complete actor | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; have h := before p; simp_all [Coherent, reset])
      | simpa [eq] using before p

theorem reachable_coherent {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish t : Nat}
    (valid : ValidPrefix cfg trace commands finish) (bound : t ≤ finish) :
    ∀ p, Coherent (trace t p) := by
  induction t with
  | zero => intro p; rw [valid.1]; exact coherent_reset false
  | succ t ih => exact next_coherent (ih (by omega)) (valid.2 t (by omega))

namespace ClockCredit

/-- Credit after the higher-position scan has passed the continuously occupied lower
position. The counter k counts lower writes since the start of the interval. -/
def Passed (count k : Nat) (upper lower : Bool) : Prop :=
  count ≤ k ∧ (count = k → upper ≠ lower)

def Sampled (count k : Nat) (upper lower sample : Bool) : Prop :=
  (count = k + 1 → sample = lower) ∧ (count = k → upper = lower → sample = lower)

/-- The actual descending cursor distinguishes an unread position, its cached
sample, and the part of the attempt after the comparison. -/
def ScanCredit (peer count k : Nat) (upper lower : Bool) : Algorithm3.PC → Prop
  | .attempt => True
  | .tickLower cursor _ => cursor < peer → Passed count k upper lower
  | .lowerOwn cursor sample =>
      (cursor < peer → Passed count k upper lower) ∧
      (cursor = peer → Sampled count k upper lower sample)
  | .tickUpper _ | .upperOwn _ _ | .tickRead | .tickWrite _ => Passed count k upper lower
  | _ => False

def Credit (peer count k : Nat) (upper lower : Bool) (pc : Algorithm3.PC) : Prop :=
  count ≤ k + 1 ∧ (count = k + 1 → upper = lower) ∧ ScanCredit peer count k upper lower pc

theorem sampled_pass {count k : Nat} {upper lower sample : Bool}
    (bound : count ≤ k + 1) (top : count = k + 1 → upper = lower)
    (sampled : Sampled count k upper lower sample) (different : sample ≠ upper) :
    Passed count k upper lower := by
  have ne : count ≠ k + 1 := by intro eq; exact different ((sampled.1 eq).trans (top eq).symm)
  refine ⟨by omega, ?_⟩
  intro eq same
  exact different ((sampled.2 eq same).trans same.symm)

theorem credit_lower_change {peer count : Nat} {upper lower new : Bool} {pc : Algorithm3.PC}
    (credit : Credit peer count 0 upper lower pc) (changed : new ≠ lower) :
    Credit peer count 1 upper new pc := by
  obtain ⟨bound, top, scan⟩ := credit
  have passed : Passed count 0 upper lower → Passed count 1 upper new := by
    intro h; exact ⟨by have := h.1; omega, by intro eq; have := h.1; omega⟩
  have sampled : ∀ sample, Sampled count 0 upper lower sample → Sampled count 1 upper new sample := by
    intro sample _
    refine ⟨by intro eq; omega, ?_⟩
    intro eq same
    exact (changed (same.symm.trans (top (by omega)))).elim
  refine ⟨by omega, by intro eq; omega, ?_⟩
  cases pc <;> simp only [ScanCredit] at scan ⊢
  all_goals first
    | exact ⟨fun h => passed (scan.1 h), fun h => sampled _ (scan.2 h)⟩
    | trivial
    | exact passed scan
    | exact fun h => passed (scan h)

theorem credit_tickLower {i m peer count k cursor : Nat} {upper lower : Bool} {observed : Bool}
    (_below : peer < i) (remaining : peer < cursor ∨ Passed count k upper lower) :
    ScanCredit peer count k upper lower (Algorithm3.tickLower i m cursor observed) := by
  unfold Algorithm3.tickLower
  split
  · simp only [ScanCredit]
    intro h
    rcases remaining with h' | h'
    · omega
    · exact h'
  · have passed : Passed count k upper lower := by rcases remaining with h | h; omega; exact h
    split <;> exact passed

theorem credit_tickUpper {i cursor peer count k : Nat} {upper lower : Bool}
    (passed : Passed count k upper lower) :
    ScanCredit peer count k upper lower (Algorithm3.tickUpper i cursor) := by
  unfold Algorithm3.tickUpper
  split <;> exact passed

/-- One instruction of the unchanged clock preserves the scan credit. It may
return from a failed comparison. Its only count increment is the actual write. -/
theorem clock_credit_step {m : Nat} {s : Algorithm3.State m} {i j : Fin m}
    {count k : Nat} {upper lower : Bool} {out : Algorithm3.Local}
    (below : j.val < i.val) (own : (s i).q = some upper) (peer : (s j).q = some lower)
    (credit : Credit j.val count k upper lower (s i).pc)
    (step : Algorithm3.ordinary s i = some out) :
    ∃ bit, out.q = some bit ∧ Credit j.val
      (if (match (s i).pc with | .tickWrite _ => true | _ => false) then count + 1 else count)
      k bit lower out.pc := by
  obtain ⟨bound, top, scan⟩ := credit
  cases hp : (s i).pc <;> simp only [hp, ScanCredit] at scan
  all_goals simp only [Algorithm3.ordinary, hp, own, bind, pure, Option.bind] at step
  case attempt =>
    simp only [Option.some.injEq] at step; subst out
    exact ⟨upper, rfl, bound, top, credit_tickLower below (Or.inl below)⟩
  case tickLower cursor observed =>
    split at step
    · rename_i valid
      cases sample : (s ⟨cursor, valid⟩).q with
      | none =>
        simp only [sample, bind, pure, Option.bind, Option.some.injEq] at step; subst out
        refine ⟨upper, rfl, bound, top, credit_tickLower below ?_⟩
        by_cases eq : cursor = j.val
        · have finEq : (⟨cursor, valid⟩ : Fin m) = j := Fin.ext eq
          simp [finEq, peer] at sample
        · by_cases lt : j.val < cursor
          · exact Or.inl lt
          · exact Or.inr (scan (by omega))
      | some bit =>
        simp only [sample, bind, pure, Option.bind, Option.some.injEq] at step; subst out
        refine ⟨upper, rfl, bound, top, scan, ?_⟩
        intro eq
        have finEq : (⟨cursor, valid⟩ : Fin m) = j := Fin.ext eq
        have bitEq : bit = lower := by simpa [finEq, peer] using sample.symm
        subst bit
        exact ⟨fun _ => rfl, fun _ _ => rfl⟩
    · contradiction
  case lowerOwn cursor sample =>
    by_cases eq : sample = upper
    · simp only [eq, ↓reduceIte, bind, pure, Option.bind, Option.some.injEq] at step; subst out
      exact ⟨upper, rfl, bound, top, trivial⟩
    · simp only [eq, ↓reduceIte, bind, pure, Option.bind, Option.some.injEq] at step; subst out
      refine ⟨upper, rfl, bound, top, credit_tickLower below ?_⟩
      by_cases before : j.val < cursor
      · exact Or.inl before
      · right
        by_cases same : cursor = j.val
        · exact sampled_pass bound top (scan.2 same) eq
        · exact scan.1 (by omega)
  case tickUpper cursor =>
    split at step
    · rename_i valid
      cases sample : (s ⟨cursor, valid⟩).q with
      | none =>
        simp only [sample, bind, pure, Option.bind, Option.some.injEq] at step; subst out
        exact ⟨upper, rfl, bound, top, credit_tickUpper scan⟩
      | some bit =>
        simp only [sample, bind, pure, Option.bind, Option.some.injEq] at step; subst out
        exact ⟨upper, rfl, bound, top, scan⟩
    · contradiction
  case upperOwn cursor sample =>
    split at step
    · simp only [bind, pure, Option.bind, Option.some.injEq] at step; subst out
      exact ⟨upper, rfl, bound, top, trivial⟩
    · simp only [bind, pure, Option.bind, Option.some.injEq] at step; subst out
      exact ⟨upper, rfl, bound, top, credit_tickUpper scan⟩
  case tickRead =>
    simp only [Option.some.injEq] at step; subst out
    exact ⟨upper, rfl, bound, top, scan⟩
  case tickWrite bit =>
    split at step
    · rename_i different
      simp only [Option.some.injEq] at step; subst out
      change ∃ v, some bit = some v ∧ Credit j.val (count + 1) k v lower .attempt
      refine ⟨bit, rfl, by have := scan.1; omega, ?_, trivial⟩
      intro eq
      have neq := scan.2 (by omega)
      cases bit <;> cases upper <;> cases lower <;> simp_all
    · contradiction


end ClockCredit

/-- The selected clock's control, including the actual whole-value write cache.
Other-clock work and non-clock local work sit between selected attempts. -/
def creditPC (l : Local n) (clock : Bool) : Algorithm3.PC :=
  match l.pc with
  | .attempt _ active cp => if active = clock then cp else .attempt
  | .tickWrite _ active pending =>
      if active = clock then
        match bit pending clock with | some b => .tickWrite b | none => .down
      else .attempt
  | _ => .attempt

def LocalCredit (l : Local n) (peer : Proc n) (clock : Bool)
    (count k : Nat) (lower : Bool) : Prop :=
  ∃ upper, bit l.value clock = some upper ∧
    ClockCredit.Credit (position peer clock).val count k upper lower (creditPC l clock)

/-- Physical reads are exactly the proceedings reads in the selected order.
The lower-position premise is checked in that clock's coordinates. -/
theorem clockInstruction_credit {n : Nat} {s : State n} {owner peer : Proc n}
    {clock : Bool} {cp : Algorithm3.PC} {count k : Nat} {upper lower : Bool}
    {out : Algorithm3.Local}
    (below : (position peer clock).val < (position owner clock).val)
    (own : bit (s owner).value clock = some upper)
    (other : bit (s peer).value clock = some lower)
    (credit : ClockCredit.Credit (position peer clock).val count k upper lower cp)
    (step : clockInstruction s owner clock cp = some out) :
    ∃ b, out.q = some b ∧ ClockCredit.Credit (position peer clock).val
      (if (match cp with | .tickWrite _ => true | _ => false) then count + 1 else count)
      k b lower out.pc := by
  have result := ClockCredit.clock_credit_step (i := position owner clock) (j := position peer clock)
    (count := count) (k := k) (upper := upper) (lower := lower)
    (s := fun j => ⟨bit (s (position j clock)).value clock,
      if j = position owner clock then cp else .idle⟩) below
    (by simpa using own) (by simpa using other) (by simpa using credit) step
  simpa only [ite_true] using result

theorem clockInstruction_keeps_bit {n : Nat} {s : State n} {p : Proc n}
    {clock : Bool} {cp : Algorithm3.PC} {upper : Bool} {out : Algorithm3.Local}
    (own : bit (s p).value clock = some upper)
    (notWrite : ∀ b, cp ≠ .tickWrite b)
    (step : clockInstruction s p clock cp = some out) : out.q = some upper := by
  cases cp
  all_goals simp only [clockInstruction, Algorithm3.ordinary, position_involution,
    ↓reduceIte, own, bind, pure, Option.bind] at step
  all_goals repeat (split at step)
  all_goals simp_all
  all_goals solve | aesop

@[simp] theorem creditPC_afterAttempt {n : Nat} (l : Local n) (phase : Phase)
    (active clock : Bool) : creditPC { l with pc := afterAttempt phase active } clock = .attempt := by
  cases active <;> cases clock <;> simp [creditPC, afterAttempt]

/-- A real selected-clock instruction before its whole-register write advances
the scan credit without counting a tick, including the separate caching read. -/
theorem attempt_preserves_credit {n : Nat} {cfg : Config n} {s t : State n}
    {owner peer : Proc n} {phase : Phase} {clock : Bool} {cp : Algorithm3.PC}
    {count k : Nat} {lower : Bool} (coherent : Coherent (s owner))
    (below : (position peer clock).val < (position owner clock).val)
    (peerValue : bit (s peer).value clock = some lower)
    (pc : (s owner).pc = .attempt phase clock cp)
    (credit : LocalCredit (s owner) peer clock count k lower)
    (step : next cfg s (.run owner) = some t) :
    LocalCredit (t owner) peer clock count k lower := by
  obtain ⟨upper, own, cr⟩ := credit
  have before : ClockCredit.Credit (position peer clock).val count k upper lower cp := by
    simpa [creditPC, pc] using cr
  cases cp
  case tickRead =>
    obtain ⟨b0, b1, value⟩ : AtLevel (s owner).value (phaseLevel phase) := by
      simpa [Coherent, pc] using coherent
    simp only [next, ordinary, pc, clockInstruction_tickRead value, bind, Option.bind,
      Option.map_some, Option.some.injEq] at step
    subst t
    refine ⟨upper, by simpa using own, before.1, before.2.1, ?_⟩
    cases clock <;> simpa [creditPC, value, replaceBit, bit, ClockCredit.ScanCredit] using before.2.2
  case tickWrite cached =>
    simp only [next, ordinary, pc, Option.map_map, Option.map_eq_some_iff] at step
    obtain ⟨out, clockStep, rfl⟩ := step
    have done : out.pc = .attempt := by
      simp only [clockInstruction, Algorithm3.ordinary, position_involution,
        ↓reduceIte, own, bind, pure, Option.bind] at clockStep
      split at clockStep
      · simp only [Option.some.injEq] at clockStep; subst out; rfl
      · contradiction
    refine ⟨upper, by simpa using own, before.1, before.2.1, ?_⟩
    simp [done, creditPC_afterAttempt, ClockCredit.ScanCredit]
  all_goals simp only [next, ordinary, pc, Option.map_map, Option.map_eq_some_iff] at step
  all_goals obtain ⟨out, clockStep, rfl⟩ := step
  all_goals have unchanged := clockInstruction_keeps_bit own (by intro b; simp) clockStep
  all_goals obtain ⟨b, bitEq, after⟩ := clockInstruction_credit below own peerValue before clockStep
  all_goals have eq : b = upper := Option.some.inj (bitEq.symm.trans unchanged)
  all_goals subst b
  all_goals refine ⟨upper, by simpa using own, ?_⟩
  all_goals by_cases returned : out.pc = .attempt
  all_goals simp [creditPC, returned, afterAttempt] at after ⊢
  all_goals cases clock <;> simpa using after

/-- The real cached tick writes its complement and preserves the other bit.
There is no independent field write or unvalidated stale cache in this result. -/
theorem coherent_tick_write {n : Nat} {cfg : Config n} {s t : State n} {p : Proc n}
    {phase : Phase} {clock : Bool} {pending : Value}
    (coherent : Coherent (s p)) (pc : (s p).pc = .tickWrite phase clock pending)
    (step : next cfg s (.run p) = some t) :
    ∃ b0 b1, (s p).value = .live (phaseLevel phase) b0 b1 ∧
      (t p).value = flipBit (s p).value clock ∧
      bit (t p).value clock = some (!(if clock then b1 else b0)) ∧
      bit (t p).value (!clock) = bit (s p).value (!clock) ∧
      (t p).pc = afterAttempt phase clock := by
  obtain ⟨⟨b0, b1, own⟩, cached⟩ :
      AtLevel (s p).value (phaseLevel phase) ∧ pending = flipBit (s p).value clock := by
    simpa [Coherent, pc] using coherent
  simp only [next, ordinary, pc, Option.map_some, Option.some.injEq] at step
  subst t
  refine ⟨b0, b1, own, by simpa using cached, ?_, ?_, by simp⟩
  all_goals cases clock <;> simp [cached, own, flipBit, replaceBit, bit]

/-- A real selected-clock write consumes one unit of scan credit. The lower
peer is sampled through the supplied historical credit, not sampled by the write.
No Algorithm 6 client restriction is used. -/
theorem tick_write_consumes_credit {n : Nat} {cfg : Config n} {s t : State n}
    {owner peer : Proc n} {phase : Phase} {clock : Bool} {pending : Value}
    {count k : Nat} {lower : Bool} (coherent : Coherent (s owner))
    (pc : (s owner).pc = .tickWrite phase clock pending)
    (credit : LocalCredit (s owner) peer clock count k lower)
    (step : next cfg s (.run owner) = some t) :
    LocalCredit (t owner) peer clock (count + 1) k lower := by
  obtain ⟨b0, b1, own, value, selected, _, control⟩ := coherent_tick_write coherent pc step
  have cached : pending = flipBit (s owner).value clock := by
    exact (show AtLevel (s owner).value (phaseLevel phase) ∧
      pending = flipBit (s owner).value clock from by simpa [Coherent, pc] using coherent).2
  obtain ⟨upper, upperEq, bound, top, scan⟩ := credit
  have old : upper = (if clock then b1 else b0) := by
    simpa [own, bit] using upperEq.symm
  have passed : ClockCredit.Passed count k upper lower := by
    cases clock <;> simpa [creditPC, pc, cached, own, flipBit, replaceBit, bit,
      ClockCredit.ScanCredit] using scan
  refine ⟨_, selected, ?_, ?_, ?_⟩
  · have := passed.1; omega
  · intro eq
    have different := passed.2 (by omega)
    have complement : (!upper) = lower := by
      cases upper <;> cases lower <;> first | rfl | exact False.elim (different rfl)
    simpa only [old] using complement
  · cases clock <;> simp [creditPC, control, afterAttempt, ClockCredit.ScanCredit]

/-- The peer's first actual selected-clock maintenance write grants the next
credit even when its scan and write cache were already in flight. -/
theorem maintenance_write_grants_credit {n : Nat} {cfg : Config n} {s t : State n}
    {owner peer : Proc n} {clock : Bool} {count : Nat} {lower : Bool}
    (different : owner ≠ peer) (coherent : Coherent (s peer))
    (peerValue : bit (s peer).value clock = some lower)
    (write : MaintenanceWrite s (.run peer) peer clock)
    (credit : LocalCredit (s owner) peer clock count 0 lower)
    (step : next cfg s (.run peer) = some t) :
    bit (t peer).value clock = some (!lower) ∧
      LocalCredit (t owner) peer clock count 1 (!lower) := by
  obtain ⟨_, pending, pc⟩ := write
  obtain ⟨b0, b1, value, _, selected, _, _⟩ := coherent_tick_write coherent pc step
  have lowerEq : lower = (if clock then b1 else b0) := by
    simpa [value, bit] using peerValue.symm
  refine ⟨by simpa only [← lowerEq] using selected, ?_⟩
  have same : t owner = s owner := by
    obtain ⟨out, _, rfl⟩ := Option.map_eq_some_iff.mp step
    simp [different]
  rw [same]
  obtain ⟨upper, own, before⟩ := credit
  exact ⟨upper, own, ClockCredit.credit_lower_change before
    (by cases lower <;> decide)⟩

/-- A pending write with at most one lower credit cannot be the third counted
write. The temporal argument identifying credits with peer writes is separate. -/
theorem pending_third_write_needs_two_credits {n : Nat} {s : State n}
    {owner peer : Proc n} {phase : Phase} {clock : Bool} {pending : Value}
    {k : Nat} {lower : Bool} (coherent : Coherent (s owner))
    (pc : (s owner).pc = .tickWrite phase clock pending)
    (credit : LocalCredit (s owner) peer clock 2 k lower) : 2 ≤ k := by
  obtain ⟨upper, _, _, _, scan⟩ := credit
  obtain ⟨⟨b0, b1, own⟩, cached⟩ :
      AtLevel (s owner).value (phaseLevel phase) ∧ pending = flipBit (s owner).value clock := by
    simpa [Coherent, pc] using coherent
  have passed : ClockCredit.Passed 2 k upper lower := by
    cases clock <;> simpa [creditPC, pc, cached, own, flipBit, replaceBit, bit,
      ClockCredit.ScanCredit] using scan
  exact passed.1

/-- During maintenance the only operation that changes a selected bit is
an actual maintenance write in that clock. Other-clock whole writes stutter. -/
theorem ordinary_maintenance_bit_change {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {clock : Bool} {out : Local n}
    (coherent : Coherent (s p)) (maintain : Maintaining (s p).pc)
    (step : ordinary cfg s p = some out)
    (changed : bit out.value clock ≠ bit (s p).value clock) :
    ∃ pending, (s p).pc = .tickWrite .maintain clock pending := by
  cases pc : (s p).pc <;> simp only [pc, Maintaining] at maintain
  case' attempt phase active cp => cases phase
  case' tickWrite phase active pending => cases phase
  case' pairDone phase => cases phase
  all_goals try contradiction
  case tickWrite.maintain =>
    obtain ⟨⟨b0, b1, own⟩, cached⟩ : AtLevel (s p).value .two ∧
        pending = flipBit (s p).value active := by
      simpa [Coherent, pc, phaseLevel] using coherent
    simp only [ordinary, pc, Option.some.injEq] at step
    subst out
    by_cases eq : active = clock
    · subst active; exact ⟨pending, rfl⟩
    · cases active <;> cases clock <;>
        simp_all [cached, own, flipBit, replaceBit, bit]
  case' attempt.maintain => cases cp
  case' delete rest => cases rest
  case' add rest => cases rest
  all_goals simp only [ordinary, pc] at step
  all_goals try (obtain ⟨result, _, rfl⟩ := Option.map_eq_some_iff.mp step)
  all_goals repeat (split at step)
  all_goals try contradiction
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try (exact (changed rfl).elim)
  all_goals simp only [bind, Option.bind_eq_some_iff] at step
  all_goals obtain ⟨result, _, step⟩ := step
  all_goals split at step
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at step
  all_goals subst out
  all_goals exact (changed rfl).elim

/-- Reset is a departure, never a maintenance clock change. The post-state
maintenance premise rules out own failure even if the identifier later restarts. -/
theorem next_maintenance_bit_change {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {p : Proc n} {clock : Bool}
    (coherent : Coherent (s p)) (before : Maintaining (s p).pc)
    (after : Maintaining (t p).pc) (step : next cfg s c = some t)
    (changed : bit (t p).value clock ≠ bit (s p).value clock) :
    MaintenanceWrite s c p clock := by
  cases c with
  | stutter => have eq := Option.some.inj step; exact (changed (by rw [← eq])).elim
  | run actor =>
    obtain ⟨out, ordinaryStep, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor
      exact ⟨rfl, ordinary_maintenance_bit_change coherent before ordinaryStep (by simpa using changed)⟩
    · exact (changed (by simp [eq])).elim
  | request actor | complete actor | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp_all [reset, Maintaining])
      | exact (changed (by simp [eq])).elim

/-- Bit changes now connect to the previously checked historical stage 7
barrier. This still requires two real changes; no three-tick oracle supplies them. -/
theorem two_maintenance_bit_changes_force_waiting {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish a b : Nat}
    {p q : Proc n} {clock : Bool} (valid : ValidPrefix cfg trace commands finish)
    (ab : a < b) (bf : b < finish) (other : q ≠ p)
    (maintain : ∀ r, a ≤ r → r ≤ b + 1 → Maintaining (trace r p).pc)
    (first : bit (trace (a + 1) p).value clock ≠ bit (trace a p).value clock)
    (second : bit (trace (b + 1) p).value clock ≠ bit (trace b p).value clock)
    (three : ∀ r, a < r → r < b → ∃ b0 b1, (trace r q).value = .live .three b0 b1) :
    ∃ r, a < r ∧ r < b ∧ AdditionRead (trace r) (commands r) p q ∧
      WaitingFor q (trace b p) ∧ ¬ PassedPeer q (trace b p).pc := by
  apply two_maintenance_writes_force_waiting valid ab bf other
  · exact next_maintenance_bit_change (reachable_coherent valid (by omega) p)
      (maintain a (by omega) (by omega)) (maintain (a + 1) (by omega) (by omega))
      (valid.2 a (by omega)) first
  · exact next_maintenance_bit_change (reachable_coherent valid (by omega) p)
      (maintain b (by omega) (by omega)) (maintain (b + 1) (by omega) (by omega))
      (valid.2 b bf) second
  · intro r lo hi; exact maintain r (by omega) (by omega)
  · exact three

end EconomicalSolutions.Algorithm7

#print axioms EconomicalSolutions.Algorithm7.reversed_pair_order
#print axioms EconomicalSolutions.Algorithm7.reachable_coherent
#print axioms EconomicalSolutions.Algorithm7.clockInstruction_credit
#print axioms EconomicalSolutions.Algorithm7.attempt_preserves_credit
#print axioms EconomicalSolutions.Algorithm7.coherent_tick_write
#print axioms EconomicalSolutions.Algorithm7.tick_write_consumes_credit
#print axioms EconomicalSolutions.Algorithm7.maintenance_write_grants_credit
#print axioms EconomicalSolutions.Algorithm7.pending_third_write_needs_two_credits
#print axioms EconomicalSolutions.Algorithm7.next_maintenance_bit_change
#print axioms EconomicalSolutions.Algorithm7.two_maintenance_bit_changes_force_waiting
