import Peterson.EconomicalSolutions.Algorithm6History

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
namespace EconomicalSolutions.Algorithm6

/-- A stage 6 physical-register read, distinct from any projected clock read. -/
def MaintenanceRead {n : Nat} (s : State n) (command : Command n) (reader owner : Proc n) : Prop :=
  command = .run reader ∧ ∃ rest, (s reader).pc = .maintain (owner :: rest)

/-- After a lower write, another write requires passing this peer in a new
maintenance scan. Publish is included because its next step leaves lower. -/
def AwaitMaintenance {n : Nat} (owner : Proc n) : PC n → Prop
  | .test | .publish => True
  | .maintain rest => owner ∈ rest
  | _ => False

/-- Credit after the upper scan has passed the continuously occupied lower
position. The counter k counts lower writes since upper publication. -/
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

/-- Any changed occupied clock value comes from its real successful write. -/
theorem clock_change_is_write {m : Nat} {s : Algorithm3.State m} {i : Fin m}
    {old : Bool} {out : Algorithm3.Local} (own : (s i).q = some old)
    (step : Algorithm3.ordinary s i = some out) :
    out.q = some old ∨ ∃ bit, out.q = some bit ∧ bit ≠ old ∧
      (s i).pc = .tickWrite bit ∧ out.pc = .attempt := by
  cases hp : (s i).pc
  all_goals simp only [Algorithm3.ordinary, hp, own, bind, pure, Option.bind] at step
  all_goals repeat (split at step)
  all_goals simp_all <;> try (solve | aesop)
  all_goals rename_i bit different
  all_goals subst out; cases bit <;> cases old <;> simp_all

/-- Monitor for an interval with no maintenance read of owner. Before the
first lower write its private clock may contain arbitrary stale work. -/
def ObservationMonitor {n : Nat} (s : State n) (owner reader : Proc n) : Prop :=
  ∃ count cp upper lower k, (s owner).pc = .upperTick count cp ∧
    (s owner).value.clock = .upper upper ∧ (s reader).value.clock = .lower lower ∧
    k ≤ 1 ∧ (k = 1 → AwaitMaintenance owner (s reader).pc) ∧
    Credit reader.val count k upper lower cp

theorem lower_step_monitor {n : Nat} {cfg : Config n} {s : State n} {reader owner : Proc n}
    {out : Local n} {lower : Bool} (other : owner ≠ reader)
    (facts : LocalFacts (s reader)) (own : (s reader).value.clock = .lower lower)
    (after : ∃ bit, out.value.clock = .lower bit)
    (noRead : ¬ MaintenanceRead s (.run reader) reader owner)
    (step : ordinary cfg s reader = some out) :
    (out.value.clock = .lower lower ∧
      (AwaitMaintenance owner (s reader).pc → AwaitMaintenance owner out.pc)) ∨
    (∃ bit, out.value.clock = .lower bit ∧ bit ≠ lower ∧
      ¬ AwaitMaintenance owner (s reader).pc ∧ AwaitMaintenance owner out.pc ∧
      label s (.run reader) = .lowerTick reader) := by
  cases hp : (s reader).pc <;> simp only [LocalFacts, hp, own, visible] at facts
  all_goals try contradiction
  case maintain rest =>
    cases rest with
    | nil =>
      simp only [ordinary, hp, Option.some.injEq] at step; subst out
      exact Or.inl ⟨own, by simp [AwaitMaintenance, hp]⟩
    | cons q rest =>
      simp only [ordinary, hp, Option.some.injEq] at step; subst out
      left
      refine ⟨own, ?_⟩
      have ne : q ≠ owner := by intro eq; subst q; exact noRead ⟨rfl, rest, hp⟩
      simpa [AwaitMaintenance, hp, ne.symm] using
        (show owner ∈ q :: rest → owner ∈ rest from fun h => (List.mem_cons.mp h).resolve_left ne.symm)
  case lowerTick cp =>
    simp only [ordinary, hp] at step
    obtain ⟨c, clock, rfl⟩ := Option.map_eq_some_iff.mp step
    have co := clock_change_is_write (s := fun j =>
      ⟨clockValue s j, if j = position reader false then cp else .idle⟩)
      (i := position reader false) (old := lower)
      (by simp [clockValue, position, own]) clock
    rcases co with same | ⟨bit, tag, ne, pc, done⟩
    · left
      exact ⟨by simp [same, clockTag], by simp [AwaitMaintenance, hp]⟩
    · right
      simp only [ite_true] at pc
      exact ⟨bit, by simp [tag, clockTag], ne, by simp [AwaitMaintenance, hp],
        by simp [done, AwaitMaintenance], by simp [label, hp, pc]⟩
  case test =>
    simp only [ordinary, hp, Option.some.injEq] at step; subst out
    left
    refine ⟨own, ?_⟩
    dsimp only
    split
    · simp [AwaitMaintenance]
    · intro _; exact (cfg.complete reader owner).mpr other
  case publish =>
    simp only [ordinary, hp, Option.some.injEq] at step; subst out
    simp at after
  case enter | cs | release => simp_all

def ClockWrite : Algorithm3.PC → Bool
  | .tickWrite _ => true
  | _ => false

/-- The upper actor consumes credit using its exact projected clock step. -/
theorem upper_step_monitor {n : Nat} {cfg : Config n} {s : State n} {owner reader : Proc n}
    {out : Local n} (other : owner ≠ reader) (monitor : ObservationMonitor s owner reader)
    (step : ordinary cfg s owner = some out) :
    ObservationMonitor (setLocal s owner out) owner reader := by
  obtain ⟨count, cp, upper, lower, k, pc, own, peer, bound, waiting, credit⟩ := monitor
  simp only [ordinary, pc] at step
  obtain ⟨c, clock, rfl⟩ := Option.map_eq_some_iff.mp step
  have co := clock_credit_step (s := fun j =>
    ⟨clockValue s j, if j = position owner true then cp else .idle⟩)
    (i := position owner true) (j := position reader false) (count := count) (k := k)
    (upper := upper) (lower := lower) (by simp [position]; omega)
    (by simp [clockValue, position, own]) (by simp [clockValue, position, peer])
    (by simpa [position] using credit) clock
  obtain ⟨bit, tag, credit'⟩ := co
  have belowThree : ¬ (ClockWrite cp = true ∧ count + 1 = 3) := by
    intro ⟨write, third⟩
    cases cp <;> simp only [ClockWrite, Bool.false_eq_true] at write
    have passed : Passed count k upper lower := credit.2.2
    have := passed.1
    omega
  simp only [ite_true] at credit'
  refine ⟨(if ClockWrite cp then count + 1 else count),
    c.pc, bit, lower, k, ?_, ?_, ?_, bound, ?_, ?_⟩
  · simp only [setLocal_self, Bool.and_eq_true, decide_eq_true_eq]
    change (if ClockWrite cp = true ∧ count + 1 = 3 then _ else _) = _
    simp only [belowThree, ↓reduceIte]
    cases cp <;> rfl
  · simp [tag, clockTag]
  · simpa [other.symm] using peer
  · simpa [other.symm] using waiting
  · cases cp <;> simpa [position, ClockWrite] using credit'

/-- Other actors only change their own register and private work. -/
theorem next_observation_monitor {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {owner reader : Proc n}
    (reach : Reachable cfg s) (other : owner ≠ reader)
    (monitor : ObservationMonitor s owner reader)
    (upperAfter : ∃ bit, (t owner).value.clock = .upper bit)
    (lowerAfter : ∃ bit, (t reader).value.clock = .lower bit)
    (noRead : ¬ MaintenanceRead s command reader owner)
    (step : next cfg s command = some t) : ObservationMonitor t owner reader := by
  cases command with
  | stutter => have eq := Option.some.inj step; simpa [← eq] using monitor
  | run actor =>
    obtain ⟨out, ordinaryStep, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases oa : owner = actor
    · subst actor; exact upper_step_monitor other monitor ordinaryStep
    · by_cases ra : reader = actor
      · subst actor
        obtain ⟨count, cp, upper, lower, k, pc, own, peer, bound, waiting, credit⟩ := monitor
        have change := lower_step_monitor other ((reachable_invariant reach).localFacts reader)
          peer (by simpa using lowerAfter) noRead ordinaryStep
        rcases change with ⟨same, kept⟩ | ⟨bit, tag, ne, before, after, _⟩
        · exact ⟨count, cp, upper, lower, k, by simpa [other] using pc,
            by simpa [other] using own, by simpa using same, bound,
            by simpa using fun h => kept (waiting h), credit⟩
        · have zero : k = 0 := by by_contra nz; exact before (waiting (by omega))
          subst k
          exact ⟨count, cp, upper, bit, 1, by simpa [other] using pc,
            by simpa [other] using own, by simpa using tag, by omega,
            by simpa using after, credit_lower_change credit ne⟩
      · simpa [ObservationMonitor, oa, ra] using monitor
  | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals have oa : owner ≠ actor := by (intro eq; subst actor; simpa [reset, dead] using upperAfter)
    all_goals have ra : reader ≠ actor := by (intro eq; subst actor; simpa [reset, dead] using lowerAfter)
    all_goals simpa [ObservationMonitor, oa, ra] using monitor

/-- Upper publication starts a fresh count and attempt; no old tick cache
survives the joining write. -/
theorem upper_publication_starts {n : Nat} {cfg : Config n} {s t : State n}
    {owner : Proc n} {bit : Bool} (pc : (s owner).pc = .upperJoin (.joinWrite bit))
    (step : next cfg s (.run owner) = some t) :
    (t owner).pc = .upperTick 0 .attempt ∧ (t owner).value.clock = .upper bit := by
  simp only [next, ordinary, pc, clockInstruction, Algorithm3.ordinary, ite_true] at step
  split at step
  · simp only [Option.map_some, Option.some.injEq] at step
    subst t
    simp [clockTag]
  · simp at step

/-- Finite observation, with closed state intervals and open event endpoints.
Continuous upper/lower tags identify the surviving episodes; an off reset or
normal departure cannot be concealed inside either interval. -/
theorem three_tick_observation {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b : Nat} {owner reader : Proc n}
    {joinBit writeBit : Bool}
    (valid : ValidPrefix cfg trace commands finish) (ab : a < b) (bf : b < finish)
    (other : owner ≠ reader)
    (publication : (trace a owner).pc = .upperJoin (.joinWrite joinBit))
    (publishCommand : commands a = .run owner)
    (third : (trace b owner).pc = .upperTick 2 (.tickWrite writeBit))
    (_thirdCommand : commands b = .run owner)
    (upperEpisode : ∀ t, a < t → t ≤ b → ∃ bit, (trace t owner).value.clock = .upper bit)
    (lowerEpisode : ∀ t, a ≤ t → t ≤ b → ∃ bit, (trace t reader).value.clock = .lower bit) :
    ∃ r, a < r ∧ r < b ∧ MaintenanceRead (trace r) (commands r) reader owner ∧
      ∃ bit, (trace r owner).value.clock = .upper bit := by
  by_contra absent
  have noRead : ∀ r, a < r → r < b → ¬ MaintenanceRead (trace r) (commands r) reader owner := by
    intro r lo hi read
    exact absent ⟨r, lo, hi, read, upperEpisode r lo (by omega)⟩
  have start := upper_publication_starts publication (by simpa [publishCommand] using valid.2 a (by omega))
  have monitor : ∀ t, a + 1 ≤ t → t ≤ b → ObservationMonitor (trace t) owner reader := by
    intro t lo
    induction t, lo using Nat.le_induction with
    | base =>
      intro hi
      obtain ⟨lower, tag⟩ := lowerEpisode (a + 1) (by omega) hi
      exact ⟨0, .attempt, joinBit, lower, 0, start.1, start.2, tag,
        by omega, by omega, by simp [Credit, ScanCredit]⟩
    | succ t lo ih =>
      intro hi
      exact next_observation_monitor (prefix_reachable valid (by omega)) other
        (ih (by omega)) (upperEpisode (t + 1) (by omega) hi)
        (lowerEpisode (t + 1) (by omega) hi) (noRead t (by omega) (by omega))
        (valid.2 t (by omega))
  obtain ⟨count, cp, upper, lower, k, pc, _, _, bound, _, credit⟩ := monitor b (by omega) (le_refl _)
  rw [third] at pc
  cases pc
  have passed : Passed 2 k upper lower := credit.2.2
  have := passed.1
  omega

/-- During a lower episode only maintenance can remove identifiers; no ordinary
instruction can add one. -/
theorem lower_list_subset {n : Nat} {cfg : Config n} {s : State n} {reader : Proc n}
    {out : Local n} {bit : Bool} (facts : LocalFacts (s reader))
    (own : (s reader).value.clock = .lower bit) (step : ordinary cfg s reader = some out) :
    out.behind ⊆ (s reader).behind := by
  cases hp : (s reader).pc <;> simp only [LocalFacts, hp, own, visible] at facts
  all_goals try contradiction
  case maintain rest =>
    cases rest <;> simp only [ordinary, hp, Option.some.injEq] at step <;> subst out
    · exact Finset.Subset.refl _
    · dsimp only; split
      · exact Finset.Subset.refl _
      · exact Finset.erase_subset _ _
  case lowerTick cp =>
    simp only [ordinary, hp] at step
    obtain ⟨c, _, rfl⟩ := Option.map_eq_some_iff.mp step
    exact Finset.Subset.refl _
  case test | publish =>
    simp only [ordinary, hp, Option.some.injEq] at step; subst out
    exact Finset.Subset.refl _
  case enter | cs | release => simp_all

theorem next_lower_list_subset {n : Nat} {cfg : Config n} {s t : State n}
    {commands : Command n} {reader : Proc n} {bit : Bool}
    (reach : Reachable cfg s) (own : (s reader).value.clock = .lower bit)
    (step : next cfg s commands = some t) : (t reader).behind ⊆ (s reader).behind := by
  cases commands with
  | stutter => have eq := Option.some.inj step; simp [← eq]
  | run actor =>
    obtain ⟨out, ordinaryStep, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : reader = actor
    · subst actor
      simpa using lower_list_subset ((reachable_invariant reach).localFacts reader) own ordinaryStep
    · simp [eq]
  | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : reader = actor
    all_goals simp [eq, reset]

theorem maintenance_removes_upper {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {reader owner : Proc n} {bit : Bool}
    (read : MaintenanceRead s command reader owner) (upper : (s owner).value.clock = .upper bit)
    (step : next cfg s command = some t) : owner ∉ (t reader).behind := by
  obtain ⟨rfl, rest, pc⟩ := read
  simp only [next, ordinary, pc, upper, visible, Bool.false_eq_true, ↓reduceIte,
    Option.map_some, Option.some.injEq] at step
  subst t
  simp

/-- The identifier stays absent for the rest of this same lower episode. -/
theorem lower_absence_persists {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b : Nat} {owner reader : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (ab : a ≤ b) (bf : b ≤ finish)
    (lowerEpisode : ∀ t, a ≤ t → t ≤ b → ∃ bit, (trace t reader).value.clock = .lower bit)
    (absent : owner ∉ (trace a reader).behind) : owner ∉ (trace b reader).behind := by
  induction b, ab using Nat.le_induction with
  | base => exact absent
  | succ b lo ih =>
    have previous := ih (by omega) (by intro t lo hi; exact lowerEpisode t lo (by omega))
    obtain ⟨bit, tag⟩ := lowerEpisode b lo (by omega)
    exact fun mem => previous (next_lower_list_subset (prefix_reachable valid (by omega)) tag
      (valid.2 b (by omega)) mem)

/-- Frozen obligation (2): actual three upper writes force a stage 6 read,
and its deletion is already effective in the prestate of the third write.
Neither successful ticking nor fairness is assumed. -/
theorem three_tick_observation_removal {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b : Nat} {owner reader : Proc n}
    {joinBit writeBit : Bool}
    (valid : ValidPrefix cfg trace commands finish) (ab : a < b) (bf : b < finish)
    (other : owner ≠ reader)
    (publication : (trace a owner).pc = .upperJoin (.joinWrite joinBit))
    (publishCommand : commands a = .run owner)
    (third : (trace b owner).pc = .upperTick 2 (.tickWrite writeBit))
    (thirdCommand : commands b = .run owner)
    (upperEpisode : ∀ t, a < t → t ≤ b → ∃ bit, (trace t owner).value.clock = .upper bit)
    (lowerEpisode : ∀ t, a ≤ t → t ≤ b → ∃ bit, (trace t reader).value.clock = .lower bit) :
    (∃ r, a < r ∧ r < b ∧ MaintenanceRead (trace r) (commands r) reader owner ∧
      ∃ bit, (trace r owner).value.clock = .upper bit) ∧ owner ∉ (trace b reader).behind := by
  have observed := three_tick_observation valid ab bf other publication publishCommand third
    thirdCommand upperEpisode lowerEpisode
  refine ⟨observed, ?_⟩
  obtain ⟨r, lo, hi, read, bit, upper⟩ := observed
  apply lower_absence_persists valid (by omega : r + 1 ≤ b) (by omega)
    (by intro t rlo thi; exact lowerEpisode t (by omega) thi)
  exact maintenance_removes_upper read upper (valid.2 r (by omega))

end EconomicalSolutions.Algorithm6

#print axioms EconomicalSolutions.Algorithm6.clock_credit_step
#print axioms EconomicalSolutions.Algorithm6.clock_change_is_write
#print axioms EconomicalSolutions.Algorithm6.lower_step_monitor
#print axioms EconomicalSolutions.Algorithm6.next_observation_monitor
#print axioms EconomicalSolutions.Algorithm6.three_tick_observation
#print axioms EconomicalSolutions.Algorithm6.lower_absence_persists
#print axioms EconomicalSolutions.Algorithm6.three_tick_observation_removal
