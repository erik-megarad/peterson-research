import MultiReaderAtomic.CausalTrace

/-! Chronological evaluation of an actual call, retaining a common final state.
This is proof evidence extracted from the endpoint protocol, never a premise of it. -/
namespace MultiReaderAtomic

abbrev TraceTo (v₀ : α) (s final : State n α) : Prop :=
  ∃ actions, (lts v₀).MTr s actions final

theorem traceTo_refl (v₀ : α) (s : State n α) : TraceTo v₀ s s :=
  ⟨[], Cslib.LTS.MTr.refl⟩

theorem traceTo_step {v₀ : α} {s s' final : State n α} {a : Action n}
    (step : Step v₀ s a s') (tail : TraceTo v₀ s' final) : TraceTo v₀ s final := by
  obtain ⟨actions, trace⟩ := tail
  exact ⟨a :: actions, Cslib.LTS.MTr.stepL step trace⟩

/-- A read's exact completion context, with its original witness history. -/
def ReadAt (v₀ : α) (final : State n α) (p : Process n) (call index : Nat)
    (r : Register n) (start : Nat) (next : Sample (Value α r) → Program n α)
    (sample : Sample (Value α r)) (s : State n α) : Prop :=
  TraceTo v₀ s final ∧
  s.threads p = some ⟨call, index, .reading r start next⟩ ∧
  Eligible (s.writes r) start s.clock sample.witness ∧
  Supplies (initialValue v₀ r) (s.writes r) sample

/-- A write's actual start and end contexts retain both value and caller. -/
def WriteStartsAt (v₀ : α) (final : State n α) (p : Process n) (call index : Nat)
    (r : Register n) (value : Value α r) (next : Program n α) (s : State n α) : Prop :=
  TraceTo v₀ s final ∧ s.threads p = some ⟨call, index, .ready (.write r value next)⟩

def WriteEndsAt (v₀ : α) (final : State n α) (p : Process n) (call index : Nat)
    (r : Register n) (start : Nat) (next : Program n α) (s : State n α) : Prop :=
  TraceTo v₀ s final ∧ s.threads p = some ⟨call, index, .writing r start next⟩

/-- Complete evaluation with strictly separated primitive intervals and actual
sample histories. Local operand choices retain either permitted order. -/
inductive ProgramExecution (v₀ : α) (final : State n α) (p : Process n)
    (call index : Nat) : Nat → Program n α → Option (Sample α) → Prop where
  | done {lower result} (bound : lower ≤ final.clock) :
      ProgramExecution v₀ final p call index lower (.done result) result
  | order {lower next result} (choice : Bool)
      (tail : ProgramExecution v₀ final p call index lower (next choice) result) :
      ProgramExecution v₀ final p call index lower (.order next) result
  | token {lower a b next result} (choice : Token) (ha : choice ≠ a) (hb : choice ≠ b)
      (tail : ProgramExecution v₀ final p call index lower (next choice) result) :
      ProgramExecution v₀ final p call index lower (.token a b next) result
  | read {lower r next result} (start : Nat) (s : State n α) (sample : Sample (Value α r))
      (beginBound : lower ≤ start) (interval : start < s.clock)
      (event : ReadAt v₀ final p call index r start next sample s)
      (tail : ProgramExecution v₀ final p call index (s.clock + 1) (next sample) result) :
      ProgramExecution v₀ final p call index lower (.read r next) result
  | write {lower r value next result} (s e : State n α)
      (beginBound : lower ≤ s.clock) (interval : s.clock < e.clock)
      (beginEvent : WriteStartsAt v₀ final p call index r value next s)
      (endEvent : WriteEndsAt v₀ final p call index r s.clock next e)
      (tail : ProgramExecution v₀ final p call index (e.clock + 1) next result) :
      ProgramExecution v₀ final p call index lower (.write r value next) result

theorem programExecution_mono {v₀ : α} {final : State n α} {p call index lower prog result}
    (h : ProgramExecution v₀ final p call index lower prog result) {earlier : Nat}
    (bound : earlier ≤ lower) : ProgramExecution v₀ final p call index earlier prog result := by
  induction h with
  | done h => exact .done (Nat.le_trans bound h)
  | order choice tail ih => exact .order choice (ih bound)
  | token choice ha hb tail ih => exact .token choice ha hb (ih bound)
  | read start s sample hb hi he tail => exact .read start s sample (Nat.le_trans bound hb) hi he tail
  | write s e hb hi hs he tail => exact .write s e (Nat.le_trans bound hb) hi hs he tail

def PhaseExecution (v₀ : α) (final : State n α) (p : Process n) (call index : Nat)
    (lower : Nat) (phase : Phase n α) (result : Option (Sample α)) : Prop :=
  match phase with
  | .ready prog => ProgramExecution v₀ final p call index lower prog result
  | .reading r start next => ∃ s sample, lower ≤ s.clock ∧
      ReadAt v₀ final p call index r start next sample s ∧
      ProgramExecution v₀ final p call index (s.clock + 1) (next sample) result
  | .writing r start next => ∃ s, lower ≤ s.clock ∧
      WriteEndsAt v₀ final p call index r start next s ∧
      ProgramExecution v₀ final p call index (s.clock + 1) next result

theorem phaseExecution_mono {v₀ : α} {final : State n α} {p call index lower phase result}
    (h : PhaseExecution v₀ final p call index lower phase result) {earlier : Nat}
    (bound : earlier ≤ lower) : PhaseExecution v₀ final p call index earlier phase result := by
  cases phase with
  | ready prog => exact programExecution_mono h bound
  | reading r start next =>
    obtain ⟨s, sample, hb, he, ht⟩ := h
    exact ⟨s, sample, Nat.le_trans bound hb, he, ht⟩
  | writing r start next =>
    obtain ⟨s, hb, he, ht⟩ := h
    exact ⟨s, Nat.le_trans bound hb, he, ht⟩

theorem instruction_execution_backwards {v₀ : α} {s final : State n α}
    {p call index phase phase' result}
    (instruction : Instruction v₀ s phase phase')
    (active : s.threads p = some ⟨call, index, phase⟩)
    (suffix : TraceTo v₀ s final)
    (after : PhaseExecution v₀ final p call index (s.clock + 1) phase' result) :
    PhaseExecution v₀ final p call index s.clock phase result := by
  cases instruction with
  | unchanged => exact phaseExecution_mono after (Nat.le_succ _)
  | order next b => exact .order b (programExecution_mono after (Nat.le_succ _))
  | token a b choice next ha hb =>
    exact .token choice ha hb (programExecution_mono after (Nat.le_succ _))
  | beginRead r next =>
    obtain ⟨e, sample, hb, he, ht⟩ := after
    exact .read s.clock e sample (Nat.le_refl _) (by omega) he ht
  | endRead r start next sample regular supplies =>
    exact ⟨s, sample, Nat.le_refl _, ⟨suffix, active, regular, supplies⟩, after⟩
  | beginWrite r value next =>
    obtain ⟨e, hb, he, ht⟩ := after
    exact .write s e (Nat.le_refl _) (by omega) ⟨suffix, active⟩ he ht
  | endWrite r start next => exact ⟨s, Nat.le_refl _, ⟨suffix, active⟩, after⟩

/-- Backward interpretation works on one actual global replay. The suffix in
all observations leads to the same endpoint, not an arbitrary reachable state. -/
theorem causalReplay_execution {v₀ : α} {p : Process n} {call index : Nat}
    {s₀ s final : State n α} {phase₀ phase : Phase n α} {result}
    (replay : CausalReplay v₀ p call index s₀ phase₀ s phase)
    (suffix : TraceTo v₀ s final)
    (after : PhaseExecution v₀ final p call index s.clock phase result) :
    PhaseExecution v₀ final p call index s₀.clock phase₀ result := by
  induction replay with
  | refl => exact after
  | snoc prior step active instruction ih =>
    have tail := traceTo_step step suffix
    apply ih tail
    apply instruction_execution_backwards instruction
      (callSegment_active (causalReplay_segment prior)) tail
    simpa [step_clock step] using after

theorem causalReplay_programExecution {v₀ : α} {p : Process n} {call index : Nat}
    {s₀ s : State n α} {prog : Program n α} {result}
    (replay : CausalReplay v₀ p call index s₀ (.ready prog) s (.ready (.done result))) :
    ProgramExecution v₀ s p call index s₀.clock prog result :=
  causalReplay_execution replay (traceTo_refl v₀ s) (.done (Nat.le_refl _))

/-- Existentially hides a consumed closure while retaining its actual read. -/
def ReadObserved (v₀ : α) (final : State n α) (p : Process n) (call index : Nat)
    (r : Register n) (sample : Sample (Value α r)) (start finish : Nat) : Prop :=
  start < finish ∧ ∃ s next, s.clock = finish ∧
    ReadAt v₀ final p call index r start next sample s

def WriteObserved (v₀ : α) (final : State n α) (p : Process n) (call index : Nat)
    (r : Register n) (value : Value α r) (start finish : Nat) : Prop :=
  start < finish ∧ ∃ s e next, s.clock = start ∧ e.clock = finish ∧
    WriteStartsAt v₀ final p call index r value next s ∧
    WriteEndsAt v₀ final p call index r start next e

theorem programExecution_read {v₀ : α} {final : State n α}
    {p call index lower r next result}
    (h : ProgramExecution v₀ final p call index lower (.read r next) result) :
    ∃ start finish sample, lower ≤ start ∧
      ReadObserved v₀ final p call index r sample start finish ∧
      ProgramExecution v₀ final p call index (finish + 1) (next sample) result := by
  cases h with
  | read start s sample hb hi he ht =>
    exact ⟨start, s.clock, sample, hb, ⟨hi, s, next, rfl, he⟩, ht⟩

theorem programExecution_write {v₀ : α} {final : State n α}
    {p call index lower r value next result}
    (h : ProgramExecution v₀ final p call index lower (.write r value next) result) :
    ∃ start finish, lower ≤ start ∧
      WriteObserved v₀ final p call index r value start finish ∧
      ProgramExecution v₀ final p call index (finish + 1) next result := by
  cases h with
  | write s e hb hi hs he ht =>
    exact ⟨s.clock, e.clock, hb, ⟨hi, s, e, next, rfl, rfl, hs, he⟩, ht⟩

theorem programExecution_done {v₀ : α} {final : State n α}
    {p call index lower result actual}
    (h : ProgramExecution v₀ final p call index lower (.done result) actual) :
    result = actual ∧ lower ≤ final.clock := by
  cases h with
  | done hb => exact ⟨rfl, hb⟩

/-- Both observations belong to this same call and are sequential in one of the
permitted operand orders. `upper` is strictly after both completions. -/
def PairObserved (v₀ : α) (final : State n α) (p : Process n) (call index : Nat)
    (a b : Register n) (lower upper : Nat)
    (x : Sample (Value α a)) (y : Sample (Value α b)) : Prop :=
  ∃ aStart aEnd bStart bEnd,
    lower ≤ aStart ∧ lower ≤ bStart ∧
    ReadObserved v₀ final p call index a x aStart aEnd ∧
    ReadObserved v₀ final p call index b y bStart bEnd ∧
    ((aEnd < bStart ∧ upper = bEnd + 1) ∨ (bEnd < aStart ∧ upper = aEnd + 1))

theorem programExecution_pair {v₀ : α} {final : State n α}
    {p call index lower a b next result}
    (h : ProgramExecution v₀ final p call index lower (pair a b next) result) :
    ∃ upper x y, PairObserved v₀ final p call index a b lower upper x y ∧
      ProgramExecution v₀ final p call index upper (next x y) result := by
  cases h with
  | order choice ht =>
    cases choice
    · simp only [Bool.false_eq_true, ↓reduceIte] at ht
      obtain ⟨bs, be, y, hb, he, ht⟩ := programExecution_read ht
      obtain ⟨as, ae, x, ha, hx, ht⟩ := programExecution_read ht
      refine ⟨ae + 1, x, y, ⟨as, ae, bs, be, ?_, hb, hx, he, Or.inr ⟨?_, rfl⟩⟩, ht⟩
      · have := he.1; omega
      · omega
    · simp only [↓reduceIte] at ht
      obtain ⟨as, ae, x, ha, hx, ht⟩ := programExecution_read ht
      obtain ⟨bs, be, y, hb, hy, ht⟩ := programExecution_read ht
      refine ⟨be + 1, x, y, ⟨as, ae, bs, be, ha, ?_, hx, hy, Or.inl ⟨?_, rfl⟩⟩, ht⟩
      · have := hx.1; omega
      · omega

theorem pairObserved_progress {v₀ : α} {final : State n α}
    {p call index a b lower upper x y}
    (h : PairObserved v₀ final p call index a b lower upper x y) : lower < upper := by
  obtain ⟨as, ae, bs, be, ha, hb, hx, hy, horder⟩ := h
  have := hx.1
  have := hy.1
  rcases horder with horder | horder <;> omega

/-- Scan evidence contains each actual pair, including nonmatching pairs. -/
inductive ScanObserved (v₀ : α) (final : State n α) (p : Process n) (call index : Nat) :
    List (Fin n) → Nat → Bool → Nat → Bool → Prop where
  | nil (time forwarded) : ScanObserved v₀ final p call index [] time forwarded time forwarded
  | cons {i rest lower middle upper forwarded outcome x y}
      (pair : PairObserved v₀ final p call index (.fc i) (.wc i) lower middle x y)
      (tail : ScanObserved v₀ final p call index rest middle
        (forwarded || decide (x.value = y.value)) upper outcome) :
      ScanObserved v₀ final p call index (i :: rest) lower forwarded upper outcome

theorem readerScan_execution {v₀ : α} {final : State n α}
    {p call index lower j saved forwarded readers result}
    (h : ProgramExecution v₀ final p call index lower
      (readerScan j saved forwarded readers) result) :
    ∃ upper outcome, ScanObserved v₀ final p call index readers lower forwarded upper outcome ∧
      ProgramExecution v₀ final p call index upper (readerScan j saved outcome []) result := by
  induction readers generalizing lower forwarded with
  | nil => exact ⟨lower, forwarded, .nil lower forwarded, h⟩
  | cons i rest ih =>
    obtain ⟨middle, x, y, hp, ht⟩ := programExecution_pair h
    obtain ⟨upper, outcome, hs, ht⟩ := ih ht
    exact ⟨upper, outcome, .cons hp hs, ht⟩

theorem scanObserved_progress {v₀ : α} {final : State n α}
    {p call index readers lower forwarded upper outcome}
    (h : ScanObserved v₀ final p call index readers lower forwarded upper outcome) :
    lower ≤ upper := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons hp ht ih => exact Nat.le_trans (Nat.le_of_lt (pairObserved_progress hp)) ih

/-- A true scan starting at false has an actual matching FC/WC pair, rather
than an assumed forwarding invariant. The witness still contains actual reads. -/
theorem scanObserved_match {v₀ : α} {final : State n α}
    {p call index readers lower forwarded upper}
    (h : ScanObserved v₀ final p call index readers lower forwarded upper true)
    (hf : forwarded = false) :
    ∃ i ∈ readers, ∃ begin finish x y,
      lower ≤ begin ∧ finish ≤ upper ∧
      PairObserved v₀ final p call index (.fc i) (.wc i) begin finish x y ∧ x.value = y.value := by
  induction readers generalizing lower forwarded with
  | nil => cases h; simp_all
  | cons i rest ih =>
    cases h with
    | cons hp ht =>
      rename_i middle x y
      by_cases eq : x.value = y.value
      · exact ⟨i, List.mem_cons_self, lower, middle, x, y, Nat.le_refl _,
          scanObserved_progress ht, hp, eq⟩
      · have hfalse : (forwarded || decide (x.value = y.value)) = false := by simp [hf, eq]
        obtain ⟨k, hk, begin, finish, a, b, hb, he, hp', heq⟩ := ih ht hfalse
        exact ⟨k, List.mem_cons_of_mem i hk, begin, finish, a, b,
          Nat.le_trans (Nat.le_of_lt (pairObserved_progress hp)) hb, he, hp', heq⟩

/-- Exact finish alternatives, including every required forwarding access and
strict completion before the caller's response boundary. -/
inductive ReaderFinishObserved (v₀ : α) (final : State n α) (p : Process n)
    (call index : Nat) (j : Fin n) (saved : Sample α) (forwarded : Bool)
    (level rc wc : Token) (lower : Nat) : Option (Sample α) → Prop where
  | buff2 (guard : rc ≠ wc ∨ (level = 1 ∧ forwarded = false))
      (start finish : Nat) (sample : Sample α) (hb : lower ≤ start)
      (read : ReadObserved v₀ final p call index .buff2 sample start finish)
      (response : finish < final.clock) :
      ReaderFinishObserved v₀ final p call index j saved forwarded level rc wc lower (some sample)
  | quiet (guard : ¬ (rc ≠ wc ∨ (level = 1 ∧ forwarded = false)))
      (levelZero : level = 0) (response : lower ≤ final.clock) :
      ReaderFinishObserved v₀ final p call index j saved forwarded level rc wc lower (some saved)
  | forward (guard : ¬ (rc ≠ wc ∨ (level = 1 ∧ forwarded = false)))
      (levelNonzero : level ≠ 0) (token : Sample Token)
      (readStart readEnd writeStart writeEnd : Nat)
      (hb : lower ≤ readStart)
      (read : ReadObserved v₀ final p call index (.rc j) token readStart readEnd)
      (between : readEnd < writeStart)
      (write : WriteObserved v₀ final p call index (.fc j) token.value writeStart writeEnd)
      (response : writeEnd < final.clock) :
      ReaderFinishObserved v₀ final p call index j saved forwarded level rc wc lower (some saved)

theorem readerFinish_execution {v₀ : α} {final : State n α}
    {p call index lower j saved forwarded level rc wc result}
    (h : ProgramExecution v₀ final p call index lower
      (readerFinish j saved forwarded level rc wc) result) :
    ReaderFinishObserved v₀ final p call index j saved forwarded level rc wc lower result := by
  by_cases guard : rc ≠ wc ∨ (level = 1 ∧ forwarded = false)
  · rw [readerFinish, ite_eq_left guard] at h
    obtain ⟨start, finish, sample, hb, hr, ht⟩ := programExecution_read h
    obtain ⟨rfl, he⟩ := programExecution_done ht
    exact .buff2 guard start finish sample hb hr (by omega)
  · by_cases hz : level = 0
    · rw [readerFinish, ite_eq_right guard, ite_eq_right (by simpa using hz)] at h
      obtain ⟨rfl, he⟩ := programExecution_done h
      exact .quiet guard hz he
    · rw [readerFinish, ite_eq_right guard, ite_eq_left hz] at h
      obtain ⟨rs, re, token, hb, hr, ht⟩ := programExecution_read h
      obtain ⟨ws, we, hw, he, ht⟩ := programExecution_write ht
      obtain ⟨rfl, hend⟩ := programExecution_done ht
      exact .forward guard hz token rs re ws we hb hr (by omega) he (by omega)

/-- Reader entry accesses: its copied WC token, RC write, and saved Buff1
sample, before all the actual scan pairs and final guards. -/
theorem readerProgram_execution_prefix {v₀ : α} {final : State n α}
    {p call index lower j result}
    (h : ProgramExecution v₀ final p call index lower (readerProgram j) result) :
    ∃ ws we token rs re bs be saved,
      lower ≤ ws ∧ ReadObserved v₀ final p call index (.wc j) token ws we ∧
      we < rs ∧ WriteObserved v₀ final p call index (.rc j) token.value rs re ∧
      re < bs ∧ ReadObserved v₀ final p call index .buff1 saved bs be ∧
      ProgramExecution v₀ final p call index (be + 1)
        (readerScan j saved false (List.finRange n)) result := by
  obtain ⟨ws, we, token, hb, hw, ht⟩ := programExecution_read h
  obtain ⟨rs, re, hr, hrc, ht⟩ := programExecution_write ht
  obtain ⟨bs, be, saved, hb1, hbuff, ht⟩ := programExecution_read ht
  exact ⟨ws, we, token, rs, re, bs, be, saved, hb, hw, by omega, hrc, by omega, hbuff, ht⟩

/-- The post-scan Level observation and the reader's RC/WC guard pair are
actual primitive accesses, followed by one of the exact finish alternatives. -/
theorem readerScan_execution_suffix {v₀ : α} {final : State n α}
    {p call index lower j saved forwarded result}
    (h : ProgramExecution v₀ final p call index lower (readerScan j saved forwarded []) result) :
    ∃ ls le level upper rc wc,
      lower ≤ ls ∧ ReadObserved v₀ final p call index .level level ls le ∧
      PairObserved v₀ final p call index (.rc j) (.wc j) (le + 1) upper rc wc ∧
      ReaderFinishObserved v₀ final p call index j saved forwarded
        level.value rc.value wc.value upper result := by
  obtain ⟨ls, le, level, hb, hl, ht⟩ := programExecution_read h
  obtain ⟨upper, rc, wc, hp, ht⟩ := programExecution_pair ht
  exact ⟨ls, le, level, upper, rc, wc, hb, hl, hp, readerFinish_execution ht⟩

/-- Writer cancellation chooses a token different from both actual operands,
then completes its WC write before continuing to the remaining readers. -/
theorem writerLoop_execution_cons {v₀ : α} {final : State n α}
    {p call index lower v j rest result}
    (h : ProgramExecution v₀ final p call index lower (writerLoop v (j :: rest)) result) :
    ∃ middle rc fc token ws we,
      PairObserved v₀ final p call index (.rc j) (.fc j) lower middle rc fc ∧
      token ≠ rc.value ∧ token ≠ fc.value ∧ middle ≤ ws ∧
      WriteObserved v₀ final p call index (.wc j) token ws we ∧
      ProgramExecution v₀ final p call index (we + 1) (writerLoop v rest) result := by
  obtain ⟨middle, rc, fc, hp, ht⟩ := programExecution_pair h
  cases ht with
  | token token ha hb tail =>
    obtain ⟨ws, we, hw, he, ht⟩ := programExecution_write tail
    exact ⟨middle, rc, fc, token, ws, we, hp, ha, hb, hw, he, ht⟩

end MultiReaderAtomic
