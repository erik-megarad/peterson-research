import MultiReaderAtomic.Origin

/-! Proof-side call segments retain every actual intermediate phase and Step.
No certificate is a premise of the protocol or of a protected target. -/
namespace MultiReaderAtomic

/-- One instruction with its actual samples and the history at completion.
Unlike an origin predicate, this retains control values and consumed closures. -/
inductive Instruction (v₀ : α) (s : State n α) : Phase n α → Phase n α → Prop where
  | unchanged (phase) : Instruction v₀ s phase phase
  | order (next : Bool → Program n α) (b : Bool) :
      Instruction v₀ s (.ready (.order next)) (.ready (next b))
  | token (a b choice : Token) (next : Token → Program n α)
      (ha : choice ≠ a) (hb : choice ≠ b) :
      Instruction v₀ s (.ready (.token a b next)) (.ready (next choice))
  | beginRead (r : Register n) (next : Sample (Value α r) → Program n α) :
      Instruction v₀ s (.ready (.read r next)) (.reading r s.clock next)
  | endRead (r : Register n) (start : Nat) (next : Sample (Value α r) → Program n α)
      (sample : Sample (Value α r))
      (regular : Eligible (s.writes r) start s.clock sample.witness)
      (supplies : Supplies (initialValue v₀ r) (s.writes r) sample) :
      Instruction v₀ s (.reading r start next) (.ready (next sample))
  | beginWrite (r : Register n) (value : Value α r) (next : Program n α) :
      Instruction v₀ s (.ready (.write r value next)) (.writing r s.clock next)
  | endWrite (r : Register n) (start : Nat) (next : Program n α) :
      Instruction v₀ s (.writing r start next) (.ready next)

theorem instruction_of_step {v₀ : α} {s s' : State n α} {a : Action n}
    (step : Step v₀ s a s') (p : Process n) (t u : Thread n α)
    (before : s.threads p = some t) (after : s'.threads p = some u) :
    Instruction v₀ s t.phase u.phase := by
  have other : ∀ (q : Process n) (replacement : Option (Thread n α)),
      p ≠ q → (Function.update s.threads q replacement) p = some u → t = u := by
    intro q replacement neq hu
    rw [Function.update_of_ne neq, before] at hu
    exact Option.some.inj hu
  cases step with
  | invokeWriter v free =>
    by_cases eq : p = .writer
    · subst p; rw [free] at before; contradiction
    · have htu := other .writer _ eq after
      cases htu
      exact Instruction.unchanged _
  | invokeReader j free =>
    by_cases eq : p = .reader j
    · subst p; rw [free] at before; contradiction
    · have htu := other (.reader j) _ eq after
      cases htu
      exact Instruction.unchanged _
  | order q x next b active control =>
    by_cases eq : p = q
    · subst p
      rw [active] at before
      cases Option.some.inj before
      have hu : u = {t with phase := .ready (next b)} :=
        (Option.some.inj (by simpa [withThread] using after)).symm
      cases hu
      rw [control]
      exact Instruction.order next b
    · have htu := other q _ eq after
      cases htu
      exact Instruction.unchanged _
  | token q x av bv choice next active control ha hb =>
    by_cases eq : p = q
    · subst p
      rw [active] at before
      cases Option.some.inj before
      have hu : u = {t with phase := .ready (next choice)} :=
        (Option.some.inj (by simpa [withThread] using after)).symm
      cases hu
      rw [control]
      exact Instruction.token av bv choice next ha hb
    · have htu := other q _ eq after
      cases htu
      exact Instruction.unchanged _
  | beginRead q x r next active control =>
    by_cases eq : p = q
    · subst p
      rw [active] at before
      cases Option.some.inj before
      have hu : u = {t with phase := .reading r s.clock next} :=
        (Option.some.inj (by simpa [withThread] using after)).symm
      cases hu
      rw [control]
      exact Instruction.beginRead r next
    · have htu := other q _ eq after
      cases htu
      exact Instruction.unchanged _
  | endRead q x r start next sample active control regular supplies =>
    by_cases eq : p = q
    · subst p
      rw [active] at before
      cases Option.some.inj before
      have hu : u = {t with phase := .ready (next sample)} :=
        (Option.some.inj (by simpa [withThread] using after)).symm
      cases hu
      rw [control]
      exact Instruction.endRead r start next sample regular supplies
    · have htu := other q _ eq after
      cases htu
      exact Instruction.unchanged _
  | beginWrite q x r value next active control owner =>
    by_cases eq : p = q
    · subst p
      rw [active] at before
      cases Option.some.inj before
      have hu : u = {t with phase := .writing r s.clock next} :=
        (Option.some.inj (by simpa [withThread] using after)).symm
      cases hu
      rw [control]
      exact Instruction.beginWrite r value next
    · have htu := other q _ eq after
      cases htu
      exact Instruction.unchanged _
  | endWrite q x r start next active control =>
    by_cases eq : p = q
    · subst p
      rw [active] at before
      cases Option.some.inj before
      have hu : u = {t with phase := .ready next} :=
        (Option.some.inj (by simpa [withThread] using after)).symm
      cases hu
      rw [control]
      exact Instruction.endWrite r start next
    · have htu := other q _ eq after
      cases htu
      exact Instruction.unchanged _
  | respond q x result active control =>
    by_cases eq : p = q
    · subst p; simp [withThread] at after
    · have htu := other q _ eq after
      cases htu
      exact Instruction.unchanged _
  | idle =>
    rw [before] at after
    cases Option.some.inj after
    exact Instruction.unchanged _

/-- A contiguous segment during which one call remains active. Read samples,
intervals and witness histories remain in the actual Step.endRead constructors. -/
inductive CallSegment (v₀ : α) (p : Process n) (call index : Nat) :
    State n α → Phase n α → State n α → Phase n α → Prop where
  | refl (s phase) (active : s.threads p = some ⟨call, index, phase⟩) :
      CallSegment v₀ p call index s phase s phase
  | snoc {s₀ phase₀ s phase s' phase' a}
      (prior : CallSegment v₀ p call index s₀ phase₀ s phase)
      (step : Step v₀ s a s')
      (active : s'.threads p = some ⟨call, index, phase'⟩) :
      CallSegment v₀ p call index s₀ phase₀ s' phase'

/-- Exact invocation and its actual Figure 1 starting program. -/
inductive CallStart (v₀ : α) : Process n → Nat → Nat → State n α → Phase n α → Prop where
  | writer (s : State n α) (v : α) (past : Reachable v₀ s)
      (free : s.threads .writer = none) :
      CallStart v₀ .writer s.clock s.nextWrite
        { withThread s .writer (some ⟨s.clock, s.nextWrite, .ready (writerProgram v)⟩) with
          nextWrite := s.nextWrite + 1
          calls := s.calls ++ [⟨s.clock, .writer, s.clock, s.nextWrite, some v, none⟩] }
        (.ready (writerProgram v))
  | reader (s : State n α) (j : Fin n) (past : Reachable v₀ s)
      (free : s.threads (.reader j) = none) :
      CallStart v₀ (.reader j) s.clock 0
        { withThread s (.reader j) (some ⟨s.clock, 0, .ready (readerProgram j)⟩) with
          calls := s.calls ++ [⟨s.clock, .reader j, s.clock, 0, none, none⟩] }
        (.ready (readerProgram j))

def ActiveSegments (v₀ : α) (s : State n α) : Prop :=
  ∀ p t, s.threads p = some t → ∃ start phase,
    CallStart v₀ p t.call t.writeIndex start phase ∧
    CallSegment v₀ p t.call t.writeIndex start phase s t.phase

theorem reachable_step {v₀ : α} {s s' : State n α} {a : Action n}
    (past : Reachable v₀ s) (step : Step v₀ s a s') : Reachable v₀ s' := by
  obtain ⟨actions, trace⟩ := past
  exact ⟨actions ++ [a], Cslib.LTS.MTr.comp (lts v₀) trace
    (Cslib.LTS.MTr.stepL step Cslib.LTS.MTr.refl)⟩

theorem callStart_active {v₀ : α} {p : Process n} {call index : Nat}
    {s : State n α} {phase : Phase n α} (h : CallStart v₀ p call index s phase) :
    s.threads p = some ⟨call, index, phase⟩ := by
  cases h <;> simp [withThread]

theorem callStart_reachable {v₀ : α} {p : Process n} {call index : Nat}
    {s : State n α} {phase : Phase n α} (h : CallStart v₀ p call index s phase) :
    Reachable v₀ s := by
  cases h with
  | writer s v past free => exact reachable_step past (Step.invokeWriter s v free)
  | reader s j past free => exact reachable_step past (Step.invokeReader s j free)

theorem callSegment_active {v₀ : α} {p : Process n} {call index : Nat}
    {s₀ s : State n α} {phase₀ phase : Phase n α}
    (h : CallSegment v₀ p call index s₀ phase₀ s phase) :
    s.threads p = some ⟨call, index, phase⟩ := by
  cases h with
  | refl active => exact active
  | snoc prior step active => exact active

theorem callSegment_trace {v₀ : α} {p : Process n} {call index : Nat}
    {s₀ s : State n α} {phase₀ phase : Phase n α}
    (h : CallSegment v₀ p call index s₀ phase₀ s phase) :
    ∃ actions, (lts v₀).MTr s₀ actions s := by
  induction h with
  | refl => exact ⟨[], Cslib.LTS.MTr.refl⟩
  | snoc prior step active ih =>
    obtain ⟨actions, trace⟩ := ih
    exact ⟨actions ++ [_], Cslib.LTS.MTr.comp (lts v₀) trace
      (Cslib.LTS.MTr.stepL step Cslib.LTS.MTr.refl)⟩

theorem callSegment_clock {v₀ : α} {p : Process n} {call index : Nat}
    {s₀ s : State n α} {phase₀ phase : Phase n α}
    (h : CallSegment v₀ p call index s₀ phase₀ s phase) : s₀.clock ≤ s.clock := by
  induction h with
  | refl => exact Nat.le_refl _
  | snoc prior step active ih => rw [step_clock step]; exact Nat.le_succ_of_le ih

/-- A replay retains both exact instructions and their contiguous global states.
In particular, old read evidence is never rechecked against a later history. -/
inductive CausalReplay (v₀ : α) (p : Process n) (call index : Nat) :
    State n α → Phase n α → State n α → Phase n α → Prop where
  | refl (s phase) (active : s.threads p = some ⟨call, index, phase⟩) :
      CausalReplay v₀ p call index s phase s phase
  | snoc {s₀ phase₀ s phase s' phase' a}
      (prior : CausalReplay v₀ p call index s₀ phase₀ s phase)
      (step : Step v₀ s a s')
      (active : s'.threads p = some ⟨call, index, phase'⟩)
      (instruction : Instruction v₀ s phase phase') :
      CausalReplay v₀ p call index s₀ phase₀ s' phase'

theorem callSegment_replay {v₀ : α} {p : Process n} {call index : Nat}
    {s₀ s : State n α} {phase₀ phase : Phase n α}
    (h : CallSegment v₀ p call index s₀ phase₀ s phase) :
    CausalReplay v₀ p call index s₀ phase₀ s phase := by
  induction h with
  | refl active => exact CausalReplay.refl _ _ active
  | snoc prior step active ih =>
    exact CausalReplay.snoc ih step active
      (instruction_of_step step p _ _ (callSegment_active prior) active)

theorem causalReplay_segment {v₀ : α} {p : Process n} {call index : Nat}
    {s₀ s : State n α} {phase₀ phase : Phase n α}
    (h : CausalReplay v₀ p call index s₀ phase₀ s phase) :
    CallSegment v₀ p call index s₀ phase₀ s phase := by
  induction h with
  | refl active => exact CallSegment.refl _ _ active
  | snoc prior step active instruction ih => exact CallSegment.snoc ih step active

theorem causalReplay_clock {v₀ : α} {p : Process n} {call index : Nat}
    {s₀ s : State n α} {phase₀ phase : Phase n α}
    (h : CausalReplay v₀ p call index s₀ phase₀ s phase) : s₀.clock ≤ s.clock := by
  induction h with
  | refl => exact Nat.le_refl _
  | snoc prior step active instruction ih => rw [step_clock step]; exact Nat.le_succ_of_le ih

def PhasePast (phase : Phase n α) (time : Nat) : Prop :=
  match phase with
  | .ready _ => True
  | .reading _ start _ | .writing _ start _ => start < time

theorem phasePast_mono {phase : Phase n α} {time later : Nat}
    (h : PhasePast phase time) (ht : time ≤ later) : PhasePast phase later := by
  cases phase <;> simp_all [PhasePast]
  all_goals exact Nat.lt_of_lt_of_le h ht

theorem phasePast_instruction {v₀ : α} {s : State n α} {phase phase' : Phase n α}
    (instruction : Instruction v₀ s phase phase') (h : PhasePast phase s.clock) :
    PhasePast phase' (s.clock + 1) := by
  cases instruction with
  | unchanged => exact phasePast_mono h (Nat.le_succ _)
  | beginRead => exact Nat.lt_succ_self _
  | beginWrite => exact Nat.lt_succ_self _
  | _ => trivial

theorem causalReplay_phasePast {v₀ : α} {p : Process n} {call index : Nat}
    {s₀ s : State n α} {phase₀ phase : Phase n α}
    (replay : CausalReplay v₀ p call index s₀ phase₀ s phase) (h : PhasePast phase₀ s₀.clock) :
    PhasePast phase s.clock := by
  induction replay with
  | refl => exact h
  | snoc prior step active instruction ih =>
    rw [step_clock step]
    exact phasePast_instruction instruction ih

theorem callStart_phasePast {v₀ : α} {p : Process n} {call index : Nat}
    {s : State n α} {phase : Phase n α} (h : CallStart v₀ p call index s phase) :
    PhasePast phase s.clock := by
  cases h <;> trivial

/-- All other processes extend their segments through this same global Step. -/
theorem activeSegments_update {v₀ : α} {s s' : State n α} {a : Action n}
    (step : Step v₀ s a s') (h : ActiveSegments v₀ s)
    (p : Process n) (t' : Option (Thread n α))
    (updated : s'.threads = Function.update s.threads p t')
    (new : ∀ t, t' = some t → ∃ start phase,
      CallStart v₀ p t.call t.writeIndex start phase ∧
      CallSegment v₀ p t.call t.writeIndex start phase s' t.phase) : ActiveSegments v₀ s' := by
  intro q t active
  by_cases eq : q = p
  · subst q
    apply new t
    simpa [updated] using active
  · have old : s.threads q = some t := by
      simpa [updated, Function.update_of_ne eq] using active
    obtain ⟨start, phase, hs, segment⟩ := h q t old
    exact ⟨start, phase, hs, CallSegment.snoc segment step active⟩

theorem activeSegments_initial (v₀ : α) : ActiveSegments (n := n) v₀ initial := by
  simp [ActiveSegments, initial]

theorem activeSegments_step {v₀ : α} {s s' : State n α} {a : Action n}
    (past : Reachable v₀ s) (step : Step v₀ s a s')
    (h : ActiveSegments v₀ s) : ActiveSegments v₀ s' := by
  cases step with
  | invokeWriter v free =>
    apply activeSegments_update (Step.invokeWriter s v free) h .writer _ rfl
    intro t eq
    cases eq
    have hs := CallStart.writer s v past free
    exact ⟨_, _, hs, CallSegment.refl _ _ (callStart_active hs)⟩
  | invokeReader j free =>
    apply activeSegments_update (Step.invokeReader s j free) h (.reader j) _ rfl
    intro t eq
    cases eq
    have hs := CallStart.reader s j past free
    exact ⟨_, _, hs, CallSegment.refl _ _ (callStart_active hs)⟩
  | order p t next b active control =>
    apply activeSegments_update (Step.order s p t next b active control) h p _ rfl
    intro u eq
    cases eq
    obtain ⟨start, phase, hs, segment⟩ := h p t active
    exact ⟨start, phase, hs, CallSegment.snoc segment
      (Step.order s p t next b active control) (by simp [withThread])⟩
  | token p t x y choice next active control ha hb =>
    apply activeSegments_update (Step.token s p t x y choice next active control ha hb) h p _ rfl
    intro u eq
    cases eq
    obtain ⟨start, phase, hs, segment⟩ := h p t active
    exact ⟨start, phase, hs, CallSegment.snoc segment
      (Step.token s p t x y choice next active control ha hb) (by simp [withThread])⟩
  | beginRead p t r next active control =>
    apply activeSegments_update (Step.beginRead s p t r next active control) h p _ rfl
    intro u eq
    cases eq
    obtain ⟨start, phase, hs, segment⟩ := h p t active
    exact ⟨start, phase, hs, CallSegment.snoc segment
      (Step.beginRead s p t r next active control) (by simp [withThread])⟩
  | endRead p t r time next sample active control regular supplies =>
    apply activeSegments_update
      (Step.endRead s p t r time next sample active control regular supplies) h p _ rfl
    intro u eq
    cases eq
    obtain ⟨start, phase, hs, segment⟩ := h p t active
    exact ⟨start, phase, hs, CallSegment.snoc segment
      (Step.endRead s p t r time next sample active control regular supplies)
      (by simp [withThread])⟩
  | beginWrite p t r value next active control owner =>
    apply activeSegments_update (Step.beginWrite s p t r value next active control owner) h p _ rfl
    intro u eq
    cases eq
    obtain ⟨start, phase, hs, segment⟩ := h p t active
    exact ⟨start, phase, hs, CallSegment.snoc segment
      (Step.beginWrite s p t r value next active control owner) (by simp [withThread])⟩
  | endWrite p t r time next active control =>
    apply activeSegments_update (Step.endWrite s p t r time next active control) h p _ rfl
    intro u eq
    cases eq
    obtain ⟨start, phase, hs, segment⟩ := h p t active
    exact ⟨start, phase, hs, CallSegment.snoc segment
      (Step.endWrite s p t r time next active control) (by simp [withThread])⟩
  | respond p t result active control =>
    apply activeSegments_update (Step.respond s p t result active control) h p none rfl
    simp
  | idle =>
    intro p t active
    obtain ⟨start, phase, hs, segment⟩ := h p t active
    exact ⟨start, phase, hs, CallSegment.snoc segment (Step.idle s) active⟩

theorem activeSegments_reachable {v₀ : α} {s : State n α} (past : Reachable v₀ s) :
    ActiveSegments v₀ s := by
  obtain ⟨actions, trace⟩ := past
  have general : ∀ {s s' : State n α} {actions}, (lts v₀).MTr s actions s' →
      Reachable v₀ s → ActiveSegments v₀ s → ActiveSegments v₀ s' := by
    intro s s' actions trace hs hi
    induction trace with
    | refl => exact hi
    | stepL step tail ih => exact ih (reachable_step hs step) (activeSegments_step hs step hi)
  exact general trace ⟨[], Cslib.LTS.MTr.refl⟩ (activeSegments_initial v₀)

/-- Real primitive intervals have strictly earlier invocation endpoints. -/
theorem active_phasePast {v₀ : α} {s : State n α} (past : Reachable v₀ s)
    (p : Process n) (t : Thread n α) (active : s.threads p = some t) :
    PhasePast t.phase s.clock := by
  obtain ⟨start, phase, hs, segment⟩ := activeSegments_reachable past p t active
  exact causalReplay_phasePast (callSegment_replay segment) (callStart_phasePast hs)

theorem active_read_interval {v₀ : α} {s : State n α} (past : Reachable v₀ s)
    (p : Process n) (t : Thread n α) (r : Register n) (start : Nat)
    (next : Sample (Value α r) → Program n α)
    (active : s.threads p = some t) (phase : t.phase = .reading r start next) :
    start < s.clock := by
  have h := active_phasePast past p t active
  simpa [phase, PhasePast] using h

/-- The exact program and sampled operands survive after response removes the
thread. This is a proof archive, not an additional field in reachable states. -/
def CompletedSegments (v₀ : α) (s : State n α) : Prop :=
  ∀ c time result, c ∈ s.calls → c.response = some (time, result) →
    ∃ (p : Process n) (index : Nat) (start : State n α) (phase : Phase n α) (finish : State n α),
      CallStart v₀ p c.id index start phase ∧
      CallSegment v₀ p c.id index start phase finish (.ready (.done result)) ∧
      Reachable v₀ finish ∧ time = finish.clock

theorem completedSegments_step {v₀ : α} {s s' : State n α} {a : Action n}
    (past : Reachable v₀ s) (step : Step v₀ s a s')
    (activeSegments : ActiveSegments v₀ s) (h : CompletedSegments v₀ s) :
    CompletedSegments v₀ s' := by
  cases step with
  | invokeWriter v free =>
    intro c time result hc hr
    rcases List.mem_append.mp hc with hc | hc
    · exact h c time result hc hr
    · cases List.mem_singleton.mp hc
      cases hr
  | invokeReader j free =>
    intro c time result hc hr
    rcases List.mem_append.mp hc with hc | hc
    · exact h c time result hc hr
    · cases List.mem_singleton.mp hc
      cases hr
  | respond p t result active control =>
    intro c time actualResult hc hr
    obtain ⟨old, hold, heq⟩ := List.mem_map.mp hc
    split at heq
    · rename_i hid
      cases heq
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨start, phase, hs, segment⟩ := activeSegments p t active
      refine ⟨p, t.writeIndex, start, phase, s, ?_, ?_, past, hr.1.symm⟩
      · simpa [hid] using hs
      · rw [← hr.2, ← control]
        simpa [hid] using segment
    · cases heq
      exact h c time actualResult hold hr
  | _ => exact h

theorem completedSegments_reachable {v₀ : α} {s : State n α} (past : Reachable v₀ s) :
    CompletedSegments v₀ s := by
  obtain ⟨actions, trace⟩ := past
  have general : ∀ {s s' : State n α} {actions}, (lts v₀).MTr s actions s' →
      Reachable v₀ s → ActiveSegments v₀ s → CompletedSegments v₀ s → CompletedSegments v₀ s' := by
    intro s s' actions trace hs hi hc
    induction trace with
    | refl => exact hc
    | stepL step tail ih =>
      exact ih (reachable_step hs step) (activeSegments_step hs step hi)
        (completedSegments_step hs step hi hc)
  exact general trace ⟨[], Cslib.LTS.MTr.refl⟩ (activeSegments_initial v₀)
    (by simp [CompletedSegments, initial])

/-- Every actual response has an exact, chronologically connected replay from
its invocation through the done continuation, including required forwarding. -/
theorem response_causalReplay {v₀ : α} {s : State n α} (past : Reachable v₀ s)
    (c : Call n α) (time : Nat) (result : Option (Sample α))
    (hc : c ∈ s.calls) (hr : c.response = some (time, result)) :
    ∃ (p : Process n) (index : Nat) (start : State n α) (phase : Phase n α) (finish : State n α),
      CallStart v₀ p c.id index start phase ∧
      CausalReplay v₀ p c.id index start phase finish (.ready (.done result)) ∧
      Reachable v₀ finish ∧ time = finish.clock := by
  obtain ⟨p, index, start, phase, finish, hs, segment, hf, ht⟩ :=
    completedSegments_reachable past c time result hc hr
  exact ⟨p, index, start, phase, finish, hs, callSegment_replay segment, hf, ht⟩

end MultiReaderAtomic
