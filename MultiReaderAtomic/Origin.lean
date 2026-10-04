import MultiReaderAtomic.Targets

namespace MultiReaderAtomic

/-- Data values retain their source write; control values carry no payload claim. -/
def DataOrigin (origin : Nat → α → Prop) : (r : Register n) → Nat → Value α r → Prop
  | .buff1 | .buff2 => origin
  | .level | .wc _ | .rc _ | .fc _ => fun _ _ => True

/-- Continuations allow the history to grow before their next read. These are
proof obligations, never extra transition premises. -/
def ProgramOrigin (origin : Nat → α → Prop) (index : Nat) : Program n α → Prop
  | .done result => ∀ sample, result = some sample → origin sample.source sample.value
  | .read r next => ∀ origin', (∀ i v, origin i v → origin' i v) →
      ∀ sample, DataOrigin origin' r sample.source sample.value →
      ProgramOrigin origin' index (next sample)
  | .write r value next => DataOrigin origin r index value ∧ ProgramOrigin origin index next
  | .order next => ∀ b, ProgramOrigin origin index (next b)
  | .token a b next => ∀ t, t ≠ a → t ≠ b → ProgramOrigin origin index (next t)

def PhaseOrigin (origin : Nat → α → Prop) (t : Thread n α) : Prop :=
  match t.phase with
  | .ready program => ProgramOrigin origin t.writeIndex program
  | .reading r _ next => ∀ origin', (∀ i v, origin i v → origin' i v) →
      ∀ sample, DataOrigin origin' r sample.source sample.value →
      ProgramOrigin origin' t.writeIndex (next sample)
  | .writing _ _ next => ProgramOrigin origin t.writeIndex next

def OriginInvariant (v₀ : α) (s : State n α) : Prop :=
  (∀ r w, w ∈ s.writes r → DataOrigin (WriteValue v₀ (fun c => c ∈ s.calls)) r w.index w.value) ∧
  (∀ p t, s.threads p = some t → PhaseOrigin (WriteValue v₀ (fun c => c ∈ s.calls)) t) ∧
  (∀ c time sample, c ∈ s.calls → c.response = some (time, some sample) →
    WriteValue v₀ (fun c => c ∈ s.calls) sample.source sample.value)

theorem dataOrigin_mono {origin origin' : Nat → α → Prop}
    (h : ∀ i v, origin i v → origin' i v) (r : Register n) (i : Nat) (v : Value α r)
    (hv : DataOrigin origin r i v) : DataOrigin origin' r i v := by
  cases r <;> simp_all [DataOrigin]

theorem programOrigin_mono {origin origin' : Nat → α → Prop}
    (h : ∀ i v, origin i v → origin' i v) (index : Nat) (p : Program n α)
    (hp : ProgramOrigin origin index p) : ProgramOrigin origin' index p := by
  induction p generalizing origin origin' with
  | done result => exact fun sample hs => h _ _ (hp sample hs)
  | read r next ih => exact fun future hf sample hs => hp future (fun i v hv => hf i v (h i v hv)) sample hs
  | write r value next ih => exact ⟨dataOrigin_mono h r index value hp.1, ih h hp.2⟩
  | order next ih => exact fun b => ih b h (hp b)
  | token a b next ih => exact fun t ha hb => ih t h (hp t ha hb)

theorem phaseOrigin_mono {origin origin' : Nat → α → Prop}
    (h : ∀ i v, origin i v → origin' i v) (t : Thread n α)
    (hp : PhaseOrigin origin t) : PhaseOrigin origin' t := by
  cases t with | mk call index phase =>
    cases phase with
    | ready p => exact programOrigin_mono h index p hp
    | reading r start next => exact fun future hf sample hs => hp future (fun i v hv => hf i v (h i v hv)) sample hs
    | writing r start next => exact programOrigin_mono h index next hp

theorem pair_programOrigin (origin : Nat → α → Prop) (index : Nat) (a b : Register n)
    (next : Sample (Value α a) → Sample (Value α b) → Program n α)
    (h : ∀ future, (∀ i v, origin i v → future i v) →
      ∀ x y, DataOrigin future a x.source x.value → DataOrigin future b y.source y.value →
      ProgramOrigin future index (next x y)) : ProgramOrigin origin index (pair a b next) := by
  intro leftFirst
  cases leftFirst <;> simp only [Bool.false_eq_true, ↓reduceIte, ProgramOrigin]
  · intro future hf y hy later hl x hx
    exact h later (fun i v hv => hl i v (hf i v hv)) x y hx (dataOrigin_mono hl b _ _ hy)
  · intro future hf x hx later hl y hy
    exact h later (fun i v hv => hl i v (hf i v hv)) x y (dataOrigin_mono hl a _ _ hx) hy


theorem writerTail_programOrigin (origin : Nat → α → Prop) (index : Nat) (value : α)
    (hv : origin index value) : ProgramOrigin origin index (writerTail (n := n) value) := by
  simp [writerTail, ProgramOrigin, DataOrigin, hv]

theorem writerLoop_programOrigin (origin : Nat → α → Prop) (index : Nat) (value : α)
    (js : List (Fin n)) (hv : origin index value) :
    ProgramOrigin origin index (writerLoop value js) := by
  induction js generalizing origin with
  | nil => exact writerTail_programOrigin origin index value hv
  | cons j js ih =>
    apply pair_programOrigin
    intro future hf a b _ _ t _ _
    exact ⟨trivial, ih future (hf _ _ hv)⟩

theorem readerFinish_programOrigin (origin : Nat → α → Prop) (index : Nat)
    (j : Fin n) (saved : Sample α) (forwarded : Bool) (level rc wc : Token)
    (hs : origin saved.source saved.value) :
    ProgramOrigin origin index (readerFinish j saved forwarded level rc wc) := by
  unfold readerFinish
  split
  · intro future _ sample hsample
    exact fun _ heq => by cases heq; exact hsample
  · split
    · intro future hf sample _
      exact ⟨trivial, fun _ heq => by cases heq; exact hf _ _ hs⟩
    · exact fun _ heq => by cases heq; exact hs

theorem readerScan_programOrigin (origin : Nat → α → Prop) (index : Nat)
    (j : Fin n) (saved : Sample α) (forwarded : Bool) (js : List (Fin n))
    (hs : origin saved.source saved.value) :
    ProgramOrigin origin index (readerScan j saved forwarded js) := by
  induction js generalizing origin forwarded with
  | nil =>
    intro future hf level _
    apply pair_programOrigin
    intro later hl rc wc _ _
    exact readerFinish_programOrigin later index j saved forwarded _ _ _ (hl _ _ (hf _ _ hs))
  | cons i js ih =>
    apply pair_programOrigin
    intro future hf fc wc _ _
    exact ih future _ (hf _ _ hs)

theorem readerProgram_programOrigin (origin : Nat → α → Prop) (index : Nat) (j : Fin n) :
    ProgramOrigin origin index (readerProgram j) := by
  intro future _ token _
  refine ⟨trivial, ?_⟩
  intro later _ saved hs
  exact readerScan_programOrigin later index j saved false _ hs


/-- Calls can acquire a response, while their identity and write argument persist. -/
def CallExtension (a b : Call n α) : Prop :=
  b.id = a.id ∧ b.process = a.process ∧ b.invoked = a.invoked ∧
  b.writeIndex = a.writeIndex ∧ b.argument = a.argument

theorem callExtension_refl (c : Call n α) : CallExtension c c := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem step_call_extension {v₀ : α} {s s' : State n α} {a : Action n}
    (step : Step v₀ s a s') (c : Call n α) (hc : c ∈ s.calls) :
    ∃ c' ∈ s'.calls, CallExtension c c' := by
  cases step with
  | invokeWriter v free => exact ⟨c, List.mem_append_left _ hc, callExtension_refl c⟩
  | invokeReader j free => exact ⟨c, List.mem_append_left _ hc, callExtension_refl c⟩
  | respond p t result active control =>
    refine ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, ?_⟩
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | _ => exact ⟨c, hc, callExtension_refl c⟩

theorem step_writeValue_mono {v₀ : α} {s s' : State n α} {a : Action n}
    (step : Step v₀ s a s') (i : Nat) (v : α)
    (hv : WriteValue v₀ (fun c => c ∈ s.calls) i v) :
    WriteValue v₀ (fun c => c ∈ s'.calls) i v := by
  rcases hv with hv | ⟨c, hc, hw, hi, ha⟩
  · exact Or.inl hv
  · obtain ⟨d, hd, he⟩ := step_call_extension step c hc
    exact Or.inr ⟨d, hd, he.2.1.trans hw, he.2.2.2.1.trans hi, he.2.2.2.2.trans ha⟩

theorem supplies_dataOrigin (v₀ : α) (s : State n α)
    (h : ∀ r w, w ∈ s.writes r →
      DataOrigin (WriteValue v₀ (fun c => c ∈ s.calls)) r w.index w.value)
    (r : Register n) (sample : Sample (Value α r))
    (hs : Supplies (initialValue v₀ r) (s.writes r) sample) :
    DataOrigin (WriteValue v₀ (fun c => c ∈ s.calls)) r sample.source sample.value := by
  cases hw : sample.witness with
  | none =>
    simp only [Supplies, hw] at hs
    rw [hs.1, hs.2]
    cases r <;> simp [DataOrigin, initialValue, WriteValue]
  | some id =>
    simp only [Supplies, hw] at hs
    obtain ⟨w, hm, _, hv, hi⟩ := hs
    rw [hv, hi]
    exact h r w hm

theorem originInvariant_initial (v₀ : α) : OriginInvariant (n := n) v₀ initial := by
  simp [OriginInvariant, initial]


theorem threads_update_origin (origin : Nat → α → Prop) (s : State n α) (p : Process n)
    (t' : Option (Thread n α))
    (ht : ∀ q t, s.threads q = some t → PhaseOrigin origin t)
    (ht' : ∀ t, t' = some t → PhaseOrigin origin t) :
    ∀ q t, (withThread s p t').threads q = some t → PhaseOrigin origin t := by
  intro q t hq
  by_cases hqp : q = p
  · subst q
    exact ht' t (by simpa [withThread] using hq)
  · exact ht q t (by simpa [withThread, Function.update_of_ne hqp] using hq)

theorem originInvariant_step {v₀ : α} {s s' : State n α} {a : Action n}
    (step : Step v₀ s a s') (h : OriginInvariant v₀ s) : OriginInvariant v₀ s' := by
  have mono := step_writeValue_mono step
  have hw := fun r w hm => dataOrigin_mono mono r w.index w.value (h.1 r w hm)
  have ht := fun p t hp => phaseOrigin_mono mono t (h.2.1 p t hp)
  have hc := fun c time sample hm hr => mono _ _ (h.2.2 c time sample hm hr)
  cases step with
  | invokeWriter v free =>
    refine ⟨hw, threads_update_origin _ s .writer _ ht ?_, ?_⟩
    · intro t heq
      cases heq
      apply writerLoop_programOrigin
      exact Or.inr ⟨⟨s.clock, .writer, s.clock, s.nextWrite, some v, none⟩,
        List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, rfl⟩
    · intro c time sample hm hr
      simp only [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact hc c time sample hm hr
      · cases hr
  | invokeReader j free =>
    refine ⟨hw, threads_update_origin _ s (.reader j) _ ht ?_, ?_⟩
    · intro t heq
      cases heq
      exact readerProgram_programOrigin _ _ j
    · intro c time sample hm hr
      simp only [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact hc c time sample hm hr
      · cases hr
  | order p t next b active control =>
    refine ⟨hw, threads_update_origin _ s p _ ht ?_, hc⟩
    intro u heq
    cases heq
    have hp := ht p t active
    rw [PhaseOrigin, control] at hp
    exact hp b
  | token p t x y choice next active control ha hb =>
    refine ⟨hw, threads_update_origin _ s p _ ht ?_, hc⟩
    intro u heq
    cases heq
    have hp := ht p t active
    rw [PhaseOrigin, control] at hp
    exact hp choice ha hb
  | beginRead p t r next active control =>
    refine ⟨hw, threads_update_origin _ s p _ ht ?_, hc⟩
    intro u heq
    cases heq
    have hp := ht p t active
    rw [PhaseOrigin, control] at hp
    exact hp
  | endRead p t r start next sample active control regular supplies =>
    refine ⟨hw, threads_update_origin _ s p _ ht ?_, hc⟩
    intro u heq
    cases heq
    have hp := ht p t active
    rw [PhaseOrigin, control] at hp
    exact hp _ (fun _ _ hv => hv) sample (supplies_dataOrigin v₀ s h.1 r sample supplies)
  | beginWrite p t r value next active control owner =>
    have hp := ht p t active
    rw [PhaseOrigin, control] at hp
    refine ⟨?_, threads_update_origin _ s p _ ht ?_, hc⟩
    · intro r' w hm
      by_cases hr : r' = r
      · subst r'
        simp only [Function.update_self, List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · exact hw r w hm
        · exact hp.1
      · simp only [Function.update_of_ne hr] at hm
        exact hw r' w hm
    · intro u heq
      cases heq
      exact hp.2
  | endWrite p t r start next active control =>
    have hp := ht p t active
    rw [PhaseOrigin, control] at hp
    refine ⟨?_, threads_update_origin _ s p _ ht ?_, hc⟩
    · intro r' w hm
      by_cases hr : r' = r
      · subst r'
        simp only [Function.update_self, closeWrite, List.mem_map] at hm
        obtain ⟨old, hm, heq⟩ := hm
        have hold := hw r old hm
        split at heq <;> cases heq <;> exact hold
      · simp only [Function.update_of_ne hr] at hm
        exact hw r' w hm
    · intro u heq
      cases heq
      exact hp
  | respond p t result active control =>
    refine ⟨hw, threads_update_origin _ s p none ht (by simp), ?_⟩
    intro c time sample hm hr
    obtain ⟨old, hm, heq⟩ := List.mem_map.mp hm
    split at heq
    · cases heq
      have hp := ht p t active
      rw [PhaseOrigin, control] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      exact hp sample hr.2
    · cases heq
      exact hc _ time sample hm hr
  | idle => exact ⟨hw, ht, hc⟩


theorem originInvariant_trace {v₀ : α} {s s' : State n α} {actions : List (Action n)}
    (trace : (lts v₀).MTr s actions s') (h : OriginInvariant v₀ s) : OriginInvariant v₀ s' := by
  induction trace with
  | refl => exact h
  | stepL step tail ih => exact ih (originInvariant_step step h)

theorem originInvariant_reachable {v₀ : α} {s : State n α} (h : Reachable v₀ s) :
    OriginInvariant v₀ s := by
  obtain ⟨actions, trace⟩ := h
  exact originInvariant_trace trace (originInvariant_initial v₀)

/-- The returned ghost source and payload come from initialization or an actual
invoked writer. No criterion, no-forwarding-error, or payload-equality premise. -/
theorem returned_writeValue {v₀ : α} {s : State n α} (h : Reachable v₀ s)
    (c : Call n α) (sample : Sample α) (hc : c ∈ s.calls) (hr : Returned c sample) :
    WriteValue v₀ (fun c => c ∈ s.calls) sample.source sample.value := by
  obtain ⟨j, time, _, hr⟩ := hr
  exact (originInvariant_reachable h).2.2 c time sample hc hr


/-- Invocation timestamps in the saved history are strictly in the past. -/
def CallsPast (s : State n α) : Prop := ∀ c ∈ s.calls, c.invoked < s.clock

theorem step_clock {v₀ : α} {s s' : State n α} {a : Action n}
    (step : Step v₀ s a s') : s'.clock = s.clock + 1 := by
  cases step <;> rfl

theorem callsPast_step {v₀ : α} {s s' : State n α} {a : Action n}
    (step : Step v₀ s a s') (h : CallsPast s) : CallsPast s' := by
  have old : ∀ c ∈ s.calls, c.invoked < s.clock + 1 := fun c hc => Nat.lt_succ_of_lt (h c hc)
  cases step with
  | invokeWriter v free =>
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact old c hc
    · have := List.mem_singleton.mp hc
      subst c
      exact Nat.lt_succ_self _
  | invokeReader j free =>
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact old c hc
    · have := List.mem_singleton.mp hc
      subst c
      exact Nat.lt_succ_self _
  | respond p t result active control =>
    intro c hc
    obtain ⟨d, hd, heq⟩ := List.mem_map.mp hc
    have hh := old d hd
    split at heq <;> cases heq <;> exact hh
  | _ => exact old

theorem callsPast_reachable {v₀ : α} {s : State n α} (h : Reachable v₀ s) : CallsPast s := by
  obtain ⟨actions, trace⟩ := h
  have general : ∀ {s s' : State n α} {actions}, (lts v₀).MTr s actions s' → CallsPast s → CallsPast s' := by
    intro s s' actions trace hs
    induction trace with
    | refl => exact hs
    | stepL step tail ih => exact ih (callsPast_step step hs)
  exact general trace (by simp [CallsPast, initial])

def TimedWriteValue (v₀ : α) (history : Call n α → Prop) (time index : Nat) (value : α) : Prop :=
  (index = 0 ∧ value = v₀) ∨
  ∃ c, history c ∧ c.process = .writer ∧ c.writeIndex = index ∧
    c.argument = some value ∧ c.invoked < time

theorem timedWriteValue_mono {v₀ : α} {s s' : State n α} {a : Action n}
    (step : Step v₀ s a s') (time i : Nat) (v : α)
    (hv : TimedWriteValue v₀ (fun c => c ∈ s.calls) time i v) :
    TimedWriteValue v₀ (fun c => c ∈ s'.calls) time i v := by
  rcases hv with hv | ⟨c, hc, hw, hi, ha, ht⟩
  · exact Or.inl hv
  · obtain ⟨d, hd, he⟩ := step_call_extension step c hc
    exact Or.inr ⟨d, hd, he.2.1.trans hw, he.2.2.2.1.trans hi,
      he.2.2.2.2.trans ha, by simpa [he.2.2.1] using ht⟩

def TimedResponses (v₀ : α) (s : State n α) : Prop :=
  ∀ c time sample, c ∈ s.calls → c.response = some (time, some sample) →
    TimedWriteValue v₀ (fun c => c ∈ s.calls) time sample.source sample.value

theorem timedResponses_step {v₀ : α} {s s' : State n α} {a : Action n}
    (step : Step v₀ s a s') (hi : OriginInvariant v₀ s) (hp : CallsPast s)
    (h : TimedResponses v₀ s) : TimedResponses v₀ s' := by
  have old := fun c time sample hc hr => timedWriteValue_mono step _ _ _ (h c time sample hc hr)
  cases step with
  | invokeWriter v free =>
    intro c time sample hc hr
    rcases List.mem_append.mp hc with hc | hc
    · exact old c time sample hc hr
    · cases List.mem_singleton.mp hc
      cases hr
  | invokeReader j free =>
    intro c time sample hc hr
    rcases List.mem_append.mp hc with hc | hc
    · exact old c time sample hc hr
    · cases List.mem_singleton.mp hc
      cases hr
  | respond p t result active control =>
    intro c time sample hc hr
    obtain ⟨d, hd, heq⟩ := List.mem_map.mp hc
    split at heq
    · cases heq
      have ht := hi.2.1 p t active
      rw [PhaseOrigin, control] at ht
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      rcases ht sample hr.2 with hv | ⟨w, hw, hpw, hwi, hwv⟩
      · exact Or.inl hv
      · obtain ⟨w', hw', he⟩ := step_call_extension (Step.respond (v₀ := v₀) s p t result active control) w hw
        exact Or.inr ⟨w', hw', he.2.1.trans hpw, he.2.2.2.1.trans hwi,
          he.2.2.2.2.trans hwv, by rw [he.2.2.1, ← hr.1]; exact hp w hw⟩
    · cases heq
      exact old _ time sample hd hr
  | _ => exact old

theorem timedResponses_reachable {v₀ : α} {s : State n α} (h : Reachable v₀ s) :
    TimedResponses v₀ s := by
  obtain ⟨actions, trace⟩ := h
  have general : ∀ {s s' : State n α} {actions}, (lts v₀).MTr s actions s' →
      OriginInvariant v₀ s → CallsPast s → TimedResponses v₀ s → TimedResponses v₀ s' := by
    intro s s' actions trace hi hp hr
    induction trace with
    | refl => exact hr
    | stepL step tail ih =>
      exact ih (originInvariant_step step hi) (callsPast_step step hp) (timedResponses_step step hi hp hr)
  exact general trace (originInvariant_initial v₀) (by simp [CallsPast, initial])
    (by simp [TimedResponses, initial])

/-- API provenance is established independently of the no-regression criterion. -/
theorem api_provenance_reachable {v₀ : α} {s : State n α} (h : Reachable v₀ s) :
    Provenance v₀ (fun c => c ∈ s.calls) APIBefore := by
  intro c sample hc hr
  refine ⟨returned_writeValue h c sample hc hr, ?_⟩
  obtain ⟨j, time, _, hr⟩ := hr
  rcases timedResponses_reachable h c time sample hc hr with hi | ⟨w, hw, hp, hi, _, ht⟩
  · exact Or.inl hi.1
  · refine Or.inr ⟨w, hw, hp, hi, ?_⟩
    rintro ⟨time', result, hr', hb⟩
    rw [hr] at hr'
    cases hr'
    exact Nat.lt_asymm ht hb

end MultiReaderAtomic
