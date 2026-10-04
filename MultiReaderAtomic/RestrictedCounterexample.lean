import MultiReaderAtomic.Restricted

/-! A two-reader certificate retaining writer RC-before-FC order. The disputed
notice register remains regular, so different reads may observe new then old
while the same FC write is unfinished. -/
namespace MultiReaderAtomic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem restricted_reachable_step {v₀ : α} {s s' : State n α} {a : Action n}
    (past : RestrictedReachable v₀ s) (step : RestrictedStep v₀ s a s') :
    RestrictedReachable v₀ s' := by
  obtain ⟨actions, trace⟩ := past
  exact ⟨actions ++ [a], Cslib.LTS.MTr.comp (restrictedLts v₀) trace
    (Cslib.LTS.MTr.stepL step Cslib.LTS.MTr.refl)⟩

theorem restricted_order_true {v₀ : α} (s : State n α) (p : Process n)
    (t : Thread n α) (next : Bool → Program n α)
    (active : s.threads p = some t) (control : t.phase = .ready (.order next)) :
    RestrictedStep v₀ s (.localStep p)
      (withThread s p (some {t with phase := .ready (next true)})) := by
  refine ⟨Step.order s p t next true active control, ?_⟩
  cases p with
  | reader j => exact Or.inl (by intro h; cases h)
  | writer =>
    right
    intro u f hu hf
    have eq : t = u := Option.some.inj (active.symm.trans hu)
    subst u
    rw [control] at hf
    cases hf
    simp [withThread]

theorem restricted_token_step {v₀ : α} (s : State n α) (p : Process n)
    (t : Thread n α) (a b choice : Token) (next : Token → Program n α)
    (active : s.threads p = some t) (control : t.phase = .ready (.token a b next))
    (ha : choice ≠ a) (hb : choice ≠ b) :
    RestrictedStep v₀ s (.localStep p)
      (withThread s p (some {t with phase := .ready (next choice)})) := by
  refine ⟨Step.token s p t a b choice next active control ha hb, ?_⟩
  cases p with
  | reader j => exact Or.inl (by intro h; cases h)
  | writer =>
    right
    intro u f hu hf
    have eq : t = u := Option.some.inj (active.symm.trans hu)
    subst u
    rw [control] at hf
    cases hf

inductive RCEInput where
  | invokeWriter (value : Nat)
  | invokeReader (j : Fin 2)
  | order (p : Process 2)
  | token (p : Process 2) (value : Token)
  | beginAccess (p : Process 2)
  | endRead (p : Process 2) (data : Nat) (control : Token) (witness : Option Nat) (source : Nat)
  | endWrite (p : Process 2)
  | respond (p : Process 2)

structure RCECertified (s : State 2 Nat) where
  state : State 2 Nat
  action : Action 2
  step : RestrictedStep 0 s action state

def rceSample (r : Register 2) (data : Nat) (control : Token)
    (witness : Option Nat) (source : Nat) : Sample (Value Nat r) :=
  match r with
  | .buff1 | .buff2 => ⟨data, witness, source⟩
  | .level | .wc _ | .rc _ | .fc _ => ⟨control, witness, source⟩

def rceValueDecidable (r : Register 2) : DecidableEq (Value Nat r) := by
  cases r <;> exact inferInstance

/-- Every accepted input has its original and its restricted transition proof.
All order inputs evaluate the left operand first, including reader pairs. -/
def rceExecute (s : State 2 Nat) : RCEInput → Option (RCECertified s)
  | .invokeWriter value =>
    match h : s.threads .writer with
    | none => some ⟨_, _, ⟨Step.invokeWriter s value h, Or.inl (by intro h; cases h)⟩⟩
    | some _ => none
  | .invokeReader j =>
    match h : s.threads (.reader j) with
    | none => some ⟨_, _, ⟨Step.invokeReader s j h, Or.inl (by intro h; cases h)⟩⟩
    | some _ => none
  | .order p =>
    match ht : s.threads p with
    | none => none
    | some t => match hp : t.phase with
      | .ready (.order next) => some ⟨_, _, restricted_order_true s p t next ht hp⟩
      | _ => none
  | .token p value =>
    match ht : s.threads p with
    | none => none
    | some t => match hp : t.phase with
      | .ready (.token a b next) =>
        if ha : value ≠ a then if hb : value ≠ b then
          some ⟨_, _, restricted_token_step s p t a b value next ht hp ha hb⟩ else none else none
      | _ => none
  | .beginAccess p =>
    match ht : s.threads p with
    | none => none
    | some t => match hp : t.phase with
      | .ready (.read r next) => some ⟨_, _, ⟨Step.beginRead s p t r next ht hp,
          Or.inl (by intro h; cases h)⟩⟩
      | .ready (.write r value next) =>
        if owner : registerOwner r = p then some ⟨_, _, ⟨Step.beginWrite s p t r value next ht hp owner,
          Or.inl (by intro h; cases h)⟩⟩
        else none
      | _ => none
  | .endRead p data control witness source =>
    match ht : s.threads p with
    | none => none
    | some t => match hp : t.phase with
      | .reading r start next =>
        let sample := rceSample r data control witness source
        letI := rceValueDecidable r
        if regular : ceEligible (s.writes r) start s.clock witness = true then
          if supplies : ceSupplies (initialValue 0 r) (s.writes r) sample = true then
            some ⟨_, _, ⟨Step.endRead s p t r start next sample ht hp
              (by cases r <;> exact ceEligible_sound _ _ _ _ regular)
              (ceSupplies_sound _ _ _ supplies), Or.inl (by intro h; cases h)⟩⟩
          else none
        else none
      | _ => none
  | .endWrite p =>
    match ht : s.threads p with
    | none => none
    | some t => match hp : t.phase with
      | .writing r start next => some ⟨_, _, ⟨Step.endWrite s p t r start next ht hp,
          Or.inl (by intro h; cases h)⟩⟩
      | _ => none
  | .respond p =>
    match ht : s.threads p with
    | none => none
    | some t => match hp : t.phase with
      | .ready (.done result) => some ⟨_, _, ⟨Step.respond s p t result ht hp,
          Or.inl (by intro h; cases h)⟩⟩
      | _ => none

structure RCEProgress where
  state : State 2 Nat
  reachable : RestrictedReachable 0 state
  failures : Nat

def rceAdvance (progress : RCEProgress) (input : RCEInput) : RCEProgress :=
  match rceExecute progress.state input with
  | none => { progress with failures := progress.failures + 1 }
  | some next => ⟨next.state, restricted_reachable_step progress.reachable next.step, progress.failures⟩

def rceRun (inputs : List RCEInput) : RCEProgress :=
  inputs.foldl rceAdvance ⟨initial, initial_restricted_reachable 0, 0⟩

/-- All writer and reader operand pairs are evaluated left first. -/
def regularFcSchedule : List RCEInput :=
  [
    .invokeWriter 1,
    .order .writer,
    .beginAccess .writer,
    .endRead .writer 0 1 none 0,
    .beginAccess .writer,
    .endRead .writer 0 1 none 0,
    .token .writer 2,
    .beginAccess .writer,
    .endWrite .writer,
    .order .writer,
    .beginAccess .writer,
    .endRead .writer 0 1 none 0,
    .beginAccess .writer,
    .endRead .writer 0 1 none 0,
    .token .writer 2,
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .endWrite .writer,
    .invokeReader 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 8) 1,
    .beginAccess (.reader 0),
    .endWrite (.reader 0),
    .beginAccess (.reader 0),
    .endRead (.reader 0) 1 0 (some 20) 1,
    .order (.reader 0),
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 1 none 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 8) 1,
    .order (.reader 0),
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 1 none 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 16) 1,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 22) 1,
    .order (.reader 0),
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 27) 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 8) 1,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 27) 0,
    .beginAccess (.reader 0),
    .endWrite (.reader 0),
    .respond (.reader 0),
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .endWrite .writer,
    .respond .writer,
    .invokeWriter 2,
    .order .writer,
    .beginAccess .writer,
    .endRead .writer 0 2 (some 27) 0,
    .beginAccess .writer,
    .endRead .writer 0 2 (some 50) 0,
    .token .writer 0,
    .beginAccess .writer,
    .endWrite .writer,
    .order .writer,
    .beginAccess .writer,
    .endRead .writer 0 1 none 0,
    .beginAccess .writer,
    .endRead .writer 0 1 none 0,
    .token .writer 0,
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .endWrite .writer,
    .invokeReader 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 0 (some 65) 2,
    .beginAccess (.reader 0),
    .endWrite (.reader 0),
    .beginAccess (.reader 0),
    .endRead (.reader 0) 2 0 (some 77) 2,
    .order (.reader 0),
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 50) 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 0 (some 65) 2,
    .order (.reader 0),
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 1 none 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 0 (some 73) 2,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 79) 2,
    .order (.reader 0),
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 0 (some 84) 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 0 (some 65) 2,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 0 (some 84) 0,
    .beginAccess (.reader 0),
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .endWrite .writer,
    .respond .writer,
    .invokeWriter 3,
    .order .writer,
    .beginAccess .writer,
    .endRead .writer 0 0 (some 84) 0,
    .beginAccess .writer,
    .endRead .writer 0 0 (some 107) 0,
    .token .writer 2,
    .beginAccess .writer,
    .endWrite .writer,
    .order .writer,
    .beginAccess .writer,
    .endRead .writer 0 1 none 0,
    .beginAccess .writer,
    .endRead .writer 0 1 none 0,
    .token .writer 2,
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .invokeReader 1,
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 2 (some 128) 3,
    .beginAccess (.reader 1),
    .endWrite (.reader 1),
    .beginAccess (.reader 1),
    .endRead (.reader 1) 3 0 (some 132) 3,
    .order (.reader 1),
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 2 (some 50) 0,
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 2 (some 120) 3,
    .order (.reader 1),
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 1 none 0,
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 2 (some 128) 3,
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 1 (some 130) 3,
    .order (.reader 1),
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 2 (some 136) 0,
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 2 (some 128) 3,
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 2 (some 136) 0,
    .beginAccess (.reader 1),
    .endWrite (.reader 1),
    .respond (.reader 1),
    .invokeReader 1,
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 2 (some 128) 3,
    .beginAccess (.reader 1),
    .endWrite (.reader 1),
    .beginAccess (.reader 1),
    .endRead (.reader 1) 2 0 (some 77) 2,
    .order (.reader 1),
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 2 (some 50) 0,
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 2 (some 120) 3,
    .order (.reader 1),
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 2 (some 159) 0,
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 2 (some 128) 3,
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 1 (some 130) 3,
    .order (.reader 1),
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 2 (some 165) 0,
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 2 (some 128) 3,
    .beginAccess (.reader 1),
    .endRead (.reader 1) 0 2 (some 165) 0,
    .beginAccess (.reader 1),
    .endWrite (.reader 1),
    .respond (.reader 1),
    .endWrite (.reader 0),
    .respond (.reader 0),
    .endWrite .writer,
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .endWrite .writer,
    .respond .writer
  ]

def regularFcRun : RCEProgress := rceRun regularFcSchedule

/-- All 200 requested inputs satisfy the original and restricted semantics. -/
theorem regularFc_no_failed_inputs : regularFcRun.failures = 0 := by rfl

def regularFcNewRead : Call 2 Nat :=
  ⟨133, .reader 1, 133, 0, none, some (161, some ⟨3, some 132, 3⟩)⟩

def regularFcOldRead : Call 2 Nat :=
  ⟨162, .reader 1, 162, 0, none, some (190, some ⟨2, some 77, 2⟩)⟩

/-- Kernel-normalized final history; every call has a response. -/
theorem regularFc_calls : regularFcRun.state.calls =
    [⟨1, .writer, 1, 1, some 1, some (57, none)⟩,
     ⟨24, .reader 0, 24, 0, none, some (52, some ⟨1, some 20, 1⟩)⟩,
     ⟨58, .writer, 58, 2, some 2, some (112, none)⟩,
     ⟨81, .reader 0, 81, 0, none, some (192, some ⟨2, some 77, 2⟩)⟩,
     ⟨113, .writer, 113, 3, some 3, some (200, none)⟩,
     regularFcNewRead, regularFcOldRead] := by rfl

theorem regularFc_reachable : RestrictedReachable 0 regularFcRun.state := regularFcRun.reachable

theorem regularFc_all_completed : ∀ c ∈ regularFcRun.state.calls, Completed c := by
  rw [regularFc_calls]
  simp [Completed, regularFcNewRead, regularFcOldRead]

theorem regularFc_all_primitives_finished :
    ∀ e ∈ regularFcRun.state.primitives, e.finish.isSome = true := by
  have h : regularFcRun.state.primitives.all (fun e => e.finish.isSome) = true := by rfl
  exact List.all_eq_true.mp h

theorem regularFc_all_threads_idle : ∀ p, regularFcRun.state.threads p = none := by
  intro p
  cases p with
  | writer => rfl
  | reader j =>
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl <;> rfl

theorem regularFc_new_mem : regularFcNewRead ∈ regularFcRun.state.calls := by
  rw [regularFc_calls]
  simp

theorem regularFc_old_mem : regularFcOldRead ∈ regularFcRun.state.calls := by
  rw [regularFc_calls]
  simp

theorem regularFc_new_returned : Returned regularFcNewRead ⟨3, some 132, 3⟩ :=
  ⟨1, 161, rfl, rfl⟩

theorem regularFc_old_returned : Returned regularFcOldRead ⟨2, some 77, 2⟩ :=
  ⟨1, 190, rfl, rfl⟩

theorem regularFc_apiBefore : APIBefore regularFcNewRead regularFcOldRead :=
  ⟨161, some ⟨3, some 132, 3⟩, rfl, by decide⟩

/-- The actual RC-before-FC history violates no-new-then-old. -/
theorem regularFc_not_indexedCriterion :
    ¬ IndexedCriterion (fun c => c ∈ regularFcRun.state.calls) APIBefore := by
  intro h
  have bad := h.1 regularFcNewRead regularFcOldRead _ _
    regularFc_new_mem regularFc_old_mem regularFc_new_returned
    regularFc_old_returned regularFc_apiBefore
  exact (by decide : ¬ (3 ≤ 2)) bad

/-- Fixing writer operand order alone does not establish the restricted target. -/
theorem regularFc_not_restrictedFiniteCorrectness : ¬ RestrictedFiniteCorrectness 2 Nat := by
  intro h
  exact regularFc_not_indexedCriterion
    (h 0 regularFcRun.state (by decide) regularFc_reachable).2.2.1

/-- The bad reads are also separated under the source's primitive lift. -/
theorem regularFc_sourceBefore : SourceBefore regularFcRun.state.primitives
    regularFcNewRead regularFcOldRead := by
  refine ⟨⟨161, some ⟨3, some 132, 3⟩, rfl⟩,
    ⟨190, some ⟨2, some 77, 2⟩, rfl⟩, ?_, ?_, ?_⟩
  · have h : regularFcRun.state.primitives.any (fun e => decide (e.call = 133)) = true := by rfl
    simpa only [List.any_eq_true, decide_eq_true_eq, regularFcNewRead] using h
  · have h : regularFcRun.state.primitives.any (fun e => decide (e.call = 162)) = true := by rfl
    simpa only [List.any_eq_true, decide_eq_true_eq, regularFcOldRead] using h
  · have h : regularFcRun.state.primitives.all (fun a =>
        regularFcRun.state.primitives.all (fun b =>
          if a.call = 133 ∧ b.call = 162 then cePrimitiveBefore a b else true)) = true := by rfl
    intro a ha b hb hca hcb
    have hpair := List.all_eq_true.mp (List.all_eq_true.mp h a ha) b hb
    simp only [regularFcNewRead, regularFcOldRead] at hca hcb
    simpa only [hca, hcb, and_self, ↓reduceIte, cePrimitiveBefore_iff] using hpair

theorem regularFc_not_sourceCriterion :
    ¬ IndexedCriterion (fun c => c ∈ regularFcRun.state.calls)
      (SourceBefore regularFcRun.state.primitives) := by
  intro h
  have bad := h.1 regularFcNewRead regularFcOldRead _ _
    regularFc_new_mem regularFc_old_mem regularFc_new_returned
    regularFc_old_returned regularFc_sourceBefore
  exact (by decide : ¬ (3 ≤ 2)) bad

/-- The old notice is 2, the overlapping new notice is 0, and both calls finish. -/
theorem regularFc_notice_writes : regularFcRun.state.writes (.fc 0) =
    [⟨50, 24, 0, 2, 50, some 51⟩, ⟨107, 81, 0, 0, 107, some 191⟩] := by rfl

def RegularFcRecordedRead (id call : Nat) (r : Register 2) (finish witness : Nat) : Prop :=
  ∃ e ∈ regularFcRun.state.primitives, e.id = id ∧ e.call = call ∧
    e.register = r ∧ e.isWrite = false ∧ e.start = id ∧
    e.finish = some finish ∧ e.witness = some witness

/-- Writer W3 observes the pending notice 0 at 117–118. -/
theorem regularFc_writer_new_notice : RegularFcRecordedRead 117 113 (.fc 0) 118 107 := by
  have h : regularFcRun.state.primitives.any (fun e => decide (e.id = 117 ∧ e.call = 113 ∧
      e.register = .fc 0 ∧ e.isWrite = false ∧ e.start = 117 ∧
      e.finish = some 118 ∧ e.witness = some 107)) = true := by rfl
  simpa only [RegularFcRecordedRead, List.any_eq_true, decide_eq_true_eq] using h

/-- The later reader observes the old notice 2 at 141–142 during the same write. -/
theorem regularFc_reader_old_notice : RegularFcRecordedRead 141 133 (.fc 0) 142 50 := by
  have h : regularFcRun.state.primitives.any (fun e => decide (e.id = 141 ∧ e.call = 133 ∧
      e.register = .fc 0 ∧ e.isWrite = false ∧ e.start = 141 ∧
      e.finish = some 142 ∧ e.witness = some 50)) = true := by rfl
  simpa only [RegularFcRecordedRead, List.any_eq_true, decide_eq_true_eq] using h

theorem regularFc_input_count : regularFcSchedule.length = 200 := by rfl

/-- Even after both FC writes finish, their saved intervals admit the exact
new-then-old control observations used by the execution. -/
theorem regularFc_control_new_then_old_allowed :
    Eligible (regularFcRun.state.writes (.fc 0)) 117 118 (some 107) ∧
    Supplies (1 : Token) (regularFcRun.state.writes (.fc 0)) ⟨0, some 107, 0⟩ ∧
    Eligible (regularFcRun.state.writes (.fc 0)) 141 142 (some 50) ∧
    Supplies (1 : Token) (regularFcRun.state.writes (.fc 0)) ⟨2, some 50, 0⟩ := by
  rw [regularFc_notice_writes]
  simp [Eligible, Precedes, Supplies]

end MultiReaderAtomic
