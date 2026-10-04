import MultiReaderAtomic.CausalTrace

/-! A proof-producing endpoint executor for checking a concrete admitted schedule.
It uses the original Step constructors and regular-read witness conditions. -/
namespace MultiReaderAtomic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def cePrecedes (w : WriteRecord α) (start : Nat) : Bool :=
  match w.finish with | none => false | some finish => decide (finish < start)

theorem cePrecedes_iff (w : WriteRecord α) (start : Nat) :
    cePrecedes w start = true ↔ Precedes w start := by
  cases h : w.finish <;> simp [cePrecedes, Precedes, h]

def ceOverlap (w : WriteRecord α) (start : Nat) : Bool :=
  match w.finish with | none => true | some finish => decide (start < finish)

theorem ceOverlap_iff (w : WriteRecord α) (start : Nat) :
    ceOverlap w start = true ↔ ∀ t, w.finish = some t → start < t := by
  cases h : w.finish <;> simp [ceOverlap, h]

def ceEligible (ws : List (WriteRecord α)) (start finish : Nat) : Option Nat → Bool
  | none => ws.all fun w => !(cePrecedes w start)
  | some id => ws.any fun w => decide (w.id = id) && decide (w.start < finish) &&
      ((cePrecedes w start && ws.all (fun other =>
        !(cePrecedes other start) || decide (other.start ≤ w.start))) || ceOverlap w start)

theorem ceEligible_sound (ws : List (WriteRecord α)) (start finish : Nat) (witness : Option Nat)
    (h : ceEligible ws start finish witness = true) : Eligible ws start finish witness := by
  cases witness with
  | none =>
    simp only [ceEligible, List.all_eq_true, Bool.not_eq_true'] at h
    intro w hw hp
    have := h w hw
    rw [(cePrecedes_iff w start).mpr hp] at this
    contradiction
  | some id =>
    simp only [ceEligible, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at h
    obtain ⟨w, hw, ⟨hid, htime⟩, choice⟩ := h
    refine ⟨w, hw, hid, htime, ?_⟩
    rcases choice with ⟨hp, hmax⟩ | overlap
    · left
      refine ⟨(cePrecedes_iff w start).mp hp, ?_⟩
      intro other ho hp
      rcases hmax other ho with hn | le
      · rw [(cePrecedes_iff other start).mpr hp] at hn
        contradiction
      · exact le
    · exact Or.inr ((ceOverlap_iff w start).mp overlap)

def ceSupplies [DecidableEq α] (initial : α) (ws : List (WriteRecord α)) (sample : Sample α) : Bool :=
  match sample.witness with
  | none => decide (sample.value = initial) && decide (sample.source = 0)
  | some id => ws.any fun w => decide (w.id = id) && decide (sample.value = w.value) &&
      decide (sample.source = w.index)

theorem ceSupplies_sound [DecidableEq α] (initial : α) (ws : List (WriteRecord α)) (sample : Sample α)
    (h : ceSupplies initial ws sample = true) : Supplies initial ws sample := by
  unfold ceSupplies at h
  unfold Supplies
  split at h <;> simp_all [List.any_eq_true, Bool.and_eq_true, and_assoc]

inductive CEInput where
  | invokeWriter (value : Nat)
  | invokeReader
  | order (p : Process 1) (leftFirst : Bool)
  | token (p : Process 1) (value : Token)
  | beginAccess (p : Process 1)
  | endRead (p : Process 1) (data : Nat) (control : Token) (witness : Option Nat) (source : Nat)
  | endWrite (p : Process 1)
  | respond (p : Process 1)

structure CECertified (s : State 1 Nat) where
  state : State 1 Nat
  action : Action 1
  step : Step 0 s action state

def ceSample (r : Register 1) (data : Nat) (control : Token)
    (witness : Option Nat) (source : Nat) : Sample (Value Nat r) :=
  match r with
  | .buff1 | .buff2 => ⟨data, witness, source⟩
  | .level | .wc _ | .rc _ | .fc _ => ⟨control, witness, source⟩

def ceValueDecidable (r : Register 1) : DecidableEq (Value Nat r) := by
  cases r <;> exact inferInstance

/-- Every returned state comes with the exact original transition proof. -/
def ceExecute (s : State 1 Nat) : CEInput → Option (CECertified s)
  | .invokeWriter value =>
    match h : s.threads .writer with
    | none => some ⟨_, _, Step.invokeWriter s value h⟩
    | some _ => none
  | .invokeReader =>
    match h : s.threads (.reader 0) with
    | none => some ⟨_, _, Step.invokeReader s 0 h⟩
    | some _ => none
  | .order p b =>
    match ht : s.threads p with
    | none => none
    | some t => match hp : t.phase with
      | .ready (.order next) => some ⟨_, _, Step.order s p t next b ht hp⟩
      | _ => none
  | .token p value =>
    match ht : s.threads p with
    | none => none
    | some t => match hp : t.phase with
      | .ready (.token a b next) =>
        if ha : value ≠ a then if hb : value ≠ b then
          some ⟨_, _, Step.token s p t a b value next ht hp ha hb⟩ else none else none
      | _ => none
  | .beginAccess p =>
    match ht : s.threads p with
    | none => none
    | some t => match hp : t.phase with
      | .ready (.read r next) => some ⟨_, _, Step.beginRead s p t r next ht hp⟩
      | .ready (.write r value next) =>
        if owner : registerOwner r = p then some ⟨_, _, Step.beginWrite s p t r value next ht hp owner⟩
        else none
      | _ => none
  | .endRead p data control witness source =>
    match ht : s.threads p with
    | none => none
    | some t => match hp : t.phase with
      | .reading r start next =>
        let sample := ceSample r data control witness source
        letI := ceValueDecidable r
        if regular : ceEligible (s.writes r) start s.clock witness = true then
          if supplies : ceSupplies (initialValue 0 r) (s.writes r) sample = true then
            some ⟨_, _, Step.endRead s p t r start next sample ht hp
              (by cases r <;> exact ceEligible_sound _ _ _ _ regular)
              (ceSupplies_sound _ _ _ supplies)⟩
          else none
        else none
      | _ => none
  | .endWrite p =>
    match ht : s.threads p with
    | none => none
    | some t => match hp : t.phase with
      | .writing r start next => some ⟨_, _, Step.endWrite s p t r start next ht hp⟩
      | _ => none
  | .respond p =>
    match ht : s.threads p with
    | none => none
    | some t => match hp : t.phase with
      | .ready (.done result) => some ⟨_, _, Step.respond s p t result ht hp⟩
      | _ => none

structure CEProgress where
  state : State 1 Nat
  reachable : Reachable 0 state
  failures : Nat

def ceAdvance (progress : CEProgress) (input : CEInput) : CEProgress :=
  match ceExecute progress.state input with
  | none => { progress with failures := progress.failures + 1 }
  | some next => ⟨next.state, reachable_step progress.reachable next.step, progress.failures⟩

def ceRun (inputs : List CEInput) : CEProgress :=
  inputs.foldl ceAdvance ⟨initial, ⟨[], Cslib.LTS.MTr.refl⟩, 0⟩

/-- Delayed forwarding and a reverse-order writer cancellation. -/
def reverseOrderSchedule : List CEInput :=
  [
    .invokeWriter 1,
    .order .writer true,
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
    .invokeReader,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 8) 1,
    .beginAccess (.reader 0),
    .endWrite (.reader 0),
    .beginAccess (.reader 0),
    .endRead (.reader 0) 1 0 (some 12) 1,
    .order (.reader 0) true,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 1 none 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 8) 1,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 14) 1,
    .order (.reader 0) true,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 19) 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 8) 1,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 19) 0,
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .endWrite .writer,
    .respond .writer,
    .invokeWriter 2,
    .order .writer true,
    .beginAccess .writer,
    .endRead .writer 0 2 (some 19) 0,
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
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .endWrite .writer,
    .respond .writer,
    .invokeWriter 3,
    .order .writer false,
    .beginAccess .writer,
    .endRead .writer 0 1 none 0,
    .beginAccess (.reader 0),
    .endWrite (.reader 0),
    .respond (.reader 0),
    .invokeReader,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 0 (some 49) 2,
    .beginAccess (.reader 0),
    .endWrite (.reader 0),
    .beginAccess (.reader 0),
    .endRead (.reader 0) 2 0 (some 53) 2,
    .order (.reader 0) true,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 66) 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 0 (some 49) 2,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 0 (some 59) 2,
    .order (.reader 0) true,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 0 (some 72) 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 0 (some 49) 2,
    .respond (.reader 0),
    .beginAccess .writer,
    .endRead .writer 0 0 (some 72) 0,
    .token .writer 2,
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .endWrite .writer,
    .beginAccess .writer,
    .invokeReader,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 92) 3,
    .beginAccess (.reader 0),
    .endWrite (.reader 0),
    .beginAccess (.reader 0),
    .endRead (.reader 0) 3 0 (some 96) 3,
    .order (.reader 0) true,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 66) 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 92) 3,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 1 (some 94) 3,
    .order (.reader 0) true,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 100) 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 92) 3,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 100) 0,
    .beginAccess (.reader 0),
    .endWrite (.reader 0),
    .respond (.reader 0),
    .invokeReader,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 92) 3,
    .beginAccess (.reader 0),
    .endWrite (.reader 0),
    .beginAccess (.reader 0),
    .endRead (.reader 0) 2 0 (some 53) 2,
    .order (.reader 0) true,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 118) 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 92) 3,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 1 (some 94) 3,
    .order (.reader 0) true,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 124) 0,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 92) 3,
    .beginAccess (.reader 0),
    .endRead (.reader 0) 0 2 (some 124) 0,
    .beginAccess (.reader 0),
    .endWrite (.reader 0),
    .respond (.reader 0)
  ]

def reverseOrderRun : CEProgress := ceRun reverseOrderSchedule

/-- All requested inputs were accepted by their original Step constructors. -/
theorem reverseOrder_no_failed_inputs : reverseOrderRun.failures = 0 := by rfl

def reverseOrderNewRead : Call 1 Nat :=
  ⟨97, .reader 0, 97, 0, none, some (120, some ⟨3, some 96, 3⟩)⟩

def reverseOrderOldRead : Call 1 Nat :=
  ⟨121, .reader 0, 121, 0, none, some (144, some ⟨2, some 53, 2⟩)⟩

/-- This equality is normalized by the kernel, without native evaluation. -/
theorem reverseOrder_calls : reverseOrderRun.state.calls =
    [⟨1, .writer, 1, 1, some 1, some (41, none)⟩,
     ⟨16, .reader 0, 16, 0, none, some (68, some ⟨1, some 12, 1⟩)⟩,
     ⟨42, .writer, 42, 2, some 2, some (61, none)⟩,
     ⟨62, .writer, 62, 3, some 3, none⟩,
     ⟨69, .reader 0, 69, 0, none, some (88, some ⟨2, some 53, 2⟩)⟩,
     reverseOrderNewRead, reverseOrderOldRead] := by rfl

theorem reverseOrder_reachable : Reachable 0 reverseOrderRun.state := reverseOrderRun.reachable

theorem reverseOrder_new_mem : reverseOrderNewRead ∈ reverseOrderRun.state.calls := by
  rw [reverseOrder_calls]
  simp

theorem reverseOrder_old_mem : reverseOrderOldRead ∈ reverseOrderRun.state.calls := by
  rw [reverseOrder_calls]
  simp

theorem reverseOrder_new_returned : Returned reverseOrderNewRead ⟨3, some 96, 3⟩ :=
  ⟨0, 120, rfl, rfl⟩

theorem reverseOrder_old_returned : Returned reverseOrderOldRead ⟨2, some 53, 2⟩ :=
  ⟨0, 144, rfl, rfl⟩

theorem reverseOrder_apiBefore : APIBefore reverseOrderNewRead reverseOrderOldRead :=
  ⟨120, some ⟨3, some 96, 3⟩, rfl, by decide⟩

/-- The actual admitted history violates the required no-new-then-old conjunct. -/
theorem reverseOrder_not_indexedCriterion :
    ¬ IndexedCriterion (fun c => c ∈ reverseOrderRun.state.calls) APIBefore := by
  intro h
  have bad := h.1 reverseOrderNewRead reverseOrderOldRead _ _
    reverseOrder_new_mem reverseOrder_old_mem reverseOrder_new_returned
    reverseOrder_old_returned reverseOrder_apiBefore
  exact (by decide : ¬ (3 ≤ 2)) bad

/-- Both operand orders in the accepted model cannot satisfy the unchanged target. -/
theorem reverseOrder_not_finiteCorrectness : ¬ FiniteCorrectness 1 Nat := by
  intro h
  exact reverseOrder_not_indexedCriterion
    (h 0 reverseOrderRun.state (by decide) reverseOrder_reachable).2.2.1

def cePrimitiveBefore (a b : Primitive n) : Bool :=
  match a.finish with | none => false | some finish => decide (finish < b.start)

theorem cePrimitiveBefore_iff (a b : Primitive n) :
    cePrimitiveBefore a b = true ↔ PrimitiveBefore a b := by
  cases h : a.finish <;> simp [cePrimitiveBefore, PrimitiveBefore, h]

/-- The same two reads are also separated under the source's primitive lift. -/
theorem reverseOrder_sourceBefore : SourceBefore reverseOrderRun.state.primitives
    reverseOrderNewRead reverseOrderOldRead := by
  refine ⟨⟨120, some ⟨3, some 96, 3⟩, rfl⟩,
    ⟨144, some ⟨2, some 53, 2⟩, rfl⟩, ?_, ?_, ?_⟩
  · have h : reverseOrderRun.state.primitives.any (fun e => decide (e.call = 97)) = true := by rfl
    simpa only [List.any_eq_true, decide_eq_true_eq, reverseOrderNewRead, reverseOrderOldRead] using h
  · have h : reverseOrderRun.state.primitives.any (fun e => decide (e.call = 121)) = true := by rfl
    simpa only [List.any_eq_true, decide_eq_true_eq, reverseOrderNewRead, reverseOrderOldRead] using h
  · have h : reverseOrderRun.state.primitives.all (fun a =>
        reverseOrderRun.state.primitives.all (fun b =>
          if a.call = 97 ∧ b.call = 121 then cePrimitiveBefore a b else true)) = true := by rfl
    intro a ha b hb hca hcb
    have hpair := List.all_eq_true.mp (List.all_eq_true.mp h a ha) b hb
    simp only [reverseOrderNewRead, reverseOrderOldRead] at hca hcb
    simpa only [hca, hcb, and_self, ↓reduceIte, cePrimitiveBefore_iff] using hpair

theorem reverseOrder_not_sourceCriterion :
    ¬ IndexedCriterion (fun c => c ∈ reverseOrderRun.state.calls)
      (SourceBefore reverseOrderRun.state.primitives) := by
  intro h
  have bad := h.1 reverseOrderNewRead reverseOrderOldRead _ _
    reverseOrder_new_mem reverseOrder_old_mem reverseOrder_new_returned
    reverseOrder_old_returned reverseOrder_sourceBefore
  exact (by decide : ¬ (3 ≤ 2)) bad

end MultiReaderAtomic
