import ConcurrentReading.Integrity

namespace ConcurrentReading

set_option maxHeartbeats 4000000

/-- The index already published by clearing the first-buffer write flag. -/
def frontier (s : State α n) : Nat :=
  if s.writer.pc = 0 ∨ 7 ≤ s.writer.pc then s.writer.index else s.writer.index - 1

def OriginLE (d : Datum α) (k : Nat) : Prop := ∀ j, d.origin = some j → j ≤ k

def OriginGE (d : Datum α) (k : Nat) : Prop := ∀ j, d.origin = some j → k ≤ j

/-- Public buffers follow the writer's source index at their respective commit
steps; private copies never anticipate flag clearing. -/
def MemoryOrder (s : State α n) : Prop :=
  (s.writer.pc ≠ 0 → 0 < s.writer.index) ∧
  (s.memory .first).origin = some
    (if s.writer.pc = 0 ∨ 4 ≤ s.writer.pc then s.writer.index else s.writer.index - 1) ∧
  (s.memory .second).origin = some
    (if s.writer.pc = 0 ∨ s.writer.pc = 15 then s.writer.index else s.writer.index - 1) ∧
  (∀ i, OriginLE (s.memory (.copy i)) (frontier s)) ∧
  (∀ i : Fin n, s.writer.j = i.val → (s.writer.pc = 11 ∨ s.writer.pc = 12) →
    (s.memory (.copy i)).origin = some s.writer.index)

theorem memory_order_initial (v : α) (privateData : Fin n → α) :
    MemoryOrder (initial v privateData) := by
  simp [MemoryOrder, initial, OriginLE, frontier]

theorem memory_order_writer {s t : State α n} (hs : MemoryOrder s)
    (hc : WriterControl s) (hb : WriterRaw s)
    (h : writerStep s = some t) : MemoryOrder t ∧ frontier s ≤ frontier t := by
  unfold writerStep at h
  dsimp only at h
  split at h
  all_goals simp_all only [WriterRaw]
  all_goals repeat' split at hb
  all_goals repeat' split at h
  all_goals simp [endWrite, hb] at h
  all_goals subst t
  all_goals simp_all [MemoryOrder, OriginLE, frontier, WriterControl, beginWrite, emit,
    Function.update_apply, Fin.ext_iff]
  all_goals grind

theorem memory_order_reader {s t : State α n} (hs : MemoryOrder s)
    (j : Fin n) (corrupt : α) (h : readerStep s j corrupt = some t) :
    MemoryOrder t ∧ frontier s = frontier t := by
  cases hr : s.rawReads j <;>
    cases hc : (s.readers j).chosen <;>
    unfold readerStep at h <;>
    dsimp only at h <;>
    split at h
  all_goals repeat' split at h
  all_goals simp [endRead, hr, hc] at h
  all_goals subst t
  all_goals exact ⟨hs, rfl⟩


def firstIndex (s : State α n) : Nat :=
  if s.writer.pc = 0 ∨ 4 ≤ s.writer.pc then s.writer.index else s.writer.index - 1

def OptionLE (o : Option (Sample α n)) (k : Nat) : Prop :=
  ∀ x, o = some x → OriginLE x.datum k

def SampleUpper (s : State α n) : Prop := ∀ i : Fin n,
  OptionLE (s.readers i).first (firstIndex s) ∧
  (8 ≤ (s.readers i).pc → (s.readers i).flag2 = false →
    OptionLE (s.readers i).first (frontier s)) ∧
  OptionLE (s.readers i).second (frontier s) ∧
  OptionLE (s.readers i).chosen (frontier s)

theorem sample_upper_initial (v : α) (privateData : Fin n → α) :
    SampleUpper (initial v privateData) := by
  simp [SampleUpper, OptionLE, initial]

theorem sample_upper_writer {s t : State α n} (hs : SampleUpper s)
    (hm : MemoryOrder s) (hc : WriterControl s) (hb : WriterRaw s)
    (h : writerStep s = some t) : SampleUpper t := by
  unfold writerStep at h
  dsimp only at h
  split at h
  all_goals simp_all only [WriterRaw]
  all_goals repeat' split at hb
  all_goals repeat' split at h
  all_goals simp [endWrite, hb] at h
  all_goals subst t
  all_goals intro i
  all_goals have hi := hs i
  all_goals clear hs
  all_goals simp_all [OptionLE, OriginLE, firstIndex, frontier,
    MemoryOrder, WriterControl, beginWrite, emit]
  all_goals grind

theorem sample_upper_reader {s t : State α n} (hs : SampleUpper s)
    (hm : MemoryOrder s) (hw : WriterControl s) (hb : ReaderRaw s)
    (j : Fin n) (corrupt : α) (h : readerStep s j corrupt = some t) : SampleUpper t := by
  unfold readerStep at h
  dsimp only at h
  split at h
  all_goals repeat' split at h
  all_goals simp [endRead, Option.bind_eq_some_iff] at h
  all_goals try obtain ⟨raw, hr, h⟩ := h
  all_goals try subst t
  all_goals intro i
  all_goals have hi := hs i
  all_goals have hj := hb j
  all_goals clear hs hb
  all_goals by_cases hij : i = j
  all_goals try subst i
  all_goals simp_all [OptionLE, OriginLE, firstIndex, frontier,
    MemoryOrder, WriterControl, putReader, beginRead, emit]
  all_goals grind


def OptionGE (o : Option (Sample α n)) (k : Nat) : Prop :=
  ∀ x, o = some x → OriginGE x.datum k

/-- Auxiliary invocation snapshots, not fields of the algorithm state. -/
def SampleLower (s : State α n) (floor : Fin n → Nat) : Prop := ∀ i : Fin n,
  floor i ≤ frontier s ∧
  ((s.readers i).pc = 2 → (s.readers i).bit ≠ s.writing i →
    OriginGE (s.memory (.copy i)) (floor i)) ∧
  (3 ≤ (s.readers i).pc → (s.readers i).pc ≤ 16 → s.reading i = s.writing i →
    OriginGE (s.memory (.copy i)) (floor i)) ∧
  (4 ≤ (s.readers i).pc → (s.readers i).flag1 = true → floor i < s.writer.index) ∧
  (8 ≤ (s.readers i).pc → (s.readers i).flag2 = true → floor i < s.writer.index) ∧
  (5 ≤ (s.readers i).pc → (s.readers i).pc ≤ 8 →
    s.switch ≠ (s.readers i).switch1 → floor i < s.writer.index) ∧
  (9 ≤ (s.readers i).pc → (s.readers i).switch1 ≠ (s.readers i).switch2 →
    floor i < s.writer.index) ∧
  OptionGE (s.readers i).first (floor i) ∧
  (11 ≤ (s.readers i).pc → BadFirst (s.readers i) = true →
    OptionGE (s.readers i).second (floor i)) ∧
  OptionGE (s.readers i).chosen (floor i)

theorem sample_lower_initial (v : α) (privateData : Fin n → α) :
    SampleLower (initial v privateData) (fun _ => 0) := by
  simp [SampleLower, OptionGE, OriginGE, frontier, initial]

theorem sample_lower_writer {s t : State α n} {floor : Fin n → Nat}
    (hs : SampleLower s floor) (hm : MemoryOrder s)
    (hc : ControlSafe s) (hb : WriterRaw s)
    (h : writerStep s = some t) : SampleLower t floor := by
  unfold writerStep at h
  dsimp only at h
  split at h
  all_goals simp_all only [WriterRaw]
  all_goals repeat' split at hb
  all_goals repeat' split at h
  all_goals simp [endWrite, hb] at h
  all_goals subst t
  all_goals intro i
  all_goals have hi := hs i
  all_goals have hci := hc.1 i
  all_goals have hw := hc.2.1
  all_goals clear hs hc
  all_goals by_cases hji : s.writer.j = i.val
  all_goals simp_all [OptionGE, OriginGE, frontier,
    MemoryOrder, WriterControl, beginWrite, emit, Function.update_apply, Fin.ext_iff]
  all_goals grind

theorem sample_lower_reader {s t : State α n} {floor : Fin n → Nat}
    (hs : SampleLower s floor) (hm : MemoryOrder s)
    (hw : WriterControl s) (hb : ReaderRaw s) (hsafe : SampleSafety s)
    (j : Fin n) (corrupt : α) (h : readerStep s j corrupt = some t) :
    SampleLower t floor := by
  unfold readerStep at h
  dsimp only at h
  split at h
  all_goals repeat' split at h
  all_goals simp [endRead, Option.bind_eq_some_iff] at h
  all_goals try obtain ⟨raw, hr, h⟩ := h
  all_goals try subst t
  all_goals intro i
  all_goals have hi := hs i
  all_goals have hj := hb j
  all_goals have hsi := hsafe i
  all_goals clear hs hb hsafe
  all_goals by_cases hij : i = j
  all_goals try subst i
  all_goals simp_all [OptionGE, OriginGE, frontier, BadFirst,
    MemoryOrder, WriterControl, putReader, beginRead, emit]
  all_goals grind


def nextFloor (s : State α n) (a : Action α n) (floor : Fin n → Nat) : Fin n → Nat :=
  match a with
  | .invokeRead i => Function.update floor i (frontier s)
  | _ => floor

def Bounds (s : State α n) (floor : Fin n → Nat) : Prop :=
  MemoryOrder s ∧ SampleUpper s ∧ SampleLower s floor

theorem bounds_initial (v : α) (privateData : Fin n → α) :
    Bounds (initial v privateData) (fun _ => 0) :=
  ⟨memory_order_initial v privateData, sample_upper_initial v privateData,
    sample_lower_initial v privateData⟩

theorem bounds_step {s t : State α n} {floor : Fin n → Nat}
    (hs : Bounds s floor) (hc : IntegrityInvariant s)
    (a : Action α n) (h : step s a = some t) : Bounds t (nextFloor s a floor) := by
  obtain ⟨hm, hu, hl⟩ := hs
  cases a with
  | invokeWrite v =>
    simp only [step] at h
    split at h <;> simp [emit] at h
    subst t
    refine ⟨?_, ?_, ?_⟩
    · simp_all [MemoryOrder, frontier, OriginLE]
      grind
    · intro i
      have hi := hu i
      simp_all [OptionLE, OriginLE, firstIndex, frontier]
    · intro i
      have hi := hl i
      simp_all [OptionGE, OriginGE, frontier, nextFloor]
      grind
  | invokeRead j =>
    simp only [step] at h
    split at h <;> simp [emit, putReader] at h
    subst t
    refine ⟨hm, ?_, ?_⟩
    · intro i
      have hi := hu i
      by_cases hij : i = j
      all_goals try subst i
      all_goals simp_all [OptionLE, OriginLE, firstIndex, frontier]
    · intro i
      have hi := hl i
      by_cases hij : i = j
      all_goals try subst i
      all_goals simp_all [OptionGE, OriginGE, frontier, nextFloor]
  | writer =>
    cases ht : writerStep s with
    | none => simp [step, ht] at h
    | some u =>
      have hm' := (memory_order_writer hm hc.1.2.1 hc.2.1.1 ht).1
      have hu' := sample_upper_writer hu hm hc.1.2.1 hc.2.1.1 ht
      have hl' := sample_lower_writer hl hm hc.1 hc.2.1.1 ht
      simp [step, ht] at h
      subst t
      exact ⟨hm', hu', hl'⟩
  | reader j corrupt =>
    cases ht : readerStep s j corrupt with
    | none => simp [step, ht] at h
    | some u =>
      have hm' := (memory_order_reader hm j corrupt ht).1
      have hu' := sample_upper_reader hu hm hc.1.2.1 hc.2.1.2.1 j corrupt ht
      have hl' := sample_lower_reader hl hm hc.1.2.1 hc.2.1.2.1 hc.2.2.1 j corrupt ht
      simp [step, ht] at h
      subst t
      exact ⟨hm', hu', hl'⟩

end ConcurrentReading
