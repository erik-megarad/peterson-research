import ConcurrentReading.Handshake

namespace ConcurrentReading

set_option maxHeartbeats 2000000

/-- The flag and the saved switch RHS agree with the writer control location. -/
def WriterControl (s : State α n) : Prop :=
  s.writer.pc ≤ 15 ∧
  (s.wflag = true ↔ 2 ≤ s.writer.pc ∧ s.writer.pc ≤ 6) ∧
  (s.writer.pc = 5 → s.writer.bit = s.switch)

/-- The scan has not crossed reader i's test, including the separately sampled
comparison at PC 8. -/
def ScanBefore (s : State α n) (i : Fin n) : Prop :=
  7 ≤ s.writer.pc ∧ s.writer.pc ≤ 12 ∧
  (s.writer.j < i.val ∨ (s.writer.j = i.val ∧
    (s.writer.pc ≠ 8 ∨ s.writer.bit ≠ s.writing i)))

def BeforeSecond (s : State α n) (i : Fin n) : Prop :=
  (2 ≤ s.writer.pc ∧ s.writer.pc ≤ 6) ∨ ScanBefore s i

def AfterToggle (s : State α n) (i : Fin n) : Prop :=
  s.writer.pc = 6 ∨ ScanBefore s i

/-- A detected writer cannot reach buff2 before acknowledging this request. -/
def Detection (s : State α n) : Prop := ∀ i : Fin n,
  (4 ≤ (s.readers i).pc → (s.readers i).pc ≤ 12 →
    (s.readers i).flag1 = true → s.reading i = s.writing i ∨ BeforeSecond s i) ∧
  (8 ≤ (s.readers i).pc → (s.readers i).pc ≤ 12 →
    (s.readers i).flag2 = true → s.reading i = s.writing i ∨ BeforeSecond s i) ∧
  (5 ≤ (s.readers i).pc → (s.readers i).pc ≤ 8 →
    s.switch ≠ (s.readers i).switch1 → s.reading i = s.writing i ∨ AfterToggle s i) ∧
  (9 ≤ (s.readers i).pc → (s.readers i).pc ≤ 12 →
    (s.readers i).switch1 ≠ (s.readers i).switch2 →
    s.reading i = s.writing i ∨ BeforeSecond s i)

theorem writer_control_initial (v : α) (privateData : Fin n → α) :
    WriterControl (initial v privateData) := by simp [WriterControl, initial]

theorem detection_initial (v : α) (privateData : Fin n → α) :
    Detection (initial v privateData) := by simp [Detection, initial]

theorem writer_control_writer {s t : State α n} (hs : WriterControl s)
    (h : writerStep s = some t) : WriterControl t := by
  cases hr : s.rawWrite <;>
    unfold writerStep at h <;>
    dsimp only at h <;>
    split at h
  all_goals repeat' split at h
  all_goals simp [endWrite, hr] at h
  all_goals subst t
  all_goals simp_all [WriterControl, beginWrite, emit]

theorem detection_writer {s t : State α n} (hs : Detection s)
    (hc : Handshake s) (hw : WriterControl s)
    (h : writerStep s = some t) : Detection t := by
  cases hr : s.rawWrite <;>
    unfold writerStep at h <;>
    dsimp only at h <;>
    split at h
  all_goals repeat' split at h
  all_goals simp [endWrite, hr] at h
  all_goals subst t
  all_goals intro i
  all_goals have hi := hs i
  all_goals have hci := hc i
  all_goals clear hs hc
  all_goals by_cases hji : s.writer.j = i.val
  all_goals simp_all [WriterControl, ScanBefore,
    BeforeSecond, AfterToggle, beginWrite, emit, Function.update_apply, Fin.ext_iff]
  all_goals grind

theorem reader_control_frame {s t : State α n} (j : Fin n) (corrupt : α)
    (h : readerStep s j corrupt = some t) :
    t.writer = s.writer ∧ t.wflag = s.wflag ∧ t.switch = s.switch := by
  cases hr : s.rawReads j <;>
    cases hc : (s.readers j).chosen <;>
    unfold readerStep at h <;>
    dsimp only at h <;>
    split at h
  all_goals repeat' split at h
  all_goals simp [endRead, hr, hc] at h
  all_goals subst t
  all_goals simp [putReader, beginRead, emit]

theorem writer_control_reader {s t : State α n} (hs : WriterControl s)
    (j : Fin n) (corrupt : α) (h : readerStep s j corrupt = some t) :
    WriterControl t := by
  obtain ⟨hw, hf, hx⟩ := reader_control_frame j corrupt h
  simpa [WriterControl, hw, hf, hx] using hs

theorem detection_reader {s t : State α n} (hs : Detection s)
    (hw : WriterControl s) (j : Fin n) (corrupt : α)
    (h : readerStep s j corrupt = some t) : Detection t := by
  cases hr : s.rawReads j <;>
    cases hc : (s.readers j).chosen <;>
    unfold readerStep at h <;>
    dsimp only at h <;>
    split at h
  all_goals repeat' split at h
  all_goals simp [endRead, hr, hc] at h
  all_goals subst t
  all_goals intro i
  all_goals have hi := hs i
  all_goals clear hs
  all_goals by_cases hij : i = j
  all_goals try subst i
  all_goals simp_all [WriterControl, ScanBefore,
    BeforeSecond, AfterToggle, putReader, beginRead, emit]
  all_goals grind

def ControlSafe (s : State α n) : Prop := Handshake s ∧ WriterControl s ∧ Detection s

theorem control_initial (v : α) (privateData : Fin n → α) :
    ControlSafe (initial v privateData) :=
  ⟨handshake_initial v privateData, writer_control_initial v privateData,
    detection_initial v privateData⟩

theorem control_step {s t : State α n} (hs : ControlSafe s)
    (a : Action α n) (h : step s a = some t) : ControlSafe t := by
  refine ⟨handshake_step hs.1 a h, ?_⟩
  obtain ⟨hc, hw, hd⟩ := hs
  cases a with
  | invokeWrite v =>
    simp only [step] at h
    split at h <;> simp [emit] at h
    subst t
    constructor
    · simp_all [WriterControl]
    · intro i
      have hi := hd i
      simp_all [Detection, BeforeSecond, AfterToggle, ScanBefore]
  | invokeRead j =>
    simp only [step] at h
    split at h <;> simp [emit, putReader] at h
    subst t
    refine ⟨hw, ?_⟩
    intro i
    have hi := hd i
    clear hd
    by_cases hij : i = j <;> simp_all [BeforeSecond, AfterToggle, ScanBefore]
  | writer =>
    cases ht : writerStep s with
    | none => simp [step, ht] at h
    | some u =>
      have huw := writer_control_writer hw ht
      have hud := detection_writer hd hc hw ht
      simp [step, ht] at h
      subst t
      exact ⟨huw, hud⟩
  | reader j corrupt =>
    cases ht : readerStep s j corrupt with
    | none => simp [step, ht] at h
    | some u =>
      have huw := writer_control_reader hw j corrupt ht
      have hud := detection_reader hd hw j corrupt ht
      simp [step, ht] at h
      subst t
      exact ⟨huw, hud⟩

theorem control_run {s t : State α n} {as : List (Action α n)}
    (hs : ControlSafe s) (h : run s as = some t) : ControlSafe t := by
  induction as generalizing s with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst t
    exact hs
  | cons a as ih =>
    cases ht : step s a with
    | none => simp [run, ht] at h
    | some u =>
      simp only [run, ht, Option.bind_some] at h
      exact ih (control_step hs a ht) h

theorem control_reachable {v : α} {privateData : Fin n → α} {s : State α n}
    (h : Reachable v privateData s) : ControlSafe s := by
  obtain ⟨as, h⟩ := h
  exact control_run (control_initial v privateData) h

end ConcurrentReading
