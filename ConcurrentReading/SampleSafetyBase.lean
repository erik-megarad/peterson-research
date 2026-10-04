import ConcurrentReading.Control
import ConcurrentReading.BufferFacts

namespace ConcurrentReading

set_option maxHeartbeats 4000000

def BadFirst (r : Reader α n) : Bool :=
  (r.switch1 != r.switch2) || r.flag1 || r.flag2

def GoodSample (v : Sample α n) : Prop := v.torn = false ∧ v.datum.origin ≠ none

def GoodOption (v : Option (Sample α n)) : Prop := ∀ x, v = some x → GoodSample x

def Selected (r : Reader α n) : Option (Sample α n) :=
  if BadFirst r then r.second else r.first

def FirstHazard (s : State α n) (i : Fin n) : Prop :=
  (3 ≤ s.writer.pc ∧ s.writer.pc ≤ 5 ∧ s.switch = (s.readers i).switch1) ∨
  (AfterToggle s i ∧ s.switch ≠ (s.readers i).switch1)

/-- Samples remain potentially corrupt until the selecting branch justifies them.
The clauses carry, in order: the final test and copy protection; initialized
untorn public samples; a torn first read through both control samples; second-
buffer protection; private-copy protection; and the final selected/chosen sample.
This is proved from transitions, not added to the accepted model. -/
def SampleSafety (s : State α n) : Prop := ∀ i : Fin n,
  ((s.readers i).pc = 12 → (s.readers i).test = s.reading i) ∧
  ((s.readers i).pc = 13 ∨ (s.readers i).pc = 14 → s.reading i = s.writing i) ∧
  (∀ x, (s.readers i).first = some x → x.torn = false → x.datum.origin ≠ none) ∧
  (∀ x, (s.readers i).second = some x → x.torn = false → x.datum.origin ≠ none) ∧
  ((s.readers i).pc = 6 → ∀ raw, s.rawReads i = some raw → raw.torn = true →
    (s.readers i).flag1 = false → s.reading i ≠ s.writing i → FirstHazard s i) ∧
  ((s.readers i).pc = 7 → ∀ x, (s.readers i).first = some x → x.torn = true →
    (s.readers i).flag1 = false → s.reading i ≠ s.writing i → FirstHazard s i) ∧
  ((s.readers i).pc = 8 → ∀ x, (s.readers i).first = some x → x.torn = true →
    (s.readers i).flag1 = false → (s.readers i).flag2 = false →
    s.reading i ≠ s.writing i → AfterToggle s i ∧ s.switch ≠ (s.readers i).switch1) ∧
  (9 ≤ (s.readers i).pc → (s.readers i).pc ≤ 12 → s.reading i ≠ s.writing i →
    BadFirst (s.readers i) = false → ∀ x, (s.readers i).first = some x → x.torn = false) ∧
  ((s.readers i).pc = 10 → s.reading i ≠ s.writing i → BadFirst (s.readers i) = true →
    ∀ raw, s.rawReads i = some raw → raw.torn = false) ∧
  (11 ≤ (s.readers i).pc → (s.readers i).pc ≤ 12 → s.reading i ≠ s.writing i →
    BadFirst (s.readers i) = true → ∀ x, (s.readers i).second = some x → x.torn = false) ∧
  ((s.readers i).pc = 14 → ∀ raw, s.rawReads i = some raw → raw.torn = false) ∧
  ((s.readers i).pc = 15 → GoodOption (Selected (s.readers i))) ∧
  ((s.readers i).pc = 16 → GoodOption (s.readers i).chosen)

theorem sample_safety_initial (v : α) (privateData : Fin n → α) :
    SampleSafety (initial v privateData) := by
  simp [SampleSafety, initial]

theorem sample_safety_writer {s t : State α n} (hs : SampleSafety s)
    (hc : ControlSafe s) (hb : BufferFacts s)
    (h : writerStep s = some t) : SampleSafety t := by
  have hwr := hb.1
  unfold writerStep at h
  dsimp only at h
  split at h
  all_goals simp_all only [WriterRaw]
  all_goals repeat' split at hwr
  all_goals repeat' split at h
  all_goals simp [endWrite, hwr] at h
  all_goals subst t
  all_goals intro i
  all_goals have hi := hs i
  all_goals have hci := hc.1 i
  all_goals have hdi := hc.2.2 i
  all_goals have hw := hc.2.1
  all_goals have hri := hb.2.1 i
  all_goals clear hs hc hb
  all_goals by_cases hji : s.writer.j = i.val
  all_goals simp_all [WriterControl, FirstHazard, BeforeSecond, AfterToggle,
    ScanBefore, GoodOption, GoodSample, Selected, BadFirst, beginWrite, emit,
    Function.update_apply, Fin.ext_iff]
  all_goals grind

theorem writer_raw_shape {s : State α n} (hs : WriterRaw s)
    (w : RawWrite α n) (h : s.rawWrite = some w) :
    (s.writer.pc = 3 ∧ w.buffer = .first) ∨
    (s.writer.pc = 10 ∧ ∃ i : Fin n, s.writer.j = i.val ∧ w.buffer = .copy i) ∨
    (s.writer.pc = 14 ∧ w.buffer = .second) := by
  unfold WriterRaw at hs
  split at hs
  all_goals repeat' split at hs
  all_goals simp_all
  all_goals grind

end ConcurrentReading
