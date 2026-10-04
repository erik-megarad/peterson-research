import ConcurrentReading.SampleSafetyBase

namespace ConcurrentReading

set_option maxHeartbeats 4000000

theorem sample_safety_reader {s t : State α n} (hs : SampleSafety s)
    (hc : ControlSafe s) (hb : BufferFacts s) (j : Fin n) (corrupt : α)
    (h : readerStep s j corrupt = some t) : SampleSafety t := by
  have hshape := writer_raw_shape hb.1
  unfold readerStep at h
  dsimp only at h
  split at h
  all_goals repeat' split at h
  all_goals simp [endRead, Option.bind_eq_some_iff] at h
  all_goals try obtain ⟨raw, hr, h⟩ := h
  all_goals try subst t
  all_goals intro i
  all_goals have hi := hs i
  all_goals have hci := hc.1 i
  all_goals have hdi := hc.2.2 i
  all_goals have hw := hc.2.1
  all_goals have hri := hb.2.1 i
  all_goals have hbi := hb.2.2
  all_goals clear hs hc hb
  all_goals by_cases hij : i = j
  all_goals try subst i
  all_goals simp_all [WriterControl, FirstHazard, BeforeSecond, AfterToggle,
    ScanBefore, GoodOption, GoodSample, Selected, BadFirst, BufferInit, Initialized,
    putReader, beginRead, emit, Option.any_eq_true, Option.any_eq_false]
  all_goals grind

end ConcurrentReading
