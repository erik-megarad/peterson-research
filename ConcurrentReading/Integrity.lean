import ConcurrentReading.SampleSafety
import ConcurrentReading.Provenance

namespace ConcurrentReading

set_option maxHeartbeats 4000000

theorem sample_safety_step {s t : State α n} (hs : SampleSafety s)
    (hc : ControlSafe s) (hb : BufferFacts s)
    (a : Action α n) (h : step s a = some t) : SampleSafety t := by
  cases a with
  | invokeWrite v =>
    simp only [step] at h
    split at h <;> simp [emit] at h
    subst t
    intro i
    have hi := hs i
    clear hs
    simp_all [FirstHazard, AfterToggle, ScanBefore, GoodOption, Selected, BadFirst]
  | invokeRead j =>
    simp only [step] at h
    split at h <;> simp [emit, putReader] at h
    subst t
    intro i
    have hi := hs i
    clear hs
    by_cases hij : i = j
    all_goals try subst i
    all_goals simp_all [FirstHazard, AfterToggle, ScanBefore, GoodOption, Selected, BadFirst]
  | writer =>
    cases ht : writerStep s with
    | none => simp [step, ht] at h
    | some u =>
      have hu := sample_safety_writer hs hc hb ht
      simp [step, ht] at h
      subst t
      exact hu
  | reader j corrupt =>
    cases ht : readerStep s j corrupt with
    | none => simp [step, ht] at h
    | some u =>
      have hu := sample_safety_reader hs hc hb j corrupt ht
      simp [step, ht] at h
      subst t
      exact hu

def HistorySafety (s : State α n) : Prop := ∀ t i call sample,
  (t, Event.readReturn i call sample) ∈ s.history → GoodSample sample

theorem history_safety_initial (v : α) (privateData : Fin n → α) :
    HistorySafety (initial v privateData) := by simp [HistorySafety, initial]

theorem history_safety_writer {s t : State α n} (hs : HistorySafety s)
    (h : writerStep s = some t) : HistorySafety t := by
  cases hr : s.rawWrite <;>
    unfold writerStep at h <;>
    dsimp only at h <;>
    split at h
  all_goals repeat' split at h
  all_goals simp [endWrite, hr] at h
  all_goals subst t
  all_goals simpa [HistorySafety, beginWrite, emit, List.mem_append] using hs

theorem history_safety_reader {s t : State α n} (hs : HistorySafety s)
    (hss : SampleSafety s) (j : Fin n) (corrupt : α)
    (h : readerStep s j corrupt = some t) : HistorySafety t := by
  have hchosen : (s.readers j).pc = 16 → GoodOption (s.readers j).chosen :=
    (hss j).2.2.2.2.2.2.2.2.2.2.2.2
  clear hss
  cases hr : s.rawReads j <;>
    cases hc : (s.readers j).chosen <;>
    unfold readerStep at h <;>
    dsimp only at h <;>
    split at h
  all_goals repeat' split at h
  all_goals simp [endRead, hr, hc] at h
  all_goals subst t
  all_goals simp_all [HistorySafety, putReader, beginRead, emit, List.mem_append, GoodOption]
  all_goals grind

theorem history_safety_step {s t : State α n} (hs : HistorySafety s)
    (hss : SampleSafety s) (a : Action α n) (h : step s a = some t) : HistorySafety t := by
  cases a with
  | invokeWrite v =>
    simp only [step] at h
    split at h <;> simp [emit] at h
    subst t
    simpa [HistorySafety, List.mem_append] using hs
  | invokeRead j =>
    simp only [step] at h
    split at h <;> simp [emit, putReader] at h
    subst t
    simpa [HistorySafety, List.mem_append] using hs
  | writer =>
    cases ht : writerStep s with
    | none => simp [step, ht] at h
    | some u =>
      have hu := history_safety_writer hs ht
      simp [step, ht] at h
      subst t
      exact hu
  | reader j corrupt =>
    cases ht : readerStep s j corrupt with
    | none => simp [step, ht] at h
    | some u =>
      have hu := history_safety_reader hs hss j corrupt ht
      simp [step, ht] at h
      subst t
      exact hu

def IntegrityInvariant (s : State α n) : Prop :=
  ControlSafe s ∧ BufferFacts s ∧ SampleSafety s ∧ HistorySafety s

theorem integrity_invariant_initial (v : α) (privateData : Fin n → α) :
    IntegrityInvariant (initial v privateData) :=
  ⟨control_initial v privateData, buffer_facts_initial v privateData,
    sample_safety_initial v privateData, history_safety_initial v privateData⟩

theorem integrity_invariant_step {s t : State α n} (hs : IntegrityInvariant s)
    (a : Action α n) (h : step s a = some t) : IntegrityInvariant t :=
  ⟨control_step hs.1 a h, buffer_facts_step hs.2.1 hs.1.1 a h,
    sample_safety_step hs.2.2.1 hs.1 hs.2.1 a h,
    history_safety_step hs.2.2.2 hs.2.2.1 a h⟩

theorem integrity_invariant_run {s t : State α n} {as : List (Action α n)}
    (hs : IntegrityInvariant s) (h : run s as = some t) : IntegrityInvariant t := by
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
      exact ih (integrity_invariant_step hs a ht) h

theorem integrity_invariant_reachable {v : α} {privateData : Fin n → α} {s : State α n}
    (h : Reachable v privateData s) : IntegrityInvariant s := by
  obtain ⟨as, h⟩ := h
  exact integrity_invariant_run (integrity_invariant_initial v privateData) h

/-- The unchanged general returned-sample integrity target. -/
theorem integrity : Integrity := by
  intro α n _ v privateData s h t i call sample hm
  have hg := (integrity_invariant_reachable h).2.2.2 t i call sample hm
  have hp := (provenance_reachable h).2.2.2.2
  obtain ⟨htorn, horigin⟩ := hg
  cases ho : sample.datum.origin with
  | none => exact False.elim (horigin ho)
  | some k =>
    obtain ⟨ti, hsource, htime⟩ := hp t i call sample k hm ho
    exact ⟨htorn, k, ti, rfl, hsource, htime⟩

end ConcurrentReading
