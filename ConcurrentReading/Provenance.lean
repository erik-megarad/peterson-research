import ConcurrentReading.Handshake

namespace ConcurrentReading

set_option maxHeartbeats 4000000

/-- This follows the stored source index and its associated payload together. -/
def DatumProvenance (s : State α n) (d : Datum α) : Prop := ∀ k,
  d.origin = some k → ∃ ti,
    (ti, Event.writeInvoke k d.value) ∈ s.history ∧ ti < s.clock

def OptionProvenance (s : State α n) (o : Option (Sample α n)) : Prop :=
  ∀ x, o = some x → DatumProvenance s x.datum

def HistoryProvenance (s : State α n) : Prop := ∀ t i call sample k,
  (t, Event.readReturn i call sample) ∈ s.history → sample.datum.origin = some k →
  ∃ ti, (ti, Event.writeInvoke k sample.datum.value) ∈ s.history ∧ ti < t

def Provenance (s : State α n) : Prop :=
  DatumProvenance s ⟨s.writer.value, some s.writer.index⟩ ∧
  (∀ b, DatumProvenance s (s.memory b)) ∧
  (∀ w, s.rawWrite = some w → DatumProvenance s w.datum) ∧
  (∀ i, OptionProvenance s (s.readers i).first ∧
    OptionProvenance s (s.readers i).second ∧ OptionProvenance s (s.readers i).chosen) ∧
  HistoryProvenance s

theorem provenance_initial (v : α) (privateData : Fin n → α) :
    Provenance (initial v privateData) := by
  simp [Provenance, DatumProvenance, OptionProvenance, HistoryProvenance, initial]
  intro b
  cases b <;> simp

theorem provenance_writer {s t : State α n} (hs : Provenance s)
    (h : writerStep s = some t) : Provenance t ∧ t.clock = s.clock := by
  cases hr : s.rawWrite <;>
    unfold writerStep at h <;>
    dsimp only at h <;>
    split at h
  all_goals repeat' split at h
  all_goals simp [endWrite, hr] at h
  all_goals subst t
  all_goals simp_all [Provenance, DatumProvenance, OptionProvenance, HistoryProvenance,
    beginWrite, emit, List.mem_append, Function.update_apply]
  all_goals grind

theorem provenance_reader {s t : State α n} (hs : Provenance s)
    (j : Fin n) (corrupt : α) (h : readerStep s j corrupt = some t) :
    Provenance t ∧ t.clock = s.clock := by
  cases hr : s.rawReads j <;>
    cases hc : (s.readers j).chosen <;>
    unfold readerStep at h <;>
    dsimp only at h <;>
    split at h
  all_goals repeat' split at h
  all_goals simp [endRead, hr, hc] at h
  all_goals subst t
  all_goals simp_all [Provenance, DatumProvenance, OptionProvenance, HistoryProvenance,
    putReader, beginRead, emit, List.mem_append, Function.update_apply]
  all_goals grind

theorem provenance_tick {s : State α n} (hs : Provenance s) :
    Provenance { s with clock := s.clock + 1 } := by
  simp_all [Provenance, DatumProvenance, OptionProvenance, HistoryProvenance]
  grind

theorem provenance_step {s t : State α n} (hs : Provenance s)
    (a : Action α n) (h : step s a = some t) : Provenance t := by
  cases a with
  | invokeWrite v =>
    simp only [step] at h
    split at h <;> simp [emit] at h
    subst t
    simp_all [Provenance, DatumProvenance, OptionProvenance, HistoryProvenance,
      List.mem_append]
    grind
  | invokeRead j =>
    simp only [step] at h
    split at h <;> simp [emit, putReader] at h
    subst t
    simp_all [Provenance, DatumProvenance, OptionProvenance, HistoryProvenance,
      List.mem_append, Function.update_apply]
    grind
  | writer =>
    cases ht : writerStep s with
    | none => simp [step, ht] at h
    | some u =>
      obtain ⟨hu, hclock⟩ := provenance_writer hs ht
      simp [step, ht] at h
      subst t
      simpa [hclock] using provenance_tick hu
  | reader j corrupt =>
    cases ht : readerStep s j corrupt with
    | none => simp [step, ht] at h
    | some u =>
      obtain ⟨hu, hclock⟩ := provenance_reader hs j corrupt ht
      simp [step, ht] at h
      subst t
      simpa [hclock] using provenance_tick hu

theorem provenance_run {s t : State α n} {as : List (Action α n)}
    (hs : Provenance s) (h : run s as = some t) : Provenance t := by
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
      exact ih (provenance_step hs a ht) h

theorem provenance_reachable {v : α} {privateData : Fin n → α} {s : State α n}
    (h : Reachable v privateData s) : Provenance s := by
  obtain ⟨as, h⟩ := h
  exact provenance_run (provenance_initial v privateData) h

end ConcurrentReading
