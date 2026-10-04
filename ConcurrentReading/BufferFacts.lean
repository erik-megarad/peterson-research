import ConcurrentReading.Handshake

namespace ConcurrentReading

set_option maxHeartbeats 2000000

/-- Exact raw-write location and source datum, derived from writer control steps. -/
def WriterRaw (s : State α n) : Prop :=
  s.rawWrite = match s.writer.pc with
  | 3 => some ⟨.first, ⟨s.writer.value, some s.writer.index⟩⟩
  | 10 => if h : s.writer.j < n then
      some ⟨.copy ⟨s.writer.j, h⟩, ⟨s.writer.value, some s.writer.index⟩⟩
    else none
  | 14 => some ⟨.second, ⟨s.writer.value, some s.writer.index⟩⟩
  | _ => none

/-- An active raw read belongs to the buffer selected at its reader control location. -/
def ReaderRaw (s : State α n) : Prop := ∀ i r, s.rawReads i = some r →
  ((s.readers i).pc = 6 ∧ r.buffer = .first) ∨
  ((s.readers i).pc = 10 ∧ r.buffer = .second) ∨
  ((s.readers i).pc = 14 ∧ r.buffer = .copy i)

def Initialized (s : State α n) (b : Buffer n) : Prop := (s.memory b).origin ≠ none

/-- Origin presence is tracked separately from the indexed history proof. The
private-buffer clauses cover a stale signal and an acknowledged active reader. -/
def BufferInit (s : State α n) : Prop :=
  Initialized s .first ∧ Initialized s .second ∧
  (∀ i : Fin n, s.writer.j = i.val →
    (s.writer.pc = 11 ∨ s.writer.pc = 12) → Initialized s (.copy i)) ∧
  (∀ i : Fin n,
    ((s.readers i).pc = 2 → (s.readers i).bit ≠ s.writing i → Initialized s (.copy i)) ∧
    (3 ≤ (s.readers i).pc → (s.readers i).pc ≤ 16 →
      s.reading i = s.writing i → Initialized s (.copy i)))

def BufferFacts (s : State α n) : Prop := WriterRaw s ∧ ReaderRaw s ∧ BufferInit s

theorem buffer_facts_initial (v : α) (privateData : Fin n → α) :
    BufferFacts (initial v privateData) := by
  simp [BufferFacts, WriterRaw, ReaderRaw, BufferInit, Initialized, initial]

theorem buffer_facts_writer {s t : State α n} (hs : BufferFacts s)
    (hh : Handshake s) (h : writerStep s = some t) : BufferFacts t := by
  have hwr := hs.1
  unfold writerStep at h
  dsimp only at h
  split at h
  all_goals simp_all only [WriterRaw]
  all_goals repeat' split at hwr
  all_goals repeat' split at h
  all_goals simp [endWrite, hwr] at h
  all_goals subst t
  all_goals simp_all [BufferFacts, WriterRaw, ReaderRaw, BufferInit, Initialized,
    Handshake, beginWrite, emit, Function.update_apply, Fin.ext_iff]
  all_goals grind

theorem buffer_facts_reader {s t : State α n} (hs : BufferFacts s)
    (j : Fin n) (corrupt : α) (h : readerStep s j corrupt = some t) : BufferFacts t := by
  cases hr : s.rawReads j <;>
    cases hc : (s.readers j).chosen <;>
    unfold readerStep at h <;>
    dsimp only at h <;>
    split at h
  all_goals repeat' split at h
  all_goals simp [endRead, hr, hc] at h
  all_goals subst t
  all_goals simp_all [BufferFacts, WriterRaw, ReaderRaw, BufferInit, Initialized,
    putReader, beginRead, emit, Function.update_apply]
  all_goals grind

theorem buffer_facts_step {s t : State α n} (hs : BufferFacts s) (hh : Handshake s)
    (a : Action α n) (h : step s a = some t) : BufferFacts t := by
  cases a with
  | invokeWrite v =>
    simp only [step] at h
    split at h <;> simp [emit] at h
    subst t
    simp_all [BufferFacts, WriterRaw, ReaderRaw, BufferInit, Initialized]
  | invokeRead j =>
    simp only [step] at h
    split at h <;> simp [emit, putReader] at h
    subst t
    simp_all [BufferFacts, WriterRaw, ReaderRaw, BufferInit, Initialized, Function.update_apply]
    grind
  | writer =>
    cases ht : writerStep s with
    | none => simp [step, ht] at h
    | some u =>
      have hu := buffer_facts_writer hs hh ht
      simp [step, ht] at h
      subst t
      exact hu
  | reader j corrupt =>
    cases ht : readerStep s j corrupt with
    | none => simp [step, ht] at h
    | some u =>
      have hu := buffer_facts_reader hs j corrupt ht
      simp [step, ht] at h
      subst t
      exact hu

theorem buffer_facts_run {s t : State α n} {as : List (Action α n)}
    (hh : Handshake s) (hs : BufferFacts s) (h : run s as = some t) : BufferFacts t := by
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
      exact ih (handshake_step hh a ht) (buffer_facts_step hs hh a ht) h

theorem buffer_facts_reachable {v : α} {privateData : Fin n → α} {s : State α n}
    (h : Reachable v privateData s) : BufferFacts s := by
  obtain ⟨as, h⟩ := h
  exact buffer_facts_run (handshake_initial v privateData) (buffer_facts_initial v privateData) h

end ConcurrentReading
