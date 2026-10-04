import ConcurrentReading.OrderHistory

namespace ConcurrentReading

set_option maxHeartbeats 4000000

/-- Writer operations are serial and their indices enumerate their invocations. -/
def WriteShape (s : State α n) : Prop :=
  (∀ k, (∃ ti v, (ti, Event.writeInvoke k v) ∈ s.history) ↔ k ≤ s.writer.index) ∧
  (∀ ti v, (ti, Event.writeInvoke s.writer.index v) ∈ s.history → v = s.writer.value) ∧
  (∀ k ti v ti' v', (ti, Event.writeInvoke k v) ∈ s.history →
    (ti', Event.writeInvoke k v') ∈ s.history → ti = ti' ∧ v = v') ∧
  (∀ j tj v k tk w, (tj, Event.writeInvoke j v) ∈ s.history →
    (tk, Event.writeInvoke k w) ∈ s.history → (j < k ↔ tj < tk)) ∧
  (∀ k, (∃ tr, (tr, Event.writeReturn k) ∈ s.history) ↔
    k < s.writer.index ∨ (k = s.writer.index ∧ s.writer.pc = 0)) ∧
  (∀ k ti v j tr, (ti, Event.writeInvoke k v) ∈ s.history →
    (tr, Event.writeReturn j) ∈ s.history → (k ≤ j ↔ ti < tr))

/-- Reader calls are their invocation timestamps and have at most one response. -/
def ReadShape (s : State α n) : Prop :=
  (∀ t i c, (t, Event.readInvoke i c) ∈ s.history → t = c) ∧
  (∀ t i c sample, (t, Event.readReturn i c sample) ∈ s.history →
    (c, Event.readInvoke i c) ∈ s.history) ∧
  (∀ i, (s.readers i).pc ≠ 0 →
    (s.readers i).call < s.clock ∧
    ((s.readers i).call, Event.readInvoke i (s.readers i).call) ∈ s.history ∧
    ¬ ∃ t sample, (t, Event.readReturn i (s.readers i).call sample) ∈ s.history)

def HistoryShape (s : State α n) : Prop :=
  WriteShape s ∧ ReadShape s ∧
  (s.history.filterMap (fun te => responseId te.2)).Nodup ∧
  s.history.Pairwise (fun a b => a.1 < b.1)

theorem history_shape_initial (v : α) (privateData : Fin n → α) :
    HistoryShape (initial v privateData) := by
  simp [HistoryShape, WriteShape, ReadShape, initial, responseId]
  grind


theorem write_shape_writer {s t : State α n} (hs : WriteShape s)
    (hclock : ClockFacts s) (h : writerStep s = some t) : WriteShape t := by
  have hinvoke : ∀ ti k v, (ti, Event.writeInvoke k v) ∈ s.history → k ≤ s.writer.index :=
    fun ti k v hm => (hs.1 k).mp ⟨ti, v, hm⟩
  have hreturn : ∀ tr k, (tr, Event.writeReturn k) ∈ s.history →
      k < s.writer.index ∨ (k = s.writer.index ∧ s.writer.pc = 0) :=
    fun tr k hm => (hs.2.2.2.2.1 k).mp ⟨tr, hm⟩
  cases hr : s.rawWrite <;>
    unfold writerStep at h <;>
    dsimp only at h <;>
    split at h
  all_goals repeat' split at h
  all_goals simp [endWrite, hr] at h
  all_goals subst t
  all_goals simp_all [WriteShape, ClockFacts, beginWrite, emit, List.mem_append]
  all_goals grind

theorem write_shape_reader {s t : State α n} (hs : WriteShape s)
    (j : Fin n) (corrupt : α) (h : readerStep s j corrupt = some t) : WriteShape t := by
  unfold readerStep at h
  dsimp only at h
  split at h
  all_goals repeat' split at h
  all_goals simp [endRead, Option.bind_eq_some_iff] at h
  all_goals try obtain ⟨raw, hr, h⟩ := h
  all_goals try subst t
  all_goals simpa [WriteShape, putReader, beginRead, emit, List.mem_append] using hs

theorem write_shape_step {s t : State α n} (hs : WriteShape s)
    (hclock : ClockFacts s) (a : Action α n) (h : step s a = some t) : WriteShape t := by
  have hinvoke : ∀ ti k v, (ti, Event.writeInvoke k v) ∈ s.history → k ≤ s.writer.index :=
    fun ti k v hm => (hs.1 k).mp ⟨ti, v, hm⟩
  have hreturn : ∀ tr k, (tr, Event.writeReturn k) ∈ s.history →
      k < s.writer.index ∨ (k = s.writer.index ∧ s.writer.pc = 0) :=
    fun tr k hm => (hs.2.2.2.2.1 k).mp ⟨tr, hm⟩
  cases a with
  | invokeWrite v =>
    simp only [step] at h
    split at h <;> simp [emit] at h
    subst t
    dsimp only [WriteShape]
    constructor
    · intro k
      constructor
      · rintro ⟨ti, w, hm⟩
        simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq,
          Event.writeInvoke.injEq] at hm
        rcases hm with hm | ⟨_, hk, _⟩
        · exact Nat.le_trans (hinvoke ti k w hm) (Nat.le_succ _)
        · omega
      · intro hk
        by_cases he : k = s.writer.index + 1
        · subst k
          exact ⟨s.clock, v, by simp⟩
        · obtain ⟨ti, w, hm⟩ := (hs.1 k).mpr (by omega)
          exact ⟨ti, w, List.mem_append_left _ hm⟩
    · simp_all [WriteShape, ClockFacts, List.mem_append]
      grind
  | invokeRead j =>
    simp only [step] at h
    split at h <;> simp [emit, putReader] at h
    subst t
    simpa [WriteShape, List.mem_append] using hs
  | writer =>
    cases ht : writerStep s with
    | none => simp [step, ht] at h
    | some u =>
      have hu := write_shape_writer hs hclock ht
      simp [step, ht] at h
      subst t
      exact hu
  | reader j corrupt =>
    cases ht : readerStep s j corrupt with
    | none => simp [step, ht] at h
    | some u =>
      have hu := write_shape_reader hs j corrupt ht
      simp [step, ht] at h
      subst t
      exact hu

theorem read_shape_writer {s t : State α n} (hs : ReadShape s)
    (h : writerStep s = some t) : ReadShape t ∧ t.clock = s.clock := by
  cases hr : s.rawWrite <;>
    unfold writerStep at h <;>
    dsimp only at h <;>
    split at h
  all_goals repeat' split at h
  all_goals simp [endWrite, hr] at h
  all_goals subst t
  all_goals simp_all [ReadShape, beginWrite, emit, List.mem_append]
  all_goals grind

theorem read_shape_reader {s t : State α n} (hs : ReadShape s)
    (j : Fin n) (corrupt : α) (h : readerStep s j corrupt = some t) :
    ReadShape t ∧ t.clock = s.clock := by
  unfold readerStep at h
  dsimp only at h
  split at h
  all_goals repeat' split at h
  all_goals simp [endRead, Option.bind_eq_some_iff] at h
  all_goals try obtain ⟨raw, hr, h⟩ := h
  all_goals try subst t
  all_goals simp_all [ReadShape, putReader, beginRead, emit, List.mem_append,
    Function.update_apply]
  all_goals grind

theorem read_shape_tick {s : State α n} (hs : ReadShape s) :
    ReadShape {s with clock := s.clock + 1} := by
  simp_all [ReadShape]
  grind

theorem read_shape_step {s t : State α n} (hs : ReadShape s)
    (hclock : ClockFacts s) (a : Action α n) (h : step s a = some t) : ReadShape t := by
  cases a with
  | invokeWrite v =>
    simp only [step] at h
    split at h <;> simp [emit] at h
    subst t
    simp_all [ReadShape, List.mem_append]
    grind
  | invokeRead j =>
    simp only [step] at h
    split at h <;> simp [emit, putReader] at h
    subst t
    have hactive := hs.2.2
    simp only [ReadShape, ClockFacts, List.mem_append, List.mem_singleton,
      Prod.mk.injEq, Event.readInvoke.injEq, Function.update_apply] at *
    grind
  | writer =>
    cases ht : writerStep s with
    | none => simp [step, ht] at h
    | some u =>
      obtain ⟨hu, htime⟩ := read_shape_writer hs ht
      simp [step, ht] at h
      subst t
      simpa [htime] using read_shape_tick hu
  | reader j corrupt =>
    cases ht : readerStep s j corrupt with
    | none => simp [step, ht] at h
    | some u =>
      obtain ⟨hu, htime⟩ := read_shape_reader hs j corrupt ht
      simp [step, ht] at h
      subst t
      simpa [htime] using read_shape_tick hu


theorem response_ids_mem (h : List (Nat × Event α n)) (o : OpId n) :
    o ∈ h.filterMap (fun te => responseId te.2) ↔ ∃ t, Responded h o t := by
  induction h with
  | nil => cases o <;> simp [Responded]
  | cons te h ih =>
    obtain ⟨t, e⟩ := te
    cases e <;> cases o <;> simp_all [responseId, Responded]
    all_goals grind

theorem writer_history_effect {s t : State α n} (h : writerStep s = some t) :
    t.history = s.history ∨
    (s.writer.pc = 15 ∧ t.history = s.history ++ [(s.clock, Event.writeReturn s.writer.index)]) := by
  cases hr : s.rawWrite <;>
    unfold writerStep at h <;>
    dsimp only at h <;>
    split at h
  all_goals repeat' split at h
  all_goals simp [endWrite, hr] at h
  all_goals subst t
  all_goals simp_all [beginWrite, emit]

theorem reader_history_effect {s t : State α n} (j : Fin n) (corrupt : α)
    (h : readerStep s j corrupt = some t) :
    t.history = s.history ∨ (s.readers j).pc = 16 ∧ ∃ sample,
      t.history = s.history ++ [(s.clock, Event.readReturn j (s.readers j).call sample)] := by
  unfold readerStep at h
  dsimp only at h
  split at h
  all_goals repeat' split at h
  all_goals simp [endRead, Option.bind_eq_some_iff] at h
  all_goals try obtain ⟨raw, hr, h⟩ := h
  all_goals try subst t
  all_goals simp_all [putReader, beginRead, emit]

theorem history_list_append {s : State α n} {e : Event α n}
    (hn : (s.history.filterMap (fun te => responseId te.2)).Nodup)
    (hp : s.history.Pairwise (fun a b => a.1 < b.1))
    (hc : ClockFacts s)
    (hfresh : ∀ o, responseId e = some o → ¬ ∃ t, Responded s.history o t) :
    ((s.history ++ [(s.clock, e)]).filterMap (fun te => responseId te.2)).Nodup ∧
      (s.history ++ [(s.clock, e)]).Pairwise (fun a b => a.1 < b.1) := by
  constructor
  · cases he : responseId e with
    | none => simpa [he] using hn
    | some o =>
      have ho : o ∉ s.history.filterMap (fun te => responseId te.2) := by
        rw [response_ids_mem]
        exact hfresh o he
      simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, he,
        List.nodup_append, List.nodup_cons, List.not_mem_nil, List.nodup_nil,
        and_true]
      refine ⟨hn, by trivial, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      intro heq
      exact ho (heq ▸ ha)
  · simp only [List.pairwise_append, List.pairwise_singleton, List.mem_singleton]
    exact ⟨hp, trivial, fun a ha b hb => by subst b; exact hc.1 a.1 a.2 ha⟩

theorem history_shape_step {s t : State α n} (hs : HistoryShape s)
    (hc : ClockFacts s) (a : Action α n) (h : step s a = some t) : HistoryShape t := by
  refine ⟨write_shape_step hs.1 hc a h, read_shape_step hs.2.1 hc a h, ?_⟩
  have happ := @history_list_append α n s
  cases a with
  | invokeWrite v =>
    simp only [step] at h
    split at h <;> simp [emit] at h
    subst t
    exact happ hs.2.2.1 hs.2.2.2 hc (by simp [responseId])
  | invokeRead j =>
    simp only [step] at h
    split at h <;> simp [emit, putReader] at h
    subst t
    exact happ hs.2.2.1 hs.2.2.2 hc (by simp [responseId])
  | writer =>
    cases ht : writerStep s with
    | none => simp [step, ht] at h
    | some u =>
      have hu := writer_history_effect ht
      simp [step, ht] at h
      subst t
      rcases hu with hu | ⟨hpc, hu⟩
      · simpa only [hu] using hs.2.2
      · rw [hu]
        apply happ hs.2.2.1 hs.2.2.2 hc
        intro o ho
        simp only [responseId, Option.some.injEq] at ho
        subst o
        intro hret
        have hh := (hs.1.2.2.2.2.1 s.writer.index).mp hret
        omega
  | reader j corrupt =>
    cases ht : readerStep s j corrupt with
    | none => simp [step, ht] at h
    | some u =>
      have hu := reader_history_effect j corrupt ht
      simp [step, ht] at h
      subst t
      rcases hu with hu | ⟨hpc, sample, hu⟩
      · simpa only [hu] using hs.2.2
      · rw [hu]
        apply happ hs.2.2.1 hs.2.2.2 hc
        intro o ho
        simp only [responseId, Option.some.injEq] at ho
        subst o
        exact (hs.2.1.2.2 j (by omega)).2.2

theorem history_shape_run {s t : State α n} {as : List (Action α n)}
    (hs : HistoryShape s) (ho : OrderingInvariant s) (h : run s as = some t) :
    HistoryShape t := by
  induction as generalizing s with
  | nil => simp only [run, Option.some.injEq] at h; subst t; exact hs
  | cons a as ih =>
    cases ht : step s a with
    | none => simp [run, ht] at h
    | some u =>
      simp only [run, ht, Option.bind_some] at h
      obtain ⟨floor, hb, hh⟩ := ho.2
      exact ih (history_shape_step hs hh.1 a ht) (ordering_invariant_step ho a ht) h

theorem history_shape_reachable {v : α} {privateData : Fin n → α} {s : State α n}
    (h : Reachable v privateData s) : HistoryShape s := by
  obtain ⟨as, h⟩ := h
  exact history_shape_run (history_shape_initial v privateData)
    (ordering_invariant_initial v privateData) h

end ConcurrentReading
