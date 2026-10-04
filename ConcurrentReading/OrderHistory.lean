import ConcurrentReading.OrderBounds

namespace ConcurrentReading

set_option maxHeartbeats 4000000

/-- Bounds from every response preceding a reader invocation. -/
def Past (s : State α n) (call k : Nat) : Prop :=
  (∀ j tj, (tj, Event.writeReturn j) ∈ s.history → tj < call → j ≤ k) ∧
  (∀ tr i c sample j, (tr, Event.readReturn i c sample) ∈ s.history →
    sample.datum.origin = some j → tr < call → j ≤ k)

def ClockFacts (s : State α n) : Prop :=
  (∀ t e, (t, e) ∈ s.history → t < s.clock) ∧
  (∀ i, (s.readers i).call < s.clock) ∧
  (∀ t i c sample, (t, Event.readReturn i c sample) ∈ s.history → c < t)

def HistoryUpper (s : State α n) : Prop :=
  (∀ t k, (t, Event.writeReturn k) ∈ s.history → k ≤ frontier s) ∧
  (∀ t i c sample, (t, Event.readReturn i c sample) ∈ s.history →
    OriginLE sample.datum (frontier s))

def HistoryOrdered (s : State α n) : Prop :=
  ∀ t i c sample k, (t, Event.readReturn i c sample) ∈ s.history →
    sample.datum.origin = some k → Past s c k

def OrderHistory (s : State α n) (floor : Fin n → Nat) : Prop :=
  ClockFacts s ∧ HistoryUpper s ∧
  (∀ i, Past s (s.readers i).call (floor i)) ∧ HistoryOrdered s

theorem order_history_initial (v : α) (privateData : Fin n → α) :
    OrderHistory (initial v privateData) (fun _ => 0) := by
  simp [OrderHistory, ClockFacts, HistoryUpper, HistoryOrdered, Past,
    OriginLE, frontier, initial]
  grind

theorem order_history_writer {s t : State α n} {floor : Fin n → Nat}
    (hs : OrderHistory s floor) (hm : MemoryOrder s)
    (hw : WriterControl s) (hb : WriterRaw s)
    (h : writerStep s = some t) : OrderHistory {t with clock := s.clock + 1} floor := by
  have hmono := (memory_order_writer hm hw hb h).2
  unfold writerStep at h
  dsimp only at h
  split at h
  all_goals simp_all only [WriterRaw]
  all_goals repeat' split at hb
  all_goals repeat' split at h
  all_goals simp [endWrite, hb] at h
  all_goals subst t
  all_goals simp_all [OrderHistory, ClockFacts, HistoryUpper, HistoryOrdered,
    Past, OriginLE, frontier, beginWrite, emit, List.mem_append]
  all_goals grind

theorem order_history_reader {s t : State α n} {floor : Fin n → Nat}
    (hs : OrderHistory s floor) (hu : SampleUpper s) (hl : SampleLower s floor)
    (j : Fin n) (corrupt : α) (h : readerStep s j corrupt = some t) :
    OrderHistory {t with clock := s.clock + 1} floor := by
  have hui := (hu j).2.2.2
  have hli := (hl j).2.2.2.2.2.2.2.2.2
  clear hu hl
  unfold readerStep at h
  dsimp only at h
  split at h
  all_goals repeat' split at h
  all_goals simp [endRead, Option.bind_eq_some_iff] at h
  all_goals try obtain ⟨raw, hr, h⟩ := h
  all_goals try subst t
  all_goals simp_all [OrderHistory, ClockFacts, HistoryUpper, HistoryOrdered,
    Past, OriginLE, OptionLE, OriginGE, OptionGE, frontier,
    putReader, beginRead, emit, List.mem_append, Function.update_apply]
  all_goals grind


theorem order_history_step {s t : State α n} {floor : Fin n → Nat}
    (hs : OrderHistory s floor) (hb : Bounds s floor) (hc : IntegrityInvariant s)
    (a : Action α n) (h : step s a = some t) :
    OrderHistory t (nextFloor s a floor) := by
  cases a with
  | invokeWrite v =>
    simp only [step] at h
    split at h <;> simp [emit] at h
    subst t
    simp_all [OrderHistory, ClockFacts, HistoryUpper, HistoryOrdered, Past,
      OriginLE, frontier, nextFloor, List.mem_append]
    grind
  | invokeRead j =>
    simp only [step] at h
    split at h <;> simp [emit, putReader] at h
    subst t
    simp_all [OrderHistory, ClockFacts, HistoryUpper, HistoryOrdered, Past,
      OriginLE, frontier, nextFloor, List.mem_append, Function.update_apply]
    grind
  | writer =>
    cases ht : writerStep s with
    | none => simp [step, ht] at h
    | some u =>
      have hu := order_history_writer hs hb.1 hc.1.2.1 hc.2.1.1 ht
      simp [step, ht] at h
      subst t
      exact hu
  | reader j corrupt =>
    cases ht : readerStep s j corrupt with
    | none => simp [step, ht] at h
    | some u =>
      have hu := order_history_reader hs hb.2.1 hb.2.2 j corrupt ht
      simp [step, ht] at h
      subst t
      exact hu

def OrderingInvariant (s : State α n) : Prop :=
  IntegrityInvariant s ∧ ∃ floor, Bounds s floor ∧ OrderHistory s floor

theorem ordering_invariant_initial (v : α) (privateData : Fin n → α) :
    OrderingInvariant (initial v privateData) :=
  ⟨integrity_invariant_initial v privateData, fun _ => 0,
    bounds_initial v privateData, order_history_initial v privateData⟩

theorem ordering_invariant_step {s t : State α n} (hs : OrderingInvariant s)
    (a : Action α n) (h : step s a = some t) : OrderingInvariant t := by
  obtain ⟨hc, floor, hb, hh⟩ := hs
  exact ⟨integrity_invariant_step hc a h, nextFloor s a floor,
    bounds_step hb hc a h, order_history_step hh hb hc a h⟩

theorem ordering_invariant_run {s t : State α n} {as : List (Action α n)}
    (hs : OrderingInvariant s) (h : run s as = some t) : OrderingInvariant t := by
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
      exact ih (ordering_invariant_step hs a ht) h

theorem ordering_invariant_reachable {v : α} {privateData : Fin n → α} {s : State α n}
    (h : Reachable v privateData s) : OrderingInvariant s := by
  obtain ⟨as, h⟩ := h
  exact ordering_invariant_run (ordering_invariant_initial v privateData) h

/-- The unchanged general source-order target, across every reader identity. -/
theorem source_order : SourceOrder := by
  intro α n hn v privateData s hr t i c sample hreturn
  obtain ⟨_, k, ti, ho, hsource, htime⟩ := integrity α n hn v privateData s hr t i c sample hreturn
  obtain ⟨_, floor, _, hh⟩ := ordering_invariant_reachable hr
  have hord := hh.2.2.2
  have hp := hord t i c sample k hreturn ho
  refine ⟨k, ho, hp.1, ⟨ti, sample.datum.value, hsource, htime⟩, ?_⟩
  intro t' i' c' sample' hreturn' hbefore
  obtain ⟨_, k', _, ho', _, _⟩ := integrity α n hn v privateData s hr t' i' c' sample' hreturn'
  exact ⟨k', ho', (hord t' i' c' sample' k' hreturn' ho').2 t i c sample k hreturn ho hbefore⟩

end ConcurrentReading
