import ConcurrentReading.HistoryShape

namespace ConcurrentReading

set_option maxHeartbeats 4000000

/-- Read entries keep their original response order within each source-write block. -/
def readsAt (h : List (Nat × Event α n)) (k : Nat) : List (OpId n × Option (Datum α)) :=
  h.filterMap fun (_, e) => match e with
    | .readReturn i c sample =>
      if sample.datum.origin = some k then some (.read i c, some sample.datum) else none
    | _ => none

noncomputable def valueAt (s : State α n) (k : Nat) : α := by
  classical
  exact if h : ∃ v, ∃ ti, (ti, Event.writeInvoke k v) ∈ s.history then Classical.choose h
  else s.writer.value

noncomputable def writeBlock (s : State α n) (k : Nat) : List (OpId n × Option (Datum α)) :=
  (.write k, some ⟨valueAt s k, some k⟩) :: readsAt s.history k

noncomputable def commonOrder (s : State α n) : List (OpId n × Option (Datum α)) :=
  (List.range (s.writer.index + 1)).flatMap (writeBlock s)

def pendingExtension (s : State α n) : List (Nat × Event α n) :=
  if s.writer.pc = 0 then [] else [(s.clock, Event.writeReturn s.writer.index)]

theorem reads_at_mem {h : List (Nat × Event α n)} {k : Nat} {entry} :
    entry ∈ readsAt h k ↔ ∃ t i c sample,
      (t, Event.readReturn i c sample) ∈ h ∧ sample.datum.origin = some k ∧
      entry = (.read i c, some sample.datum) := by
  simp only [readsAt, List.mem_filterMap]
  constructor
  · rintro ⟨⟨t, e⟩, hm, he⟩
    cases e with
    | readReturn i c sample =>
      dsimp only at he
      split at he <;> simp_all
      exact ⟨t, i, c, sample, hm, by assumption, he.symm⟩
    | _ => simp at he
  · rintro ⟨t, i, c, sample, hm, ho, rfl⟩
    exact ⟨(t, .readReturn i c sample), hm, by simp [ho]⟩

theorem value_at_source {s : State α n} (hs : WriteShape s) {k ti v}
    (h : (ti, Event.writeInvoke k v) ∈ s.history) : valueAt s k = v := by
  classical
  have hex : ∃ w, ∃ tj, (tj, Event.writeInvoke k w) ∈ s.history := ⟨v, ti, h⟩
  simp only [valueAt, dite_eq_left hex]
  obtain ⟨tj, hj⟩ := Classical.choose_spec hex
  exact (hs.2.2.1 k tj _ ti v hj h).2

theorem reads_at_legal {s : State α n} (hw : WriteShape s) (hp : HistoryProvenance s)
    (k : Nat) {rest : List (OpId n × Option (Datum α))}
    (hrest : Sequential k (valueAt s k) rest) :
    Sequential k (valueAt s k) (readsAt s.history k ++ rest) := by
  have hall : ∀ entry ∈ readsAt s.history k, ∃ i c,
      entry = (.read i c, some ⟨valueAt s k, some k⟩) := by
    intro entry he
    obtain ⟨t, i, c, sample, hm, ho, rfl⟩ := reads_at_mem.mp he
    obtain ⟨ti, hi, _⟩ := hp t i c sample k hm ho
    have hv := value_at_source hw hi
    refine ⟨i, c, ?_⟩
    congr 2
    cases hd : sample.datum
    simp_all
  generalize readsAt s.history k = xs at hall ⊢
  induction xs with
  | nil => exact hrest
  | cons x xs ih =>
    obtain ⟨i, c, rfl⟩ := hall x (by simp)
    exact .read (ih (fun e he => hall e (by simp [he])))

theorem common_order_legal {s : State α n} (hw : WriteShape s) (hp : HistoryProvenance s) :
    ∃ v, Sequential 0 v (commonOrder s) := by
  have hblocks : ∀ (ks : List Nat) old oldv, Sequential old oldv (ks.flatMap (writeBlock s)) := by
    intro ks
    induction ks with
    | nil => intro old oldv; exact .nil
    | cons k ks ih =>
      intro old oldv
      simp only [List.flatMap_cons, writeBlock, List.cons_append]
      exact .write (reads_at_legal hw hp k (ih k (valueAt s k)))
  exact ⟨s.writer.value, hblocks _ _ _⟩


theorem filter_map_unique {xs : List β} {f : β → Option γ}
    (hn : (xs.filterMap f).Nodup) {a b : β} {v : γ}
    (ha : a ∈ xs) (hb : b ∈ xs) (hfa : f a = some v) (hfb : f b = some v) : a = b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    have ht : (xs.filterMap f).Nodup := by
      cases hx : f x <;> simp_all
    rcases List.mem_cons.mp ha with rfl | haTail
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · rfl
      · have hv : v ∈ xs.filterMap f := List.mem_filterMap.mpr ⟨b, hbTail, hfb⟩
        simp_all
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · have hv : v ∈ xs.filterMap f := List.mem_filterMap.mpr ⟨a, haTail, hfa⟩
        simp_all
      · exact ih ht haTail hbTail

theorem read_response_unique {s : State α n} (hs : HistoryShape s)
    {t t' i c sample sample'}
    (h : (t, Event.readReturn i c sample) ∈ s.history)
    (h' : (t', Event.readReturn i c sample') ∈ s.history) : t = t' ∧ sample = sample' := by
  have he := filter_map_unique hs.2.2.1 h h' (show responseId _ = some (.read i c) from rfl) rfl
  simpa using he

theorem reads_at_ids_mem {h : List (Nat × Event α n)} {k : Nat} {o : OpId n}
    (ho : o ∈ (readsAt h k).map Prod.fst) : ∃ t, Responded h o t := by
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp ho
  obtain ⟨t, i, c, sample, hm, _, rfl⟩ := reads_at_mem.mp he
  exact ⟨t, sample, hm⟩

theorem reads_at_nodup {h : List (Nat × Event α n)}
    (hn : (h.filterMap (fun te => responseId te.2)).Nodup) (k : Nat) :
    ((readsAt h k).map Prod.fst).Nodup := by
  induction h with
  | nil => simp [readsAt]
  | cons te h ih =>
    obtain ⟨t, e⟩ := te
    cases e with
    | writeInvoke j v => simpa [readsAt, responseId] using ih (by simpa [responseId] using hn)
    | readInvoke i c => simpa [readsAt, responseId] using ih (by simpa [responseId] using hn)
    | writeReturn j =>
      have ht : (h.filterMap (fun te => responseId te.2)).Nodup := by
        simpa [responseId] using (List.nodup_cons.mp (by simpa [responseId] using hn)).2
      simpa [readsAt] using ih ht
    | readReturn i c sample =>
      have hsplit : (.read i c ∉ h.filterMap (fun te => responseId te.2)) ∧
          (h.filterMap (fun te => responseId te.2)).Nodup := by
        simpa [responseId] using hn
      by_cases ho : sample.datum.origin = some k
      · have hnot : .read i c ∉ (readsAt h k).map Prod.fst := by
          intro hm
          exact hsplit.1 ((response_ids_mem h (.read i c)).mpr (reads_at_ids_mem hm))
        simpa [readsAt, ho] using And.intro hnot (ih hsplit.2)
      · simpa [readsAt, ho] using ih hsplit.2


theorem block_ids_mem {s : State α n} {k : Nat} {o : OpId n} :
    o ∈ (writeBlock s k).map Prod.fst ↔ o = .write k ∨ ∃ t i c sample,
      (t, Event.readReturn i c sample) ∈ s.history ∧ sample.datum.origin = some k ∧ o = .read i c := by
  simp only [writeBlock, List.map_cons, List.mem_cons, List.mem_map]
  constructor
  · rintro (ho | ⟨entry, he, rfl⟩)
    · exact .inl ho
    · obtain ⟨t, i, c, sample, hm, ho, rfl⟩ := reads_at_mem.mp he
      exact .inr ⟨t, i, c, sample, hm, ho, rfl⟩
  · rintro (ho | ⟨t, i, c, sample, hm, ho, rfl⟩)
    · exact .inl ho
    · exact .inr ⟨(.read i c, some sample.datum), reads_at_mem.mpr ⟨t, i, c, sample, hm, ho, rfl⟩, rfl⟩

theorem write_block_nodup {s : State α n} (hs : HistoryShape s) (k : Nat) :
    ((writeBlock s k).map Prod.fst).Nodup := by
  simp only [writeBlock, List.map_cons, List.nodup_cons]
  refine ⟨?_, reads_at_nodup hs.2.2.1 k⟩
  intro hm
  obtain ⟨entry, he, hh⟩ := List.mem_map.mp hm
  obtain ⟨t, i, c, sample, _, _, rfl⟩ := reads_at_mem.mp he
  cases hh

theorem write_blocks_disjoint {s : State α n} (hs : HistoryShape s) {k j : Nat}
    (hne : k ≠ j) : ∀ a ∈ (writeBlock s k).map Prod.fst,
      ∀ b ∈ (writeBlock s j).map Prod.fst, a ≠ b := by
  intro a ha b hb hab
  subst b
  rcases block_ids_mem.mp ha with rfl | ⟨t, i, c, sample, hm, ho, rfl⟩
  · rcases block_ids_mem.mp hb with h | ⟨_, _, _, _, _, _, h⟩
    · exact hne (OpId.write.inj h)
    · cases h
  · rcases block_ids_mem.mp hb with h | ⟨t', i', c', sample', hm', ho', h⟩
    · cases h
    · cases h
      have he := (read_response_unique hs hm hm').2
      subst sample'
      exact hne (Option.some.inj (ho.symm.trans ho'))

theorem common_order_nodup {s : State α n} (hs : HistoryShape s) :
    ((commonOrder s).map Prod.fst).Nodup := by
  simp only [commonOrder, List.map_flatMap, List.Nodup, List.pairwise_flatMap]
  exact ⟨fun k _ => write_block_nodup hs k,
    (List.nodup_range (n := s.writer.index + 1)).imp (fun {k j} hne => write_blocks_disjoint hs hne)⟩

theorem common_order_ids {s : State α n} (hw : WriteShape s) (hp : HistoryProvenance s)
    (hi : HistorySafety s) {o : OpId n} :
    o ∈ (commonOrder s).map Prod.fst ↔
      (∃ k, o = .write k ∧ k ≤ s.writer.index) ∨
      (∃ t i c sample, (t, Event.readReturn i c sample) ∈ s.history ∧ o = .read i c) := by
  simp only [commonOrder, List.map_flatMap, List.mem_flatMap]
  constructor
  · rintro ⟨k, hk, ho⟩
    rcases block_ids_mem.mp ho with rfl | ⟨t, i, c, sample, hm, _, rfl⟩
    · exact .inl ⟨k, rfl, by simpa [Nat.lt_succ_iff] using hk⟩
    · exact .inr ⟨t, i, c, sample, hm, rfl⟩
  · rintro (⟨k, rfl, hk⟩ | ⟨t, i, c, sample, hm, rfl⟩)
    · exact ⟨k, by simpa [Nat.lt_succ_iff] using hk, block_ids_mem.mpr (.inl rfl)⟩
    · have hg := (hi t i c sample hm).2
      cases ho : sample.datum.origin with
      | none => exact False.elim (hg ho)
      | some k =>
        obtain ⟨ti, hsource, _⟩ := hp t i c sample k hm ho
        have hk := (hw.1 k).mp ⟨ti, sample.datum.value, hsource⟩
        exact ⟨k, by simpa [Nat.lt_succ_iff] using hk, block_ids_mem.mpr (.inr ⟨t, i, c, sample, hm, ho, rfl⟩)⟩


/-- A local list-order witness used to connect chronological filtering to blocks. -/
def Earlier (xs : List β) (a b : β) : Prop :=
  ∃ l m r, xs = l ++ [a] ++ m ++ [b] ++ r

theorem earlier_of_pairwise {xs : List β} (rank : β → Nat)
    (hp : xs.Pairwise (fun a b => rank a < rank b)) {a b : β}
    (ha : a ∈ xs) (hb : b ∈ xs) (hlt : rank a < rank b) : Earlier xs a b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp ha with rfl | haTail
    · have hb' : b ∈ xs := by rcases List.mem_cons.mp hb with rfl | hb; omega; exact hb
      obtain ⟨l, r, rfl⟩ := List.mem_iff_append.mp hb'
      exact ⟨[], l, r, by simp⟩
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · have := hhead a haTail
        omega
      · obtain ⟨l, m, r, he⟩ := ih htail haTail hbTail
        exact ⟨x :: l, m, r, by simp [he]⟩

theorem earlier_filter_map {xs : List β} {a b : β} {f : β → Option γ} {x y : γ}
    (he : Earlier xs a b) (hx : f a = some x) (hy : f b = some y) :
    Earlier (xs.filterMap f) x y := by
  obtain ⟨l, m, r, rfl⟩ := he
  exact ⟨l.filterMap f, m.filterMap f, r.filterMap f, by simp [hx, hy]⟩

theorem before_flat_map {ks : List Nat} {k j : Nat} {f : Nat → List (OpId n)}
    (he : Earlier ks k j) {a b : OpId n} (ha : a ∈ f k) (hb : b ∈ f j) :
    Before (ks.flatMap f) a b := by
  obtain ⟨l, m, r, rfl⟩ := he
  obtain ⟨la, ra, hka⟩ := List.mem_iff_append.mp ha
  obtain ⟨lb, rb, hjb⟩ := List.mem_iff_append.mp hb
  exact ⟨l.flatMap f ++ la, ra ++ m.flatMap f ++ lb, rb ++ r.flatMap f,
    by simp [hka, hjb, List.append_assoc]⟩

theorem common_order_before_blocks {s : State α n} {k j : Nat}
    (hk : k ≤ s.writer.index) (hj : j ≤ s.writer.index) (hlt : k < j)
    {a b : OpId n} (ha : a ∈ (writeBlock s k).map Prod.fst)
    (hb : b ∈ (writeBlock s j).map Prod.fst) :
    Before ((commonOrder s).map Prod.fst) a b := by
  simp only [commonOrder, List.map_flatMap]
  apply before_flat_map (earlier_of_pairwise id (List.pairwise_lt_range (n := s.writer.index + 1)) (by simpa [Nat.lt_succ_iff] using hk)
    (by simpa [Nat.lt_succ_iff] using hj) hlt) ha hb

theorem before_in_block {s : State α n} {k : Nat} (hk : k ≤ s.writer.index)
    {a b : OpId n} (h : Before ((writeBlock s k).map Prod.fst) a b) :
    Before ((commonOrder s).map Prod.fst) a b := by
  have hmem : k ∈ List.range (s.writer.index + 1) := by simpa [Nat.lt_succ_iff] using hk
  obtain ⟨l, r, he⟩ := List.mem_iff_append.mp hmem
  obtain ⟨la, m, ra, hb⟩ := h
  refine ⟨l.flatMap (fun j => (writeBlock s j).map Prod.fst) ++ la, m,
    ra ++ r.flatMap (fun j => (writeBlock s j).map Prod.fst), ?_⟩
  simp [commonOrder, List.map_flatMap, he, hb, List.append_assoc]

theorem write_before_read {s : State α n} {k t i c sample}
    (hk : k ≤ s.writer.index) (hm : (t, Event.readReturn i c sample) ∈ s.history)
    (ho : sample.datum.origin = some k) :
    Before ((commonOrder s).map Prod.fst) (.write k) (.read i c) := by
  apply before_in_block hk
  have hr : .read i c ∈ (readsAt s.history k).map Prod.fst :=
    List.mem_map.mpr ⟨(.read i c, some sample.datum),
      reads_at_mem.mpr ⟨t, i, c, sample, hm, ho, rfl⟩, rfl⟩
  obtain ⟨l, r, he⟩ := List.mem_iff_append.mp hr
  exact ⟨[], l, r, by simp [writeBlock, he]⟩

theorem read_before_read_same {s : State α n} (hp : s.history.Pairwise (fun a b => a.1 < b.1))
    {k t i c sample t' i' c' sample'} (hk : k ≤ s.writer.index)
    (hm : (t, Event.readReturn i c sample) ∈ s.history) (ho : sample.datum.origin = some k)
    (hm' : (t', Event.readReturn i' c' sample') ∈ s.history) (ho' : sample'.datum.origin = some k)
    (hlt : t < t') : Before ((commonOrder s).map Prod.fst) (.read i c) (.read i' c') := by
  have he := earlier_of_pairwise Prod.fst hp hm hm' hlt
  have hf := earlier_filter_map (x := .read i c) (y := .read i' c') (f := fun te : Nat × Event α n =>
    match te.2 with
    | .readReturn j d x => if x.datum.origin = some k then some (.read j d : OpId n) else none
    | _ => none) he (by simp [ho]) (by simp [ho'])
  have hid : (readsAt s.history k).map Prod.fst = s.history.filterMap (fun te =>
      match te.2 with
      | .readReturn j d x => if x.datum.origin = some k then some (.read j d : OpId n) else none
      | _ => none) := by
    rw [readsAt, List.map_filterMap]
    congr 1
    funext te
    obtain ⟨tm, e⟩ := te
    cases e <;> simp
  rw [← hid] at hf
  obtain ⟨l, m, r, he⟩ := hf
  apply before_in_block hk
  exact ⟨.write k :: l, m, r, by simp [writeBlock, he]⟩


theorem pending_extension_responses {s : State α n} (hw : WriteShape s) :
    ∀ t e, (t, e) ∈ pendingExtension s → s.clock ≤ t ∧
      match e with
      | .writeReturn k => (∃ ti, Invoked s.history (.write k) ti) ∧
          ¬ ∃ tr, Responded s.history (.write k) tr
      | .readReturn i c _ => (∃ ti, Invoked s.history (.read i c) ti) ∧
          ¬ ∃ tr, Responded s.history (.read i c) tr
      | _ => False := by
  intro t e hm
  unfold pendingExtension at hm
  split at hm
  · simp at hm
  · simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨Nat.le_refl _, ?_, ?_⟩
    · obtain ⟨ti, v, hi⟩ := (hw.1 s.writer.index).mpr (Nat.le_refl _)
      exact ⟨ti, v, hi⟩
    · intro hret
      have hh := (hw.2.2.2.2.1 s.writer.index).mp hret
      simp_all

theorem extended_write_responses {s : State α n} (hw : WriteShape s) (k : Nat) :
    (∃ t, Responded (s.history ++ pendingExtension s) (.write k) t) ↔ k ≤ s.writer.index := by
  simp only [Responded, List.mem_append, exists_or]
  rw [hw.2.2.2.2.1 k]
  by_cases hp : s.writer.pc = 0
  · simp [pendingExtension, hp]
    omega
  · simp [pendingExtension, hp]
    omega

theorem extended_read_return {s : State α n} {t i c sample} :
    (t, Event.readReturn i c sample) ∈ s.history ++ pendingExtension s ↔
      (t, Event.readReturn i c sample) ∈ s.history := by
  by_cases hp : s.writer.pc = 0 <;> simp [pendingExtension, hp]

theorem extended_history_lists {s : State α n} (hs : HistoryShape s) (hc : ClockFacts s) :
    ((s.history ++ pendingExtension s).filterMap (fun te => responseId te.2)).Nodup ∧
    (s.history ++ pendingExtension s).Pairwise (fun a b => a.1 < b.1) := by
  by_cases hp : s.writer.pc = 0
  · simpa [pendingExtension, hp] using hs.2.2
  · simp only [pendingExtension, ite_eq_right hp]
    apply history_list_append hs.2.2.1 hs.2.2.2 hc
    intro o ho
    simp only [responseId, Option.some.injEq] at ho
    subst o
    intro hret
    have hh := (hs.1.2.2.2.2.1 s.writer.index).mp hret
    omega

theorem common_order_coverage {s : State α n} (hs : HistoryShape s)
    (hp : HistoryProvenance s) (hi : HistorySafety s) (o : OpId n) :
    o ∈ (commonOrder s).map Prod.fst ↔ ∃ t, Responded (s.history ++ pendingExtension s) o t := by
  rw [common_order_ids hs.1 hp hi]
  cases o with
  | write k => simpa using (extended_write_responses hs.1 k).symm
  | read i c =>
    simp only [Responded, extended_read_return]
    simp

theorem common_order_invoked {s : State α n} (hs : HistoryShape s)
    (hp : HistoryProvenance s) (hi : HistorySafety s) (o : OpId n)
    (ho : o ∈ (commonOrder s).map Prod.fst) : ∃ t, Invoked s.history o t := by
  rcases (common_order_ids hs.1 hp hi).mp ho with ⟨k, rfl, hk⟩ | ⟨t, i, c, sample, hm, rfl⟩
  · obtain ⟨ti, v, hsource⟩ := (hs.1.1 k).mpr hk
    exact ⟨ti, v, hsource⟩
  · exact ⟨c, hs.2.1.2.1 t i c sample hm⟩

theorem common_order_initial_first (s : State α n) :
    ∃ v rest, commonOrder s = (.write 0, some ⟨v, some 0⟩) :: rest := by
  refine ⟨valueAt s 0, readsAt s.history 0 ++
    ((List.range s.writer.index).map Nat.succ).flatMap (writeBlock s), ?_⟩
  simp [commonOrder, List.range_succ_eq_map, writeBlock]

theorem common_order_write_values {s : State α n} (hw : WriteShape s) :
    ∀ k d, (.write k, d) ∈ commonOrder s →
      ∃ t v, (t, Event.writeInvoke k v) ∈ s.history ∧ d = some ⟨v, some k⟩ := by
  intro k d hm
  obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp hm
  simp only [writeBlock, List.mem_cons, Prod.mk.injEq, OpId.write.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | hm
  · obtain ⟨t, v, hv⟩ := (hw.1 k).mpr (by simpa [Nat.lt_succ_iff] using hj)
    exact ⟨t, v, hv, by rw [value_at_source hw hv]⟩
  · obtain ⟨t, i, c, sample, _, _, he⟩ := reads_at_mem.mp hm
    cases he

theorem common_order_read_values {s : State α n} (hw : WriteShape s)
    (hp : HistoryProvenance s) (hi : HistorySafety s) :
    ∀ t i c sample, (t, Event.readReturn i c sample) ∈ s.history ++ pendingExtension s →
      (.read i c, some sample.datum) ∈ commonOrder s := by
  intro t i c sample hm
  have hm' := extended_read_return.mp hm
  have hg := (hi t i c sample hm').2
  cases ho : sample.datum.origin with
  | none => exact False.elim (hg ho)
  | some k =>
    obtain ⟨ti, hsource, _⟩ := hp t i c sample k hm' ho
    have hk := (hw.1 k).mp ⟨ti, sample.datum.value, hsource⟩
    apply List.mem_flatMap.mpr
    exact ⟨k, by simpa [Nat.lt_succ_iff] using hk, List.mem_cons_of_mem _
      (reads_at_mem.mpr ⟨t, i, c, sample, hm', ho, rfl⟩)⟩


theorem invoked_time_lt {s : State α n} (hc : ClockFacts s) {o : OpId n} {t}
    (h : Invoked s.history o t) : t < s.clock := by
  cases o with
  | write k => obtain ⟨v, hv⟩ := h; exact hc.1 t _ hv
  | read i c => exact hc.1 t _ h

theorem earlier_response_original {s : State α n} (hc : ClockFacts s) {a b : OpId n} {ta tb}
    (ha : Responded (s.history ++ pendingExtension s) a ta)
    (hb : Invoked s.history b tb) (hlt : ta < tb) : Responded s.history a ta := by
  have ht := invoked_time_lt hc hb
  cases a with
  | write k =>
    change (ta, Event.writeReturn k) ∈ s.history ++ pendingExtension s at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ha
    · by_cases hpc : s.writer.pc = 0
      · simp [pendingExtension, hpc] at ha
      · simp [pendingExtension, hpc] at ha
        omega
  | read i c =>
    obtain ⟨sample, hm⟩ := ha
    exact ⟨sample, extended_read_return.mp hm⟩

theorem returned_origin {s : State α n} (hi : HistorySafety s) {t i c sample}
    (hm : (t, Event.readReturn i c sample) ∈ s.history) : ∃ k, sample.datum.origin = some k := by
  have hg := (hi t i c sample hm).2
  cases ho : sample.datum.origin with
  | none => exact False.elim (hg ho)
  | some k => exact ⟨k, rfl⟩

theorem returned_source_bound {s : State α n} (hw : WriteShape s) (hp : HistoryProvenance s)
    {t i c sample k} (hm : (t, Event.readReturn i c sample) ∈ s.history)
    (ho : sample.datum.origin = some k) : k ≤ s.writer.index := by
  obtain ⟨ti, hi, _⟩ := hp t i c sample k hm ho
  exact (hw.1 k).mp ⟨ti, sample.datum.value, hi⟩

theorem common_read_completed {s : State α n} (hs : HistoryShape s)
    (hp : HistoryProvenance s) (hi : HistorySafety s) {i c}
    (hm : .read i c ∈ (commonOrder s).map Prod.fst) :
    ∃ t sample, (t, Event.readReturn i c sample) ∈ s.history := by
  simpa using (common_order_ids hs.1 hp hi).mp hm

theorem common_order_realtime {s : State α n} (hs : HistoryShape s)
    (hp : HistoryProvenance s) (hi : HistorySafety s) (hc : ClockFacts s)
    (ho : HistoryOrdered s) :
    ∀ a b ta tb, Responded (s.history ++ pendingExtension s) a ta →
      Invoked s.history b tb → ta < tb → b ∈ (commonOrder s).map Prod.fst →
      Before ((commonOrder s).map Prod.fst) a b := by
  intro a b ta tb ha hb hlt hbmem
  have ha' := earlier_response_original hc ha hb hlt
  cases a with
  | write j =>
    have hj : j ≤ s.writer.index := by
      have hh := (hs.1.2.2.2.2.1 j).mp ⟨ta, ha'⟩
      omega
    cases b with
    | write k =>
      obtain ⟨v, hv⟩ := hb
      have hk := (hs.1.1 k).mp ⟨tb, v, hv⟩
      have hrel := hs.1.2.2.2.2.2 k tb v j ta hv ha'
      apply common_order_before_blocks hj hk (by omega)
      · exact block_ids_mem.mpr (.inl rfl)
      · exact block_ids_mem.mpr (.inl rfl)
    | read i c =>
      have htc := hs.2.1.1 tb i c hb
      subst tb
      obtain ⟨tr, sample, hr⟩ := common_read_completed hs hp hi hbmem
      obtain ⟨k, hk⟩ := returned_origin hi hr
      have hbound := returned_source_bound hs.1 hp hr hk
      have hle := (ho tr i c sample k hr hk).1 j ta ha' hlt
      by_cases he : j = k
      · subst j
        exact write_before_read hbound hr hk
      · apply common_order_before_blocks hj hbound (by omega)
        · exact block_ids_mem.mpr (.inl rfl)
        · exact block_ids_mem.mpr (.inr ⟨tr, i, c, sample, hr, hk, rfl⟩)
  | read i c =>
    obtain ⟨sample, hr⟩ := ha'
    obtain ⟨j, hj⟩ := returned_origin hi hr
    have hjbound := returned_source_bound hs.1 hp hr hj
    cases b with
    | write k =>
      obtain ⟨v, hv⟩ := hb
      have hk := (hs.1.1 k).mp ⟨tb, v, hv⟩
      obtain ⟨tj, hsource, hjtime⟩ := hp ta i c sample j hr hj
      have hrel := hs.1.2.2.2.1 j tj sample.datum.value k tb v hsource hv
      apply common_order_before_blocks hjbound hk (hrel.mpr (by omega))
      · exact block_ids_mem.mpr (.inr ⟨ta, i, c, sample, hr, hj, rfl⟩)
      · exact block_ids_mem.mpr (.inl rfl)
    | read i' c' =>
      have htc := hs.2.1.1 tb i' c' hb
      subst tb
      obtain ⟨tr, sample', hr'⟩ := common_read_completed hs hp hi hbmem
      obtain ⟨k, hk⟩ := returned_origin hi hr'
      have hkbound := returned_source_bound hs.1 hp hr' hk
      have hle := (ho tr i' c' sample' k hr' hk).2 ta i c sample j hr hj hlt
      by_cases he : j = k
      · subst j
        have hct := hc.2.2 tr i' c' sample' hr'
        exact read_before_read_same hs.2.2.2 hkbound hr hj hr' hk (by omega)
      · apply common_order_before_blocks hjbound hkbound (by omega)
        · exact block_ids_mem.mpr (.inr ⟨ta, i, c, sample, hr, hj, rfl⟩)
        · exact block_ids_mem.mpr (.inr ⟨tr, i', c', sample', hr', hk, rfl⟩)

/-- The common finite-history order includes every invoked write, completing the
sole pending writer if present, and omits pending reads. -/
theorem linearization_exists {v : α} {privateData : Fin n → α} {s : State α n}
    (hr : Reachable v privateData s) : Nonempty (Linearization s) := by
  have hs := history_shape_reachable hr
  have hp := (provenance_reachable hr).2.2.2.2
  obtain ⟨hc, floor, _, hh⟩ := ordering_invariant_reachable hr
  have hi := hc.2.2.2
  have hl := extended_history_lists hs hh.1
  exact ⟨{
    extension := pendingExtension s
    order := commonOrder s
    extensionResponses := pending_extension_responses hs.1
    responseUnique := hl.1
    eventTimes := hl.2
    unique := common_order_nodup hs
    coverage := common_order_coverage hs hp hi
    invoked := common_order_invoked hs hp hi
    realtime := common_order_realtime hs hp hi hh.1 hh.2.2.2
    initialFirst := common_order_initial_first s
    writeValues := common_order_write_values hs.1
    readValues := common_order_read_values hs.1 hp hi
    legal := common_order_legal hs.1 hp }⟩

/-- The unchanged common-order target for every finite reachable history. -/
theorem common_ordering : CommonOrdering := by
  intro α n _ v privateData s hr
  exact linearization_exists hr

end ConcurrentReading
