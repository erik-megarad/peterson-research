module
public import CircularElection.Progress
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Actual transmission bounds for arbitrary prefixes through first detection. -/
@[expose] public section
open scoped BigOperators
namespace CircularElection
variable {n : Nat} {Id : Type} [LinearOrder Id]
namespace Frontier
variable {owner : Fin n → Id}

/-- A surviving carrier and its predecessor occupy disjoint positions. -/
theorem advance_size_half (f : Frontier owner) (hi : Function.Injective owner)
    (hm : 1 < f.size) : 2 * (f.advance hi).size ≤ f.size := by
  let s := f.survivors
  let e := (finRotate f.size).symm
  have hd : Disjoint s (s.image e) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq
    have hs : RoundSurvives f.candidate e q := by simpa [s, survivors] using hq
    have hn := round_no_adjacent f.candidate e q
      (fun he => rotate_previous_ne (by omega) _ ((f.candidate_injective hi he).symm)) hs
    exact hn (by simpa [s, survivors] using hp)
  have hc : (s.image e).card = s.card := Finset.card_image_of_injective _ e.injective
  have hu := Finset.card_le_card (Finset.subset_univ (s ∪ s.image e))
  rw [Finset.card_union_of_disjoint hd, hc] at hu
  simpa [advance, s, Nat.two_mul] using hu

/-- A singleton stays a singleton in the prospective recurrence. -/
theorem advance_size_one (f : Frontier owner) (hi : Function.Injective owner)
    (hm : f.size = 1) : (f.advance hi).size = 1 := by
  have h := Finset.card_le_card (Finset.subset_univ f.survivors)
  have hp := (f.advance hi).positive
  simp only [Finset.card_univ, Fintype.card_fin] at h
  change (f.advance hi).size ≤ f.size at h
  omega
end Frontier
variable (owner : Fin n → Id) (hn : 0 < n) (hi : Function.Injective owner)

/-- Until only one carrier remains, each round pays a factor of two. -/
theorem frontier_power_bound (r : Nat)
    (hr : 1 < (frontierAt owner hn hi r).size) :
    2 ^ r * (frontierAt owner hn hi r).size ≤ n := by
  induction r with
  | zero => simp [frontierAt, Frontier.first]
  | succ r ih =>
    have hp := (frontierAt owner hn hi r).positive
    have hprev : 1 < (frontierAt owner hn hi r).size := by
      by_contra hh
      have he : (frontierAt owner hn hi r).size = 1 := by omega
      have hh := (frontierAt owner hn hi r).advance_size_one hi he
      change (frontierAt owner hn hi (r + 1)).size = 1 at hh
      omega
    have hh := (frontierAt owner hn hi r).advance_size_half hi hprev
    have he := Nat.mul_le_mul_left (2 ^ r) hh
    rw [pow_succ]
    exact le_trans (by simpa [frontierAt, Nat.mul_assoc] using he) (ih hprev)

/-- By floor(log₂ n) the ideal frontier is a singleton, including n=1. -/
theorem frontier_log_singleton :
    (frontierAt owner hn hi (Nat.log 2 n)).size = 1 := by
  have hp := (frontierAt owner hn hi (Nat.log 2 n)).positive
  by_contra hh
  have hb := frontier_power_bound owner hn hi (Nat.log 2 n) (by omega)
  have ht : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_of_log_lt (by decide) (by omega)
  have hm := Nat.mul_le_mul_left (2 ^ Nat.log 2 n)
    (show 2 ≤ (frontierAt owner hn hi (Nat.log 2 n)).size by omega)
  rw [pow_succ] at ht
  omega

/-- A noncarrier cannot create an extra occurrence after the chosen frontier. -/
theorem local_plan_late_relay (p : Fin n) (R sent received : Nat) (l : Local Id)
    (hp : LocalPlan owner hn hi p sent received l) (he : l.pc ≠ .elected)
    (ha : ¬ (frontierAt owner hn hi R).Active p) :
    sent ≤ max (2 * R) received := by
  cases hc : l.pc <;> simp only [LocalPlan, hc] at hp
  all_goals try (exfalso; exact he hc)
  all_goals try omega
  all_goals rcases hp with ⟨r, hs, hr, hactive, hrest⟩
  all_goals
    have hlt : r < R := by
      by_contra hh
      exact ha (frontier_active_decreases owner hn hi p (by omega) hactive)
    omega

omit owner hn hi in
/-- Traversing fewer than n ring positions visits a designated carrier at most once. -/
theorem rotate_hits_once (hn : 0 < n) (p a : Fin n) (k : Nat) (hk : k ≤ n) :
    ((Finset.range k).filter (fun j => (finRotate n)^[j] p = a)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi, hei⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj, hej⟩ := Finset.mem_filter.mp hj
  have hi' : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
  have hj' : j < n := lt_of_lt_of_le (Finset.mem_range.mp hj) hk
  let : NeZero n := ⟨by omega⟩
  have hh : p + (⟨i, hi'⟩ : Fin n) = p + (⟨j, hj'⟩ : Fin n) := by
    have hiEq := congrFun (finCycle_eq_finRotate_iterate (k := (⟨i, hi'⟩ : Fin n))) p
    have hjEq := congrFun (finCycle_eq_finRotate_iterate (k := (⟨j, hj'⟩ : Fin n))) p
    simpa only [finCycle_apply] using hiEq.trans (hei.trans (hej.symm.trans hjEq.symm))
  have hh' := add_left_cancel hh
  exact congrArg Fin.val hh'

omit owner hn hi in
/-- A ring with only one possible +1 source has at most one unit of count skew.
A floor allows earlier rounds still to be in progress at other processes. -/
theorem ring_single_source_bound (hn : 0 < n) (v : Fin n → Nat) (a p : Fin n)
    (B : Nat) (hp : v p ≤ B)
    (hstep : ∀ q, v (next q) ≤ max B (v q) + if next q = a then 1 else 0) :
    ∀ q, v q ≤ B + 1 := by
  let start := next p
  have hit (k : Nat) : v ((finRotate n)^[k] p) ≤ B +
      ((Finset.range k).filter (fun j => (finRotate n)^[j] start = a)).card := by
    induction k with
    | zero => simpa using hp
    | succ k ih =>
      have hs := hstep ((finRotate n)^[k] p)
      rw [← rotate_is_actual_next, ← Function.iterate_succ_apply' (finRotate n)] at hs
      have hx : (finRotate n)^[k + 1] p = (finRotate n)^[k] start := by
        simp only [start, ← rotate_is_actual_next, Function.iterate_succ_apply]
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases ha : (finRotate n)^[k] start = a
      · simp only [ha, ite_true]
        rw [Finset.card_insert_of_notMem (by simp)]
        simp only [hx, ha, ite_true] at hs ⊢
        omega
      · simp only [ha, ite_false]
        simp only [hx, ite_eq_right ha] at hs ⊢
        omega
  intro q
  let : NeZero n := ⟨by omega⟩
  let k : Fin n := q - p
  have he : (finRotate n)^[k.val] p = q := by
    rw [← finCycle_eq_finRotate_iterate, finCycle_apply]
    simp [k]
  have hh := hit k.val
  have hc := rotate_hits_once hn start a k.val (by omega)
  rw [he] at hh
  omega

/-- The original owner of the singleton candidate sees its own ID at occurrence 2R. -/
theorem singleton_return_at (R : Nat)
    (hR : (frontierAt owner hn hi R).size = 1) :
    ∃ p, inputAt owner hn hi p (2 * R) = owner p := by
  let f := frontierAt owner hn hi R
  let c : Fin f.size := ⟨0, f.positive⟩
  refine ⟨f.origin c, ?_⟩
  rw [inputAt_even]
  change f.candidate ((finRotate f.size).symm (f.block (f.origin c))) = owner (f.origin c)
  have he : (finRotate f.size).symm (f.block (f.origin c)) = c := by
    apply Fin.ext
    have hh := ((finRotate f.size).symm (f.block (f.origin c))).isLt
    have hc := c.isLt
    change f.size = 1 at hR
    omega
  rw [he]
  rfl

/-- The actual FIFO counters are bounded independently of asynchronous skew. -/
theorem singleton_sent_bound (R : Nat)
    (hR : (frontierAt owner hn hi R).size = 1)
    {s : State n Id} {rc : Fin n → Nat}
    (hp : Planned owner hn hi s rc) (hno : ¬ Announced s)
    (p : Fin n) (hb : rc p ≤ 2 * R) : ∀ q, s.sent q ≤ 2 * R + 2 := by
  let f := frontierAt owner hn hi R
  let c : Fin f.size := ⟨0, f.positive⟩
  let a := f.physical c
  have hactive (q : Fin n) (ha : q ≠ a) : ¬ f.Active q := by
    rintro ⟨d, hd⟩
    have he : d = c := by
      apply Fin.ext
      have hd' := d.isLt
      have hc := c.isLt
      change f.size = 1 at hR
      omega
    exact ha (hd ▸ congrArg f.physical he)
  have hstep (q : Fin n) : s.sent (next q) ≤ max (2 * R + 1) (s.sent q) +
      if next q = a then 1 else 0 := by
    have hq := hp.counts.2 q
    by_cases he : next q = a
    · rw [ite_eq_left he]
      have hl := local_count_bounds (hp.counts.1 (next q))
        (fun h => hno ⟨next q, h⟩)
      omega
    · rw [ite_eq_right he]
      have hl := local_plan_late_relay owner hn hi (next q) R _ _ _
        (hp.locals (next q)) (fun h => hno ⟨next q, h⟩) (hactive (next q) he)
      omega
  have hc := local_count_bounds (hp.counts.1 p) (fun h => hno ⟨p, h⟩)
  exact ring_single_source_bound hn s.sent a p (2 * R + 1) (by omega) hstep

omit hn hi in
/-- Every global transmission is exactly one of the per-edge transmissions. -/
theorem step_send_total {s t : State n Id} {a : Action n}
    (ht : (lts owner).Tr s a t) (hs : s.sends = ∑ p, s.sent p) :
    t.sends = ∑ p, t.sent p := by
  change execute owner s a = some t at ht
  cases a with
  | idle =>
    simp only [execute, Option.some.injEq] at ht
    exact ht ▸ hs
  | deliver p =>
    cases he : s.edge p with
    | nil => simp [execute, he] at ht
    | cons v rest =>
      simp only [execute, he, Option.some.injEq] at ht
      subst t
      exact hs
  | send p | receive p | compare p =>
    simp only [execute, Option.map_eq_some_iff] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    rcases z with ⟨l, q, out⟩
    cases out with
    | none => exact hs
    | some v =>
      simp only [commitLocal]
      rw [Finset.sum_update_of_mem (Finset.mem_univ p)]
      rw [Finset.sdiff_singleton_eq_erase]
      have hh := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) s.sent (Finset.mem_univ p)
      omega

omit hn hi in
/-- A protocol step can add at most one real edge transmission. -/
theorem step_sends_le_one {s t : State n Id} {a : Action n}
    (ht : (lts owner).Tr s a t) : t.sends ≤ s.sends + 1 := by
  change execute owner s a = some t at ht
  cases a with
  | idle => simp_all [execute]
  | deliver p =>
    cases he : s.edge p with
    | nil => simp [execute, he] at ht
    | cons v rest =>
      simp only [execute, he, Option.some.injEq] at ht
      subst t
      simp
  | send p | receive p | compare p =>
    simp only [execute, Option.map_eq_some_iff] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    rcases z with ⟨l, q, out⟩
    cases out <;> simp [commitLocal]

/-- Consuming the chosen returning occurrence would end the nonannouncing prefix. -/
theorem step_return_barrier (p : Fin n) (k : Nat)
    (hv : inputAt owner hn hi p k = owner p)
    {s t : State n Id} {rc : Fin n → Nat} {a : Action n}
    (hp : Planned owner hn hi s rc) (hb : rc p ≤ k)
    (ht : (lts owner).Tr s a t) (hno : ¬ Announced t) :
    receivedAfter rc a p ≤ k := by
  cases a with
  | idle | deliver q | send q | compare q => simpa [receivedAfter] using hb
  | receive q =>
    by_cases he : p = q
    · subst q
      simp only [receivedAfter, Function.update_self]
      by_contra hh
      have hr : rc p = k := by omega
      exact hno (receive_return_announces owner hn hi s t p rc hp (by simpa [hr] using hv) ht)
    · simpa [receivedAfter, Function.update_of_ne he] using hb

/-- Summing per-edge bounds counts active and relay sends alike. -/
theorem singleton_total_bound (R : Nat)
    (hR : (frontierAt owner hn hi R).size = 1)
    {s : State n Id} {rc : Fin n → Nat}
    (hp : Planned owner hn hi s rc) (hno : ¬ Announced s)
    (hs : s.sends = ∑ q, s.sent q) (p : Fin n) (hb : rc p ≤ 2 * R) :
    s.sends ≤ n * (2 * R + 2) := by
  rw [hs]
  calc
    ∑ q, s.sent q ≤ ∑ _q : Fin n, (2 * R + 2) :=
      Finset.sum_le_sum (fun q _ => singleton_sent_bound owner hn hi R hR hp hno p hb q)
    _ = n * (2 * R + 2) := by simp

/-- The final step is included; a terminal partial round requires no completion
or fairness assumption. One harmless unit of slack covers that last step. -/
theorem beforeFirst_sends_bound (R : Nat)
    (hR : (frontierAt owner hn hi R).size = 1)
    {as : List (Action n)} {s : State n Id}
    (h : BeforeFirst owner (initial owner) as s) :
    s.sends ≤ n * (2 * R + 2) + 1 := by
  obtain ⟨p, hv⟩ := singleton_return_at owner hn hi R hR
  have aux : ∀ {u v : State n Id} {as : List (Action n)}, BeforeFirst owner u as v →
      ∀ rc, Planned owner hn hi u rc → ¬ Announced u →
      u.sends = ∑ q, u.sent q → rc p ≤ 2 * R →
      v.sends ≤ n * (2 * R + 2) + 1 := by
    intro u v as ht
    induction ht with
    | nil u =>
      intro rc hp hno hs hb
      have hh := singleton_total_bound owner hn hi R hR hp hno hs p hb
      omega
    | @cons u v w a as hno ht htail ih =>
      intro rc hp _ hs hb
      have hcost := singleton_total_bound owner hn hi R hR hp hno hs p hb
      by_cases hvno : Announced v
      · cases htail with
        | nil =>
          have hh := step_sends_le_one owner ht
          omega
        | cons hcontra _ _ => exact (hcontra hvno).elim
      · exact ih (receivedAfter rc a) (step_planned owner hn hi hp ht) hvno
          (step_send_total owner ht hs) (step_return_barrier owner hn hi p (2 * R) hv hp hb ht hvno)
  apply aux h (fun _ => 0)
  · refine ⟨?_, ?_, ?_⟩
    · simp [Counted, LocalCount, initial]
    · intro q
      refine ⟨0, rfl, rfl, ?_, rfl⟩
      exact ⟨q, rfl⟩
    · intro q
      trivial
  · simp [Announced, initial]
  · simp [initial]
  · omega

/-- Uniform source-close complexity for every positive ring and every finite
prefix through first announcement, including unfair prefixes and n=1. -/
theorem message_complexity : MessageComplexity := by
  refine ⟨3, by decide, ?_⟩
  intro n hn Id inst owner hi as s h
  have hb := beforeFirst_sends_bound owner hn hi (Nat.log 2 n)
    (frontier_log_singleton owner hn hi) h
  have hpos : 1 ≤ n * (1 + Nat.log 2 n) := Nat.mul_pos hn (by omega)
  have he : n * (2 * Nat.log 2 n + 2) = 2 * (n * (1 + Nat.log 2 n)) := by
    simp only [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm n 2]
    omega
  rw [Nat.mul_assoc]
  omega
end CircularElection
