module
public import CircularElection.IdealRound
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Fin

/-! Order-preserving compression of a finite cyclic carrier set. -/
@[expose] public section
namespace CircularElection

/-- The block ending at the first selected carrier at or after c, with wrap. -/
def compressedBlock {m : Nat} (s : Finset (Fin m)) (hs : 0 < s.card) (c : Fin m) : Fin s.card :=
  ⟨(s.filter (· < c)).card % s.card, Nat.mod_lt _ hs⟩

theorem selected_rank {m : Nat} (s : Finset (Fin m)) (i : Fin s.card) :
    (s.filter (· < s.orderEmbOfFin rfl i)).card = i.val := by
  classical
  have he : s.filter (· < s.orderEmbOfFin rfl i) =
      Finset.image (s.orderEmbOfFin rfl) (Finset.Iio i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨hx, hlt⟩
      let j := (s.orderIsoOfFin rfl).symm ⟨x, hx⟩
      have hj : s.orderEmbOfFin rfl j = x := by
        exact congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)
      refine ⟨j, ?_, hj⟩
      apply (s.orderEmbOfFin rfl).lt_iff_lt.mp
      simpa [hj] using hlt
    · rintro ⟨j, hj, rfl⟩
      exact ⟨s.orderEmbOfFin_mem rfl j, (s.orderEmbOfFin rfl).strictMono hj⟩
  rw [he, Finset.card_image_of_injective _ (s.orderEmbOfFin rfl).injective, Fin.card_Iio]

theorem compressedBlock_selected {m : Nat} (s : Finset (Fin m)) (hs : 0 < s.card)
    (i : Fin s.card) : compressedBlock s hs (s.orderEmbOfFin rfl i) = i := by
  apply Fin.ext
  simp [compressedBlock, selected_rank, Nat.mod_eq_of_lt i.isLt]

/-- Before cyclic wrap the rank increases only at a selected carrier. -/
theorem rank_next_of_not_last {m : Nat} (s : Finset (Fin m)) (c : Fin m)
    (hstep : c.val + 1 < m) :
    (s.filter (· < next c)).card = (s.filter (· < c)).card + if c ∈ s then 1 else 0 := by
  classical
  by_cases hc : c ∈ s
  · have he : s.filter (· < next c) = insert c (s.filter (· < c)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      have hv : (next c).val = c.val + 1 := Nat.mod_eq_of_lt hstep
      constructor
      · rintro ⟨hx, hlt⟩
        by_cases heq : x = c
        · exact Or.inl heq
        · right; refine ⟨hx, ?_⟩
          have ht : x.val < (next c).val := hlt
          have hn : x.val ≠ c.val := fun h => heq (Fin.ext h)
          change x.val < c.val
          omega
      · rintro (heq | ⟨hx, hlt⟩)
        · subst x
          exact ⟨hc, by change c.val < (next c).val; omega⟩
        · refine ⟨hx, ?_⟩
          have ht : x.val < c.val := hlt
          change x.val < (next c).val
          omega
    rw [he, Finset.card_insert_of_notMem (by simp), ite_eq_left hc]
  · have he : s.filter (· < next c) = s.filter (· < c) := by
      ext x
      simp only [Finset.mem_filter]
      have hv : (next c).val = c.val + 1 := Nat.mod_eq_of_lt hstep
      constructor
      · rintro ⟨hx, hlt⟩
        have hn : x.val ≠ c.val := fun h => hc ((Fin.ext h) ▸ hx)
        have ht : x.val < (next c).val := hlt
        refine ⟨hx, ?_⟩
        change x.val < c.val
        omega
      · rintro ⟨hx, hlt⟩
        have ht : x.val < c.val := hlt
        refine ⟨hx, ?_⟩
        change x.val < (next c).val
        omega
    simp [he, hc]

/-- A last carrier has all selected carriers before it except possibly itself. -/
theorem rank_last {m : Nat} (s : Finset (Fin m)) (c : Fin m)
    (hstep : c.val + 1 = m) :
    (s.filter (· < c)).card + (if c ∈ s then 1 else 0) = s.card := by
  classical
  by_cases hc : c ∈ s
  · have he : insert c (s.filter (· < c)) = s := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro (rfl | ⟨hx, _⟩)
        · exact hc
        · exact hx
      · intro hx
        by_cases hxc : x = c
        · exact Or.inl hxc
        · right; refine ⟨hx, ?_⟩
          have hn : x.val ≠ c.val := fun h => hxc (Fin.ext h)
          have ht := x.isLt
          change x.val < c.val
          omega
    have hcard := congrArg Finset.card he
    simpa [hc] using hcard
  · have he : s.filter (· < c) = s := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · exact And.left
      · intro hx
        have hn : x.val ≠ c.val := fun h => hc ((Fin.ext h) ▸ hx)
        have ht := x.isLt
        refine ⟨hx, ?_⟩
        change x.val < c.val
        omega
    simp [he, hc]

/-- Compression preserves every old cyclic edge, with a new cyclic step
precisely at the surviving endpoint. -/
theorem compressedBlock_next {m : Nat} (s : Finset (Fin m)) (hs : 0 < s.card)
    (c : Fin m) :
    compressedBlock s hs (next c) =
      if c ∈ s then finRotate s.card (compressedBlock s hs c) else compressedBlock s hs c := by
  classical
  by_cases hstep : c.val + 1 < m
  · have hr := rank_next_of_not_last s c hstep
    by_cases hc : c ∈ s
    · rw [ite_eq_left hc, rotate_is_actual_next]
      apply Fin.ext
      change (s.filter (· < next c)).card % s.card =
        ((s.filter (· < c)).card % s.card + 1) % s.card
      rw [hr, ite_eq_left hc]
      simp [Nat.add_mod]
    · apply Fin.ext
      simp [hc, compressedBlock, hr]
  · have hlast : c.val + 1 = m := by have := c.isLt; omega
    have hn : (next c).val = 0 := by simp [next, hlast]
    have hz : s.filter (· < next c) = ∅ := by
      ext x; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _
      change ¬ x.val < (next c).val
      omega
    have hr := rank_last s c hlast
    by_cases hc : c ∈ s
    · rw [ite_eq_left hc, rotate_is_actual_next]
      apply Fin.ext
      change (s.filter (· < next c)).card % s.card =
        ((s.filter (· < c)).card % s.card + 1) % s.card
      rw [hz]
      simp only [Finset.card_empty, Nat.zero_mod]
      have hrc : (s.filter (· < c)).card + 1 = s.card := by simpa [hc] using hr
      have hlt : (s.filter (· < c)).card < s.card := by omega
      rw [Nat.mod_eq_of_lt hlt, hrc, Nat.mod_self]
    · apply Fin.ext
      have hrc : (s.filter (· < c)).card = s.card := by simpa [hc] using hr
      simp [hc, compressedBlock, hz, hrc]

end CircularElection
