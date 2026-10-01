import Peterson.EconomicalSolutions.Algorithm2Solo
import Peterson.EconomicalSolutions.Algorithm2Tree

/-! Exact counts for arbitrary complete scan orders, including padded leaves. -/
namespace EconomicalSolutions.Algorithm2.Solo

variable {n : Nat}

/-- At level k+1 the opposite child is a contiguous block of width 2^k. -/
theorem opponent_quotient (i j k : Nat) :
    Opponent i j (k + 1) ↔
      j / 2 ^ k = 2 * (i / 2 ^ (k + 1)) + (if bit i (k + 1) then 0 else 1) := by
  have own : Child (i / 2 ^ (k + 1)) (k + 1) (bit i (k + 1)) i :=
    (child_iff _ _ _ _ (by omega)).mpr ⟨rfl, rfl⟩
  rw [opponent_child (by omega) own]
  cases bit i (k + 1) <;> simp [Child]

/-- Both children of every visited node fit within the minimal padded tree. -/
theorem opponent_block_bound (p : Proc n) (k : Nat) (hk : k < height n) :
    (2 * (p.val / 2 ^ (k + 1)) + (if bit p.val (k + 1) then 0 else 1) + 1) * 2 ^ k
      ≤ capacity n := by
  have factor : 2 ^ (height n - (k + 1)) * 2 ^ (k + 1) = capacity n := by
    rw [← Nat.pow_add, capacity]
    congr 1
    omega
  have small : p.val < capacity n := lt_of_lt_of_le p.isLt (real_fits_padding n)
  have parent : p.val / 2 ^ (k + 1) < 2 ^ (height n - (k + 1)) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rwa [factor]
  have children : 2 * (p.val / 2 ^ (k + 1)) + (if bit p.val (k + 1) then 0 else 1) + 1
      ≤ 2 * 2 ^ (height n - (k + 1)) := by
    split <;> omega
  calc
    _ ≤ (2 * 2 ^ (height n - (k + 1))) * 2 ^ k := Nat.mul_le_mul_right _ children
    _ = capacity n := by rw [Nat.mul_comm 2, Nat.mul_assoc, Nat.mul_comm 2, ← Nat.pow_succ, factor]

/-- Completeness and no duplicates fix length independently of enumeration. -/
theorem order_length (cfg : Config n) (p : Proc n) (k : Nat) (hk : k < height n) :
    (cfg.order p (k + 1)).length = 2 ^ k := by
  let child := 2 * (p.val / 2 ^ (k + 1)) + (if bit p.val (k + 1) then 0 else 1)
  let width := 2 ^ k
  have pos : 0 < width := Nat.two_pow_pos k
  have bound : (child + 1) * width ≤ capacity n := opponent_block_bound p k hk
  have nodup : ((cfg.order p (k + 1)).map Fin.val).Nodup :=
    (List.nodup_map_iff Fin.val_injective).mpr (cfg.nodup p (k + 1))
  have perm : List.Perm ((cfg.order p (k + 1)).map Fin.val) (List.range' (child * width) width) := by
    apply (List.perm_ext_iff_of_nodup nodup (List.nodup_range')).mpr
    intro j
    simp only [List.mem_map, List.mem_range'_1]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have quot : a.val / width = child :=
        (opponent_quotient p.val a.val k).mp ((cfg.complete p (k + 1) a).mp ha)
      have interval := (Nat.div_eq_iff pos).mp quot
      omega
    · intro interval
      have small : j < capacity n := by
        have : child * width + width = (child + 1) * width := by simp [Nat.add_mul]
        omega
      let a : Leaf n := ⟨j, small⟩
      refine ⟨a, (cfg.complete p (k + 1) a).mpr ?_, rfl⟩
      apply (opponent_quotient p.val a.val k).mpr
      apply (Nat.div_eq_iff pos).mpr
      dsimp [a]
      change child * width ≤ j ∧ j ≤ child * width + width - 1
      omega
  have := perm.length_eq
  simpa [width] using this

/-- The sum of one scan's lengths across the positive levels. -/
def scanTotal (cfg : Config n) (p : Proc n) : Nat → Nat
  | 0 => 0
  | k + 1 => scanTotal cfg p k + (cfg.order p (k + 1)).length

theorem scanTotal_exact (cfg : Config n) (p : Proc n) (k : Nat) (hk : k ≤ height n) :
    scanTotal cfg p k + 1 = 2 ^ k := by
  induction k with
  | zero => simp [scanTotal]
  | succ k ih =>
    have prev := ih (by omega)
    rw [scanTotal, order_length cfg p k (by omega), Nat.pow_succ]
    omega

theorem work_scanTotal (cfg : Config n) (p : Proc n) (k : Nat) :
    work cfg p k = 3 * scanTotal cfg p k + 7 * k := by
  induction k with
  | zero => simp [work, scanTotal]
  | succ k ih => simp only [work, scanTotal, ih]; omega

/-- Includes request and entry as two additional interpreter instructions. -/
def count (n : Nat) : Nat := 3 * 2 ^ height n + 7 * height n - 1

theorem work_count (cfg : Config n) (p : Proc n) :
    work cfg p (height n) + 2 = count n := by
  have := scanTotal_exact cfg p (height n) (by rfl)
  rw [work_scanTotal]
  unfold count
  omega

theorem count_singleton : count 1 = 2 := by simp [count, singleton_height]

/-- Minimal padding is less than twice a positive population. -/
theorem capacity_lt_twice (n : Nat) (positive : 0 < n) : capacity n < 2 * n := by
  by_cases singleton : n = 1
  · subst n; simp [capacity, singleton_height]
  · have large : 1 < n := by omega
    have hpos : 0 < height n := Nat.clog_pos (by decide) large
    have pred : 2 ^ (height n - 1) < n := Nat.pow_pred_clog_lt_self (by decide) large
    have pow : 2 ^ height n = 2 ^ (height n - 1) * 2 := by
      rw [← Nat.pow_succ]; congr 1; omega
    rw [capacity, pow]
    omega

theorem count_linear (n : Nat) (positive : 0 < n) : count n ≤ 13 * n := by
  have pad := capacity_lt_twice n positive
  have heightBound : height n ≤ n := (height_le_iff n n).mpr (Nat.le_of_lt Nat.lt_two_pow_self)
  unfold count
  unfold capacity at pad
  omega

/-- One request, all counted local instructions, and one entry. -/
def labels (cfg : Config n) (p : Proc n) : List (Label n) :=
  .request p :: (List.replicate (work cfg p (height n)) (.instruction p) ++ [.entry p])

theorem labels_length (cfg : Config n) (p : Proc n) : (labels cfg p).length = count n := by
  simpa [labels, Nat.add_assoc] using work_count cfg p

theorem labels_get (cfg : Config n) (p : Proc n) (i : Nat) (hi : i < (labels cfg p).length) :
    (labels cfg p)[i] =
      if i = 0 then .request p else if i + 1 = count n then .entry p else .instruction p := by
  have size := work_count cfg p
  have bound : i < work cfg p (height n) + 2 := by simpa [labels, Nat.add_assoc] using hi
  cases i with
  | zero => simp [labels]
  | succ i =>
    by_cases h : i < work cfg p (height n)
    · have last : ¬ i + 1 + 1 = count n := by omega
      simp [labels, h, last]
    · have eq : i = work cfg p (height n) := by omega
      subst i
      simp [labels, ← size, Nat.add_assoc]

/-- Actual initialized execution reaches cs at the exact count, with successful
run commands, the expected labels and no critical state at any earlier index. -/
theorem initialized_first_entry (cfg : Config n) (p : Proc n) :
    execute cfg p (initial n) 0 = initial n ∧
    (execute cfg p (initial n) (count n) p).pc = .cs ∧
    (∀ i < count n,
      next cfg (execute cfg p (initial n) i) (.run p) =
        some (execute cfg p (initial n) (i + 1)) ∧
      (execute cfg p (initial n) i p).pc ≠ .cs ∧
      label (execute cfg p (initial n) i) (.run p) =
        if i = 0 then .request p else if i + 1 = count n then .entry p else .instruction p) ∧
    (∀ i (q : Proc n), q ≠ p → execute cfg p (initial n) i q = ⟨.idle, dead⟩) ∧
    count n ≤ 13 * n := by
  have path := initialized_path cfg p
  have checked := path_execution path
  change execute cfg p (initial n) (labels cfg p).length = _ ∧ _ at checked
  have finish := checked.1
  rw [labels_length] at finish
  refine ⟨rfl, ?_, ?_, ?_, count_linear n cfg.positive⟩
  · rw [finish]
    simp
  · intro i hi
    have bound : i < (labels cfg p).length := by rwa [labels_length]
    have step := checked.2 i bound
    exact ⟨step.1, step.2.2, step.2.1.trans (labels_get cfg p i bound)⟩
  · intro i q different
    exact execute_peer cfg p q different i

/-- The original LTS has the same exact labelled finite execution. -/
theorem initialized_lts (cfg : Config n) (p : Proc n) :
    (lts cfg).MTr (initial n) (labels cfg p)
      (execute cfg p (initial n) (count n)) ∧ (labels cfg p).length = count n := by
  have path := initialized_path cfg p
  have finish := (path_execution path).1
  change execute cfg p (initial n) (labels cfg p).length = _ at finish
  rw [labels_length] at finish
  exact ⟨finish.symm ▸ path_lts path, labels_length cfg p⟩

end EconomicalSolutions.Algorithm2.Solo

#print axioms EconomicalSolutions.Algorithm2.Solo.order_length
#print axioms EconomicalSolutions.Algorithm2.Solo.scanTotal_exact
#print axioms EconomicalSolutions.Algorithm2.Solo.work_scanTotal
#print axioms EconomicalSolutions.Algorithm2.Solo.work_count
#print axioms EconomicalSolutions.Algorithm2.Solo.count_singleton
#print axioms EconomicalSolutions.Algorithm2.Solo.count_linear
#print axioms EconomicalSolutions.Algorithm2.Solo.initialized_first_entry
#print axioms EconomicalSolutions.Algorithm2.Solo.initialized_lts
