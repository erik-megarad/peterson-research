import Mathlib.Data.List.Count

/-! Arithmetic obstruction in the retained Figure 6, which prints `≤`.
`observations` contains the separately read peer values from one completed
scan; it is not a snapshot of shared memory. This module does not encode a
full execution or claim to prove a corrected algorithm. -/
namespace Peterson.EssentialDekker.LiteralObstruction

def count (level : Nat) (observations : List Nat) : Nat :=
  (observations.filter (fun value => decide (value ≤ level))).length

/-- If each peer observation is at most the level, every peer is counted. -/
theorem count_all (level : Nat) (observations : List Nat)
    (h : ∀ value ∈ observations, value ≤ level) :
    count level observations = observations.length := by
  induction observations with
  | nil => rfl
  | cons value rest ih =>
    have hv : value ≤ level := h value (by simp)
    have hr : ∀ v ∈ rest, v ≤ level := fun v hm => h v (by simp [hm])
    simpa [count, hv] using congrArg Nat.succ (ih hr)

/-- No completed first-level scan can pass while all observed flags are 0/1.
There are n-1 peer reads, regardless of their interleaving with writes. -/
theorem first_level_test_false (n : Nat) (observations : List Nat)
    (hlen : observations.length = n - 1)
    (h : ∀ value ∈ observations, value ≤ 1) :
    ¬ count 1 observations < n - 1 := by
  rw [count_all 1 observations h, hlen]
  exact Nat.lt_irrefl _

/-- The smallest obstruction: a two-process scan of the inactive peer. -/
theorem inactive_peer_test_false : ¬ count 1 [0] < 2 - 1 := by decide

#print axioms count_all
#print axioms first_level_test_false
#print axioms inactive_peer_test_false

end Peterson.EssentialDekker.LiteralObstruction
