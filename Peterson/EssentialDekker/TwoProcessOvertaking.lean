import Peterson.EssentialDekker.TwoProcessProgressProof
import Mathlib.Tactic.IntervalCases

/-! Explicit Figure 4 witnesses: a clearing stem, any number of completed peer
passages, the requester's completion, then idle stuttering. -/
namespace Peterson.EssentialDekker.TwoProcess.Overtaking
open Progress

def stem : Nat → State
  | 0 => ⟨.idle, .idle, false, false, true⟩
  | 1 => ⟨.readTurn, .idle, false, false, true⟩
  | 2 => ⟨.readPeer, .idle, false, false, true⟩
  | 3 => ⟨.writeTrue, .idle, false, false, true⟩
  | 4 => ⟨.guardSelf, .idle, true, false, true⟩
  | 5 => ⟨.guardSelf, .readTurn, true, false, true⟩
  | 6 => ⟨.guardSelf, .writeTrue, true, false, true⟩
  | 7 => ⟨.guardSelf, .guardSelf, true, true, true⟩
  | 8 => ⟨.guardPeer, .guardSelf, true, true, true⟩
  | 9 => ⟨.readTurn, .guardSelf, true, true, true⟩
  | 10 => ⟨.readPeer, .guardSelf, true, true, true⟩
  | 11 => ⟨.writeFalse, .guardSelf, true, true, true⟩
  | 12 => ⟨.guardSelf, .guardSelf, false, true, true⟩
  | 13 => ⟨.guardSelf, .guardPeer, false, true, true⟩
  | 14 => ⟨.guardSelf, .critical, false, true, true⟩
  | 15 => ⟨.guardSelf, .writeTurn, false, true, true⟩
  | 16 => ⟨.guardSelf, .clearFlag, false, true, false⟩
  | _ => ⟨.guardSelf, .idle, false, false, false⟩

def lap : Nat → State
  | 0 => ⟨.guardSelf, .idle, false, false, false⟩
  | 1 => ⟨.guardSelf, .readTurn, false, false, false⟩
  | 2 => ⟨.guardSelf, .readPeer, false, false, false⟩
  | 3 => ⟨.guardSelf, .writeTrue, false, false, false⟩
  | 4 => ⟨.guardSelf, .guardSelf, false, true, false⟩
  | 5 => ⟨.guardSelf, .guardPeer, false, true, false⟩
  | 6 => ⟨.guardSelf, .critical, false, true, false⟩
  | 7 => ⟨.guardSelf, .writeTurn, false, true, false⟩
  | 8 => ⟨.guardSelf, .clearFlag, false, true, false⟩
  | _ => ⟨.guardSelf, .idle, false, false, false⟩

def finish : Nat → State
  | 0 => ⟨.guardSelf, .idle, false, false, false⟩
  | 1 => ⟨.readTurn, .idle, false, false, false⟩
  | 2 => ⟨.writeTrue, .idle, false, false, false⟩
  | 3 => ⟨.guardSelf, .idle, true, false, false⟩
  | 4 => ⟨.guardPeer, .idle, true, false, false⟩
  | 5 => ⟨.critical, .idle, true, false, false⟩
  | 6 => ⟨.writeTurn, .idle, true, false, false⟩
  | 7 => ⟨.clearFlag, .idle, true, false, true⟩
  | _ => ⟨.idle, .idle, false, false, true⟩

def stemActor (n : Nat) : Proc :=
  if n < 4 ∨ (7 ≤ n ∧ n < 12) then false else true

def witness (k : Nat) : Execution where
  state n := if n < 17 then stem n else
    if n < 17 + 9*k then lap ((n-17)%9) else finish (n-(17+9*k))
  event n := if n < 17 then some (stemActor n) else
    if n < 17 + 9*k then some true else
      if n < 25 + 9*k then some false else none

theorem stem_step (n : Nat) (h : n < 17) :
    stem (n+1) = next (stem n) (stemActor n) := by
  interval_cases n <;> decide

theorem lap_step (n : Nat) (h : n < 9) :
    lap ((n+1)%9) = next (lap n) true := by
  interval_cases n <;> decide

theorem finish_step (n : Nat) (h : n < 8) :
    finish (n+1) = next (finish n) false := by
  interval_cases n <;> decide

theorem finish_idle (n : Nat) (h : 8 ≤ n) : finish n = finish 8 := by
  unfold finish
  split <;> first | rfl | omega

theorem witness_valid (k : Nat) : Valid (witness k) := by
  refine ⟨⟨true, rfl⟩, ?_⟩
  intro n
  change (if n+1 < 17 then _ else _) = _
  by_cases hs : n < 17
  · by_cases hb : n+1 < 17
    · simpa [witness, hs, hb] using stem_step n hs
    · have hn : n = 16 := by omega
      subst n
      by_cases hk : k = 0
      · subst k; decide
      · simp [witness, show 17 < 17+9*k by omega, stemActor, stem, lap, next,
          State.pc, State.setPC, State.setFlag]
  · by_cases hl : n < 17+9*k
    · have hm : (n-17)%9 < 9 := Nat.mod_lt _ (by decide)
      have hmod : (n+1-17)%9 = ((n-17)%9+1)%9 := by omega
      by_cases hb : n+1 < 17+9*k
      · simp only [witness, ite_eq_right hs, ite_eq_left hl,
          ite_eq_right (show ¬ n+1 < 17 by omega), ite_eq_left hb]
        rw [hmod]
        exact lap_step ((n-17)%9) hm
      · have hn : n+1 = 17+9*k := by omega
        have hm8 : (n-17)%9 = 8 := by omega
        simp [witness, hs, hl, hn, hm8,
          lap, finish, next, State.pc, State.setPC, State.setFlag]
    · by_cases hf : n < 25+9*k
      · have hd : n-(17+9*k) < 8 := by omega
        have he : n+1-(17+9*k) = n-(17+9*k)+1 := by omega
        simpa [witness, hs, hl, hf, show ¬ n+1 < 17 by omega,
          show ¬ n+1 < 17+9*k by omega, he] using finish_step _ hd
      · simp only [witness, ite_eq_right hs, ite_eq_right hl, ite_eq_right hf,
          ite_eq_right (show ¬ n+1 < 17 by omega),
          ite_eq_right (show ¬ n+1 < 17+9*k by omega)]
        exact (finish_idle _ (by omega)).trans (finish_idle _ (by omega)).symm

/-- Both clients have finished by this time; later slots stutter. -/
theorem idle_suffix (k n : Nat) (hn : 25+9*k ≤ n) (p : Proc) :
    ((witness k).state n).pc p = .idle := by
  simp only [witness, ite_eq_right (show ¬ n < 17 by omega),
    ite_eq_right (show ¬ n < 17+9*k by omega)]
  rw [finish_idle _ (by omega)]
  cases p <;> rfl

theorem witness_fair (k : Nat) : WeakProtocolFair (witness k) := by
  intro p n h
  have hi := (h (n+25+9*k) (by omega)).1
  exact False.elim (hi (idle_suffix k _ (by omega) p))

/-- In a valid execution, a critical actor can leave its critical location
only by its actual completion step. An idle suffix therefore ensures completion. -/
theorem witness_completes (k : Nat) : CriticalCompletes (witness k) := by
  intro p n hn
  by_contra hno
  have hpersist : ∀ m, n ≤ m → ((witness k).state m).pc p = .critical := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hn
    | succ m hm ih =>
      have he : (witness k).event m ≠ some p := by
        intro he
        exact hno ⟨m, hm, ih, he⟩
      exact (pc_succ_unselected (witness_valid k) he).trans ih
  have hc := hpersist (n+25+9*k) (by omega)
  rw [idle_suffix k _ (by omega) p] at hc
  cases hc

theorem request_at_zero (k : Nat) : Request (witness k) false 0 := by
  simp [Request, witness, stem, stemActor, State.pc]

theorem matching_entry (k : Nat) : Entry (witness k) false (21+9*k) := by
  have hs : ¬ 21+9*k < 17 := by omega
  have hl : ¬ 21+9*k < 17+9*k := by omega
  have hf : 21+9*k < 25+9*k := by omega
  have hd : 21+9*k-(17+9*k) = 4 := by omega
  simp [Entry, witness, hs, hl, hf, hd, finish, State.pc, State.flag]

theorem pending_interval (k n : Nat) (hn : 0 < n) (he : n ≤ 21+9*k) :
    Pending ((witness k).state n) false := by
  by_cases hs : n < 17
  · simp only [witness, ite_eq_left hs]
    interval_cases n <;> simp [Pending, stem, State.pc]
  · by_cases hl : n < 17+9*k
    · simp only [witness, ite_eq_right hs, ite_eq_left hl]
      have hm : (n-17)%9 < 9 := Nat.mod_lt _ (by decide)
      generalize (n-17)%9 = r at *
      interval_cases r <;> simp [Pending, lap, State.pc]
    · simp only [witness, ite_eq_right hs, ite_eq_right hl]
      have hd : n-(17+9*k) ≤ 4 := by omega
      generalize n-(17+9*k) = r at *
      interval_cases r <;> simp [Pending, finish, State.pc]

/-- The request explicitly executes the loop's false write in slot 11. -/
theorem clears_in_loop (k : Nat) :
    ((witness k).state 11).pc false = .writeFalse ∧
    ((witness k).state 11).flag false = true ∧
    (witness k).event 11 = some false ∧
    ((witness k).state 12).flag false = false := by
  simp [witness, stem, stemActor, State.pc, State.flag]

/-- Each indexed lap contains a distinct peer entry and a completed exit. -/
theorem peer_lap (k i : Nat) (hi : i < k) :
    Entry (witness k) true (22+9*i) ∧
    ((witness k).state (26+9*i)).pc true = .idle := by
  have hs : ¬ 22+9*i < 17 := by omega
  have hl : 22+9*i < 17+9*k := by omega
  have hd : (22+9*i-17)%9 = 5 := by omega
  constructor
  · simp [Entry, witness, hs, hl, hd, lap, State.pc, State.flag]
  · have hs' : ¬ 26+9*i < 17 := by omega
    by_cases hl' : 26+9*i < 17+9*k
    · have hd' : (26+9*i-17)%9 = 0 := by omega
      simp [witness, hs', hl', hd', lap, State.pc]
    · have hd' : 26+9*i-(17+9*k) = 0 := by omega
      simp [witness, hs', hl', hd', finish, State.pc]

/-- The loop-cleared flag remains false throughout all k completed peer laps. -/
theorem flag_clear_interval (k n : Nat) (hn : 12 ≤ n) (he : n ≤ 17+9*k) :
    ((witness k).state n).flag false = false := by
  by_cases hs : n < 17
  · simp only [witness, ite_eq_left hs]
    interval_cases n <;> decide
  · by_cases hl : n < 17+9*k
    · simp only [witness, ite_eq_right hs, ite_eq_left hl]
      have hm : (n-17)%9 < 9 := Nat.mod_lt _ (by decide)
      generalize (n-17)%9 = r at *
      interval_cases r <;> decide
    · have hd : n-(17+9*k) = 0 := by omega
      simp [witness, hs, hl, hd, finish, State.flag]

/-- For every finite count there is an initialized, fair infinite execution
with that many ordered distinct peer entries during the same private request.
The request clears its flag in its loop, eventually enters, and both clients
complete. The indexed peer passages themselves finish before that entry. -/
theorem arbitrary_finite_overtaking (k : Nat) :
    ∃ E : Execution, Valid E ∧ WeakProtocolFair E ∧ CriticalCompletes E ∧
      Request E false 0 ∧ Entry E false (21+9*k) ∧
      (∀ n, 0 < n → n ≤ 21+9*k → Pending (E.state n) false) ∧
      (E.state 11).pc false = .writeFalse ∧ (E.state 11).flag false = true ∧
      E.event 11 = some false ∧
      (∀ n, 12 ≤ n → n ≤ 17+9*k → (E.state n).flag false = false) ∧
      ∃ slots : Fin k → Nat, StrictMono slots ∧
        ∀ i, 12 < slots i ∧ slots i < 21+9*k ∧ Entry E true (slots i) ∧
          (E.state (slots i+4)).pc true = .idle ∧ slots i+4 < 21+9*k := by
  refine ⟨witness k, witness_valid k, witness_fair k, witness_completes k,
    request_at_zero k, matching_entry k, pending_interval k,
    (clears_in_loop k).1, (clears_in_loop k).2.1,
    (clears_in_loop k).2.2.1, flag_clear_interval k,
    (fun i => 22+9*i.val), ?_, ?_⟩
  · intro i j hij
    change i.val < j.val at hij
    dsimp
    omega
  · intro i
    dsimp
    have hi := i.isLt
    obtain ⟨he, hc⟩ := peer_lap k i.val hi
    refine ⟨by omega, by omega, he, ?_, by omega⟩
    simpa only [show 22+9*i.val+4 = 26+9*i.val by omega] using hc

end Peterson.EssentialDekker.TwoProcess.Overtaking

#print axioms Peterson.EssentialDekker.TwoProcess.Overtaking.arbitrary_finite_overtaking
