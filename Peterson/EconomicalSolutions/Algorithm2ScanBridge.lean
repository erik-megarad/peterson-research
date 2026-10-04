module

public import Std.Tactic

@[expose] public section

/-! Historical QMAX bridge for Algorithm 2, not a tournament safety theorem.
Uniqueness below is a proof obligation on an execution, never a restriction on
its steps. Read times are explicit; no snapshot or fresh-return premise occurs. -/
namespace EconomicalSolutions.Algorithm2.ScanBridge

/-- The source's entire level/Boolean pair is one atomic register. -/
structure Value where
  level : Nat
  flag : Bool
  deriving DecidableEq, Repr

def dead : Value := ⟨0, false⟩

variable {P : Type}

/-- At most one register changes in a global step (stutter is included). -/
def SingleChange (before after : P → Value) : Prop :=
  ∀ i j, before i ≠ after i → before j ≠ after j → i = j

/-- A condition to derive from lower-tree ownership, not an execution premise. -/
def Unique (opponents : List P) (k : Nat) (q : P → Value) : Prop :=
  ∀ i ∈ opponents, ∀ j ∈ opponents,
    k ≤ (q i).level → k ≤ (q j).level → i = j

def Absent (opponents : List P) (k : Nat) (q : P → Value) : Prop :=
  ∀ i ∈ opponents, (q i).level < k

/-- A continuously occupied unique child cannot replace its representative in
one atomic step: removing the old and adding the new would change two registers. -/
theorem representative_survives_step
    {opponents : List P} {k : Nat} {before after : P → Value} {i : P}
    (unique : Unique opponents k before) (atomic : SingleChange before after)
    (member : i ∈ opponents) (active : k ≤ (before i).level)
    (occupied : ∃ j ∈ opponents, k ≤ (after j).level) :
    k ≤ (after i).level := by
  apply Classical.byContradiction
  intro inactive
  obtain ⟨j, hj, high⟩ := occupied
  have changed_i : before i ≠ after i := by
    intro same
    rw [same] at active
    exact inactive active
  have distinct : i ≠ j := by
    intro same
    subst j
    exact inactive high
  have changed_j : before j ≠ after j := by
    intro same
    have old_high : k ≤ (before j).level := by simpa [same] using high
    exact distinct (unique i member j hj active old_high)
  exact distinct (atomic i j changed_i changed_j)

/-- If no absent instant occurs in [start, finish], the representative at start
remains above the threshold at every state of the interval. -/
theorem representative_persists
    {opponents : List P} {k start finish : Nat} {trace : Nat → P → Value}
    (unique : ∀ t, start ≤ t → t ≤ finish → Unique opponents k (trace t))
    (atomic : ∀ t, start ≤ t → t < finish → SingleChange (trace t) (trace (t + 1)))
    (occupied : ∀ t, start ≤ t → t ≤ finish →
      ∃ j ∈ opponents, k ≤ (trace t j).level)
    {i : P} (member : i ∈ opponents) (active : k ≤ (trace start i).level)
    {t : Nat} (lower : start ≤ t) (upper : t ≤ finish) :
    k ≤ (trace t i).level := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le lower
  induction d with
  | zero => simpa using active
  | succ d ih =>
    have bound : start + d ≤ finish := by omega
    have previous := ih (by omega) bound
    exact representative_survives_step
      (unique (start + d) (by omega) bound)
      (atomic (start + d) (by omega) (by omega)) member previous
      (occupied (start + d + 1) (by omega) (by omega))

/-- A completed all-low scan has an absent instant somewhere in its interval.
The per-process reads may be at different times and arbitrarily stale at finish.
Read order is immaterial: this stronger interface even allows unordered times. -/
theorem all_low_scan_has_absent_instant
    {opponents : List P} {k start finish : Nat} {trace : Nat → P → Value}
    (interval : start ≤ finish)
    (unique : ∀ t, start ≤ t → t ≤ finish → Unique opponents k (trace t))
    (atomic : ∀ t, start ≤ t → t < finish → SingleChange (trace t) (trace (t + 1)))
    (observed : ∀ i ∈ opponents, ∃ t, start ≤ t ∧ t ≤ finish ∧
      (trace t i).level < k) :
    ∃ t, start ≤ t ∧ t ≤ finish ∧ Absent opponents k (trace t) := by
  classical
  apply Classical.byContradiction
  intro no_absence
  have occupied : ∀ t, start ≤ t → t ≤ finish →
      ∃ j ∈ opponents, k ≤ (trace t j).level := by
    intro t lo hi
    apply Classical.byContradiction
    intro no_representative
    apply no_absence
    refine ⟨t, lo, hi, ?_⟩
    intro j hj
    have not_high : ¬ k ≤ (trace t j).level := by
      intro high
      exact no_representative ⟨j, hj, high⟩
    omega
  obtain ⟨i, member, active⟩ := occupied start (by omega) interval
  obtain ⟨t, lo, hi, low⟩ := observed i member
  have high := representative_persists unique atomic occupied member active lo hi
  omega

/-- One historical read. The recorded time names the state just before its
atomic read; the register value comes directly from that state. -/
structure Read (P : Type) where
  process : P
  time : Nat

/-- Replay recorded individual samples, stopping at the first sampled >= k.
This is a function on history, not an atomic implementation of QMAX. -/
def qmax (k : Nat) (trace : Nat → P → Value) : List (Read P) → Value
  | [] => dead
  | r :: rs => if k ≤ (trace r.time r.process).level then trace r.time r.process
      else qmax k trace rs

/-- Either every examined sample is low and the result is dead, or the returned
whole pair really occurred at one of the recorded reads. -/
theorem qmax_sample_cases (k : Nat) (trace : Nat → P → Value) (reads : List (Read P)) :
    (qmax k trace reads = dead ∧
      ∀ r ∈ reads, (trace r.time r.process).level < k) ∨
    (∃ r ∈ reads, k ≤ (trace r.time r.process).level ∧
      qmax k trace reads = trace r.time r.process) := by
  induction reads with
  | nil => exact Or.inl ⟨rfl, by simp⟩
  | cons r rs ih =>
    by_cases high : k ≤ (trace r.time r.process).level
    · exact Or.inr ⟨r, by simp, high, by simp [qmax, high]⟩
    · rcases ih with ⟨result, low⟩ | ⟨s, member, active, result⟩
      · left
        refine ⟨by simpa [qmax, high] using result, ?_⟩
        intro s member
        rcases List.mem_cons.mp member with same | tail
        · subst s; omega
        · exact low s tail
      · exact Or.inr ⟨s, by simp [member], active, by simpa [qmax, high] using result⟩

/-- A positive-level dead return means every recorded sample was below k.
This exposes precisely the completion fact the future scan interpreter supplies. -/
theorem qmax_dead_iff_all_low (k : Nat) (positive : 0 < k)
    (trace : Nat → P → Value) (reads : List (Read P)) :
    qmax k trace reads = dead ↔
      ∀ r ∈ reads, (trace r.time r.process).level < k := by
  constructor
  · intro result
    rcases qmax_sample_cases k trace reads with ⟨_, low⟩ | ⟨r, _, high, sampled⟩
    · exact low
    · rw [result] at sampled
      have level := congrArg Value.level sampled
      simp [dead] at level
      omega
  · intro low
    rcases qmax_sample_cases k trace reads with ⟨result, _⟩ | ⟨r, member, high, _⟩
    · exact result
    · have below := low r member
      omega

/-- The virtual opponent value at one instant: dead exactly when no opponent
qualifies, otherwise the qualifying representative's whole visible pair. -/
def Represents (opponents : List P) (k : Nat) (q : P → Value) (v : Value) : Prop :=
  (v = dead ∧ Absent opponents k q) ∨
    ∃ i ∈ opponents, k ≤ (q i).level ∧ v = q i

/-- QMAX replay has a valid historical observation inside its interval.
The actual read prefix must cover every opponent only when the result is dead.
An early qualifying return needs no completion or hypothetical suffix reads.
Uniqueness and single-register evolution are conditional obligations for the
future model; recorded times need not be consecutive or ordered for this lemma. -/
theorem qmax_has_historical_observation
    {opponents : List P} {k start finish : Nat} {trace : Nat → P → Value}
    {reads : List (Read P)} (interval : start ≤ finish)
    (unique : ∀ t, start ≤ t → t ≤ finish → Unique opponents k (trace t))
    (atomic : ∀ t, start ≤ t → t < finish → SingleChange (trace t) (trace (t + 1)))
    (coverage : qmax k trace reads = dead →
      ∀ i ∈ opponents, ∃ r ∈ reads, r.process = i)
    (read_scope : ∀ r ∈ reads, r.process ∈ opponents ∧ start ≤ r.time ∧ r.time ≤ finish) :
    ∃ t, start ≤ t ∧ t ≤ finish ∧
      Represents opponents k (trace t) (qmax k trace reads) := by
  rcases qmax_sample_cases k trace reads with ⟨result, low⟩ | ⟨r, member, high, result⟩
  · have observed : ∀ i ∈ opponents, ∃ t, start ≤ t ∧ t ≤ finish ∧
        (trace t i).level < k := by
      intro i hi
      obtain ⟨r, hr, same⟩ := coverage result i hi
      obtain ⟨_, lo, up⟩ := read_scope r hr
      exact ⟨r.time, lo, up, by simpa [same] using low r hr⟩
    obtain ⟨t, lo, hi, absent⟩ := all_low_scan_has_absent_instant interval unique atomic observed
    exact ⟨t, lo, hi, Or.inl ⟨result, absent⟩⟩
  · obtain ⟨opponent, lo, hi⟩ := read_scope r member
    exact ⟨r.time, lo, hi, Or.inr ⟨r.process, opponent, high, result⟩⟩

end EconomicalSolutions.Algorithm2.ScanBridge

#print axioms EconomicalSolutions.Algorithm2.ScanBridge.representative_persists
#print axioms EconomicalSolutions.Algorithm2.ScanBridge.all_low_scan_has_absent_instant
#print axioms EconomicalSolutions.Algorithm2.ScanBridge.qmax_sample_cases
#print axioms EconomicalSolutions.Algorithm2.ScanBridge.qmax_dead_iff_all_low
#print axioms EconomicalSolutions.Algorithm2.ScanBridge.qmax_has_historical_observation
