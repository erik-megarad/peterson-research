module

public import Peterson.EconomicalSolutions.Algorithm2History

@[expose] public section

/-! Reachable local-state facts for the unchanged Algorithm 2 interpreter.
These facts concern real executions; no representative or scan premise is used. -/
namespace EconomicalSolutions.Algorithm2

/-- The first scan/write still retains the preceding level. Every later
instruction at k has already published k. Cached writes and equal-level wait
samples have exactly that level. -/
def StageWF {n : Nat} (l : Local n) : Prop :=
  match l.pc with
  | .down | .idle => l.q = dead
  | .scan .first k _ => 0 < k ∧ k ≤ height n ∧ l.q.level + 1 = k
  | .write1 k v => 0 < k ∧ k ≤ height n ∧ l.q.level + 1 = k ∧ v.level = k
  | .scan .second k _ | .scan .wait k _ | .self2 k | .pass k =>
      0 < k ∧ k ≤ height n ∧ l.q.level = k
  | .write2 k v | .waitSelf k v =>
      0 < k ∧ k ≤ height n ∧ l.q.level = k ∧ v.level = k
  | .enter | .cs | .release => l.q.level = height n

def LocalWF {n : Nat} (l : Local n) : Prop :=
  l.q.level ≤ height n ∧ (l.q.level = 0 → l.q = dead) ∧ StageWF l

def WellFormed {n : Nat} (s : State n) : Prop := ∀ p, LocalWF (s p)

theorem resume_stageWF {n : Nat} (cfg : Config n) (p : Proc n)
    (c : Continuation) (k : Nat) (q x : Value) (remaining : List (Leaf n))
    (h : StageWF (⟨.scan c k remaining, q⟩ : Local n)) :
    StageWF (⟨resume cfg p c k x, q⟩ : Local n) := by
  cases c <;> simp only [StageWF] at h
  · by_cases eq : x.level = k <;> simp [resume, StageWF, matching, h, eq]
  · by_cases eq : x.level = k
    · simp [resume, eq, StageWF, matching, h]
    · simpa [resume, eq, StageWF] using h
  · by_cases high : k < x.level
    · simpa [resume, high, scan, StageWF] using h
    · by_cases low : x.level < k
      · simpa [resume, high, low, StageWF] using h
      · have eq : x.level = k := by omega
        simpa [resume, high, low, StageWF, eq] using h

theorem ordinary_localWF {n : Nat} (cfg : Config n) (p : Proc n)
    (s : State n) (l : Local n) (wf : LocalWF (s p))
    (step : ordinary cfg p s = some l) : LocalWF l := by
  rcases wf with ⟨bound, zero, stage⟩
  cases pc : (s p).pc with
  | down => simp [ordinary, pc] at step
  | idle =>
    have q : (s p).q = dead := by simpa [StageWF, pc] using stage
    by_cases singleton : height n = 0
    · simp only [ordinary, pc, singleton, ite_true, Option.some.injEq] at step
      subst l
      simp [LocalWF, StageWF, q, singleton, dead, ScanBridge.dead]
    · simp only [ordinary, pc, singleton, ite_false, Option.some.injEq] at step
      subst l
      simp [LocalWF, StageWF, scan, q, dead, ScanBridge.dead]
      omega
  | scan c k remaining =>
    have pre : StageWF (⟨.scan c k remaining, (s p).q⟩ : Local n) := by
      simpa [StageWF, pc] using stage
    cases remaining with
    | nil =>
      simp only [ordinary, pc, Option.some.injEq] at step
      subst l
      exact ⟨bound, zero, resume_stageWF cfg p c k _ dead [] pre⟩
    | cons j rest =>
      by_cases high : k ≤ (visible s j).level
      · simp only [ordinary, pc, high, ite_true, Option.some.injEq] at step
        subst l
        exact ⟨bound, zero, resume_stageWF cfg p c k _ _ (j :: rest) pre⟩
      · simp only [ordinary, pc, high, ite_false, Option.some.injEq] at step
        subst l
        refine ⟨bound, zero, ?_⟩
        cases c <;> simpa [StageWF] using pre
  | write1 k v =>
    have h : 0 < k ∧ k ≤ height n ∧ (s p).q.level + 1 = k ∧ v.level = k := by
      simpa [StageWF, pc] using stage
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp [LocalWF, StageWF, scan, h.2.2.2, h.1.ne', h.1, h.2.1]
  | self2 k =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    refine ⟨bound, zero, ?_⟩
    simpa [StageWF, pc] using stage
  | write2 k v =>
    have h : 0 < k ∧ k ≤ height n ∧ (s p).q.level = k ∧ v.level = k := by
      simpa [StageWF, pc] using stage
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp [LocalWF, StageWF, scan, h.2.2.2, h.1.ne', h.1, h.2.1]
  | waitSelf k x =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    refine ⟨bound, zero, ?_⟩
    have h : 0 < k ∧ k ≤ height n ∧ (s p).q.level = k ∧ x.level = k := by
      simpa [StageWF, pc] using stage
    split <;> simp [StageWF, scan, h]
  | pass k =>
    have h : 0 < k ∧ k ≤ height n ∧ (s p).q.level = k := by
      simpa [StageWF, pc] using stage
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    refine ⟨bound, zero, ?_⟩
    split
    · simp [StageWF, scan, h.2.2]; omega
    · simp only [StageWF]; omega
  | enter =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    exact ⟨bound, zero, by simpa [StageWF, pc] using stage⟩
  | cs =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    exact ⟨bound, zero, by simpa [StageWF, pc] using stage⟩
  | release =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp [LocalWF, StageWF, dead, ScanBridge.dead]

theorem next_wellFormed {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    (wf : WellFormed s) (step : next cfg s c = some t) : WellFormed t := by
  have replace (p : Proc n) (l : Local n) (hl : LocalWF l) :
      WellFormed (setLocal s p l) := by
    intro q
    by_cases eq : q = p
    · simpa [setLocal, eq] using hl
    · simpa [setLocal, eq] using wf q
  cases c with
  | stutter =>
    have ht : s = t := Option.some.inj step
    exact ht ▸ wf
  | run p =>
    simp only [next] at step
    cases h : ordinary cfg p s with
    | none => simp [h] at step
    | some l =>
      have ht : t = setLocal s p l := by simpa [h] using step.symm
      rw [ht]
      exact replace p l (ordinary_localWF cfg p s l (wf p) h)
  | fail p =>
    simp only [next] at step
    split at step
    · simp at step
    · have ht := Option.some.inj step
      rw [← ht]
      apply replace
      simp [LocalWF, StageWF, dead, ScanBridge.dead]
  | restart p =>
    simp only [next] at step
    split at step
    · have ht := Option.some.inj step
      rw [← ht]
      apply replace
      simp [LocalWF, StageWF, dead, ScanBridge.dead]
    · simp at step

theorem reachable_wellFormed {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) : WellFormed s := by
  induction reach with
  | initial => intro p; simp [initial, LocalWF, StageWF, dead, ScanBridge.dead]
  | step _ edge ih =>
    obtain ⟨c, hc, _⟩ := edge
    exact next_wellFormed ih hc

/-- Number of levels concretely passed in the current request. In particular,
first-scan delay at k+1 already retains k; this is independent of publication. -/
def passedLevel {n : Nat} (l : Local n) : Nat :=
  match l.pc with
  | .down | .idle => 0
  | .scan _ k _ | .write1 k _ | .self2 k | .write2 k _ | .waitSelf k _ => k - 1
  | .pass k => k
  | .enter | .cs | .release => height n

/-- Register level and concrete progress differ by at most one. This supplies
lower-child qualification even before the next first publication. -/
theorem localWF_levels {n : Nat} {l : Local n} (wf : LocalWF l) :
    passedLevel l ≤ l.q.level ∧ l.q.level ≤ passedLevel l + 1 := by
  rcases wf with ⟨_, _, stage⟩
  cases h : l.pc <;> simp only [passedLevel, h, StageWF] at *
  case scan c k rest => cases c <;> dsimp at stage <;> omega
  all_goals first | omega | (simp_all [dead, ScanBridge.dead])

/-- Only the release instruction may lower the executing owner's published
level or relinquish a concretely passed node. Failure is handled by next. -/
theorem ordinary_monotone {n : Nat} (cfg : Config n) (p : Proc n)
    (s : State n) (l : Local n) (wf : LocalWF (s p))
    (step : ordinary cfg p s = some l) (notRelease : (s p).pc ≠ .release) :
    (s p).q.level ≤ l.q.level ∧ passedLevel (s p) ≤ passedLevel l := by
  rcases wf with ⟨bound, zero, stage⟩
  have resume_progress (c : Continuation) (k : Nat) (x : Value) :
      k - 1 ≤ passedLevel (⟨resume cfg p c k x, (s p).q⟩ : Local n) := by
    cases c <;> simp only [resume]
    · simp [passedLevel]
    · split <;> simp [passedLevel]
    · split
      · simp [passedLevel, scan]
      · split <;> simp [passedLevel]
  cases pc : (s p).pc with
  | down => simp [ordinary, pc] at step
  | release => exact (notRelease pc).elim
  | idle =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp only [passedLevel, pc]
    exact ⟨by omega, Nat.zero_le _⟩
  | scan c k remaining =>
    cases remaining with
    | nil =>
      simp only [ordinary, pc, Option.some.injEq] at step
      subst l
      exact ⟨by rfl, by simpa [passedLevel, pc] using resume_progress c k dead⟩
    | cons j rest =>
      by_cases high : k ≤ (visible s j).level
      · simp only [ordinary, pc, high, ite_true, Option.some.injEq] at step
        subst l
        exact ⟨by rfl, by simpa [passedLevel, pc] using resume_progress c k (visible s j)⟩
      · simp only [ordinary, pc, high, ite_false, Option.some.injEq] at step
        subst l
        simp [passedLevel, pc]
  | write1 k v =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp only [StageWF, pc] at stage
    simp only [passedLevel, scan, pc]
    omega
  | self2 k =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp [passedLevel, pc]
  | write2 k v =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp only [StageWF, pc] at stage
    simp only [passedLevel, scan, pc]
    omega
  | waitSelf k x =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    constructor
    · rfl
    · by_cases waiting : (Bool.xor (bit p.val k) (x == (s p).q)) = true <;>
        simp [waiting, passedLevel, pc, scan]
  | pass k =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp only [StageWF, pc] at stage
    constructor
    · rfl
    · by_cases more : k < height n <;> simp [more, passedLevel, pc, scan]; omega
  | enter =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp [passedLevel, pc]
  | cs =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp [passedLevel, pc]

/-- Exact concrete events that end the owner's retained gates. -/
def Resets {n : Nat} (s : State n) (c : Command n) (p : Proc n) : Prop :=
  c = .fail p ∨ (c = .run p ∧ (s p).pc = .release)

theorem next_retains_levels {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} (p : Proc n) (wf : WellFormed s)
    (step : next cfg s c = some t) (noReset : ¬ Resets s c p) :
    (s p).q.level ≤ (t p).q.level ∧ passedLevel (s p) ≤ passedLevel (t p) := by
  have unchanged (h : t p = s p) :
      (s p).q.level ≤ (t p).q.level ∧ passedLevel (s p) ≤ passedLevel (t p) := by
    rw [h]; exact ⟨le_refl _, le_refl _⟩
  cases c with
  | stutter => exact unchanged (congrFun (Option.some.inj step.symm) p)
  | run actor =>
    simp only [next] at step
    cases h : ordinary cfg actor s with
    | none => simp [h] at step
    | some l =>
      have ht : t = setLocal s actor l := by simpa [h] using step.symm
      by_cases same : actor = p
      · subst actor
        have nr : (s p).pc ≠ .release := by simpa [Resets] using noReset
        simpa [ht, setLocal] using ordinary_monotone cfg p s l (wf p) h nr
      · exact unchanged (by simp [ht, setLocal, Ne.symm same])
  | fail actor =>
    have different : actor ≠ p := by intro eq; subst actor; simp [Resets] at noReset
    simp only [next] at step
    split at step
    · simp at step
    · exact unchanged (by simp [← Option.some.inj step, setLocal, Ne.symm different])
  | restart actor =>
    simp only [next] at step
    split at step
    · rename_i down
      by_cases same : actor = p
      · subst actor
        have q : (s p).q = dead := by simpa [StageWF, down] using (wf p).2.2
        simp [← Option.some.inj step, setLocal, q, passedLevel, down]
      · exact unchanged (by simp [← Option.some.inj step, setLocal, Ne.symm same])
    · simp at step

/-- Every nonreset finite interval retains all passed lower gates, while own
higher-level writes and other processes' arbitrary failures remain allowed. -/
theorem interval_retains_levels {n : Nat} {cfg : Config n}
    (trace : Nat → State n) (commands : Nat → Command n) (p : Proc n)
    (start finish : Nat) (ordered : start ≤ finish)
    (wf : ∀ t, start ≤ t → t ≤ finish → WellFormed (trace t))
    (valid : ∀ t, start ≤ t → t < finish →
      next cfg (trace t) (commands t) = some (trace (t + 1)))
    (noReset : ∀ t, start ≤ t → t < finish → ¬ Resets (trace t) (commands t) p) :
    (trace start p).q.level ≤ (trace finish p).q.level ∧
      passedLevel (trace start p) ≤ passedLevel (trace finish p) := by
  induction finish, ordered using Nat.le_induction with
  | base => exact ⟨le_refl _, le_refl _⟩
  | succ finish bound ih =>
    have before := ih (fun t ht hu => wf t ht (by omega))
      (fun t ht hu => valid t ht (by omega))
      (fun t ht hu => noReset t ht (by omega))
    have edge := next_retains_levels p (wf finish bound (by omega))
      (valid finish bound (by omega)) (noReset finish bound (by omega))
    exact ⟨before.1.trans edge.1, before.2.trans edge.2⟩

theorem prefix_reachable {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish : Nat}
    (start : trace 0 = initial n) (valid : ValidPrefix cfg trace commands finish) :
    ∀ time, time ≤ finish → Reachable cfg (trace time) := by
  intro time
  induction time with
  | zero => intro _; rw [start]; exact .initial
  | succ time ih =>
    intro bound
    exact .step (ih (by omega)) ⟨commands time, valid time (by omega), rfl⟩

/-- All well-formedness premises of interval retention are discharged directly
from a finite initial execution, with no fairness or peer-failure premise. -/
theorem concrete_interval_retains_levels {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} (p : Proc n)
    (start finish : Nat) (ordered : start ≤ finish)
    (initially : trace 0 = initial n) (valid : ValidPrefix cfg trace commands finish)
    (noReset : ∀ t, start ≤ t → t < finish → ¬ Resets (trace t) (commands t) p) :
    (trace start p).q.level ≤ (trace finish p).q.level ∧
      passedLevel (trace start p) ≤ passedLevel (trace finish p) :=
  interval_retains_levels trace commands p start finish ordered
    (fun t _ ht => reachable_wellFormed (prefix_reachable initially valid t ht))
    (fun t _ ht => valid t ht) noReset

/-- Both equal-level premises required by the node's whole-pair wait comparison
now follow from actual reachability, rather than being user-supplied facts. -/
theorem reachable_waitSelf_levels {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) (p : Proc n) (k : Nat) (x : Value)
    (pc : (s p).pc = .waitSelf k x) : (s p).q.level = k ∧ x.level = k := by
  have h := (reachable_wellFormed reach p).2.2
  simp only [StageWF, pc] at h
  exact h.2.2

/-- Concrete critical occupancy has passed the root. Connecting this fact to
one retained abstract root winner still requires the concrete refinement. -/
theorem critical_root_passed {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) (p : Proc n) (cs : (s p).pc = .cs) :
    passedLevel (s p) = height n ∧ (s p).q.level = height n := by
  have h := (reachable_wellFormed reach p).2.2
  exact ⟨by simp [passedLevel, cs], by simpa [StageWF, cs] using h⟩

/-- Even a representative still scanning before its next write has already
concretely passed the child node and retains that child's published level. -/
theorem first_scan_retains_child {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) (p : Proc n) (k : Nat) (remaining : List (Leaf n))
    (pc : (s p).pc = .scan .first (k + 1) remaining) :
    passedLevel (s p) = k ∧ (s p).q.level = k := by
  have h := (reachable_wellFormed reach p).2.2
  simp only [StageWF, pc] at h
  exact ⟨by simp [passedLevel, pc], by omega⟩

/-- This explicitly closes the zero-height safety specialization, independently
of any tournament induction. -/
theorem singleton_mutualExclusion (s : State 1) : MutualExclusion s := by
  intro p q _ _
  exact Fin.ext (by omega)

end EconomicalSolutions.Algorithm2

#print axioms EconomicalSolutions.Algorithm2.reachable_wellFormed

#print axioms EconomicalSolutions.Algorithm2.next_retains_levels
#print axioms EconomicalSolutions.Algorithm2.interval_retains_levels
#print axioms EconomicalSolutions.Algorithm2.singleton_mutualExclusion

#print axioms EconomicalSolutions.Algorithm2.concrete_interval_retains_levels
#print axioms EconomicalSolutions.Algorithm2.reachable_waitSelf_levels
#print axioms EconomicalSolutions.Algorithm2.critical_root_passed
#print axioms EconomicalSolutions.Algorithm2.first_scan_retains_child
