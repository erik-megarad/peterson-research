module

public import Peterson.EconomicalSolutions.Algorithm2WellFormed
public import Peterson.EconomicalSolutions.Algorithm2NodeSafety

@[expose] public section

/-! Extract open invocation boundaries and their possible observation points
from concrete prefixes. No completed-scan or observation-support premise is
added to the concrete execution. -/
namespace EconomicalSolutions.Algorithm2

/-- An invocation is still open at time `now`; its start is an actual full
scan, and neither a return nor an owner failure has been crossed. -/
structure OpenScan {n : Nat} (cfg : Config n) (trace : Nat → State n)
    (commands : Nat → Command n) (p : Proc n) (c : Continuation) (k start now : Nat) : Prop where
  ordered : start ≤ now
  started : (trace start p).pc = .scan c k (cfg.order p k)
  noReturn : ∀ time, start ≤ time → time < now →
    scanReturn (trace time) (commands time) p = none
  noAbort : ∀ time, start ≤ time → time < now → commands time ≠ .fail p

theorem scan_full {n : Nat} (cfg : Config n) (p : Proc n)
    (c d : Continuation) (k m : Nat) (remaining : List (Leaf n))
    (h : scan cfg p c k = .scan d m remaining) : remaining = cfg.order p m := by
  obtain ⟨_, rfl, rfl⟩ := PC.scan.inj h
  rfl

theorem resume_scan_full {n : Nat} (cfg : Config n) (p : Proc n)
    (c d : Continuation) (k m : Nat) (x : Value) (remaining : List (Leaf n))
    (h : resume cfg p c k x = .scan d m remaining) : remaining = cfg.order p m := by
  cases c <;> simp only [resume] at h
  · contradiction
  · split at h <;> contradiction
  · split at h
    · exact scan_full cfg p _ _ _ _ _ h
    · split at h <;> contradiction

/-- Backward classification: a scan suffix either begins at this step, with
its complete configured enumeration, or continues an unreturned old scan. -/
theorem scan_origin_step {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {p : Proc n} {c : Continuation} {k : Nat}
    {remaining : List (Leaf n)} (step : next cfg s command = some t)
    (after : (t p).pc = .scan c k remaining) :
    remaining = cfg.order p k ∨
      (∃ before, (s p).pc = .scan c k before) ∧
        scanReturn s command p = none ∧ command ≠ .fail p := by
  have preserved (same : t p = s p) (notRun : command ≠ .run p)
      (notFail : command ≠ .fail p) :
      (∃ before, (s p).pc = .scan c k before) ∧
        scanReturn s command p = none ∧ command ≠ .fail p := by
    refine ⟨⟨remaining, same ▸ after⟩, ?_, notFail⟩
    cases command <;> simp only [scanReturn]
    case run actor => simp [show actor ≠ p by simpa using notRun]
  cases command with
  | stutter =>
    exact Or.inr (preserved (congrFun (Option.some.inj step.symm) p) (by simp) (by simp))
  | fail actor =>
    simp only [next] at step
    split at step
    · simp at step
    · have ht := Option.some.inj step.symm
      by_cases same : p = actor
      · simp [ht, setLocal, same] at after
      · exact Or.inr (preserved (by simp [ht, setLocal, same]) (by simp)
          (by simpa using Ne.symm same))
  | restart actor =>
    simp only [next] at step
    split at step
    · have ht := Option.some.inj step.symm
      by_cases same : p = actor
      · simp [ht, setLocal, same] at after
      · exact Or.inr (preserved (by simp [ht, setLocal, same]) (by simp) (by simp))
    · simp at step
  | run actor =>
    simp only [next] at step
    cases run : ordinary cfg actor s with
    | none => simp [run] at step
    | some l =>
      have ht : t = setLocal s actor l := by simpa [run] using step.symm
      by_cases same : p = actor
      · subst actor
        have localAfter : l.pc = .scan c k remaining := by simpa [ht, setLocal] using after
        cases before : (s p).pc with
        | down => simp [ordinary, before] at run
        | idle =>
          simp only [ordinary, before, Option.some.injEq] at run
          subst l
          split at localAfter
          · contradiction
          · exact Or.inl (scan_full cfg p _ _ _ _ _ localAfter)
        | scan d m rest =>
          cases rest with
          | nil =>
            simp only [ordinary, before, Option.some.injEq] at run
            subst l
            exact Or.inl (resume_scan_full cfg p d c m k dead remaining localAfter)
          | cons j tail =>
            by_cases high : m ≤ (visible s j).level
            · simp only [ordinary, before, high, ite_true, Option.some.injEq] at run
              subst l
              exact Or.inl (resume_scan_full cfg p d c m k _ remaining localAfter)
            · simp only [ordinary, before, high, ite_false, Option.some.injEq] at run
              subst l
              have ids := PC.scan.inj localAfter
              rcases ids with ⟨rfl, rfl, rfl⟩
              exact Or.inr ⟨⟨j :: tail, rfl⟩,
                by simp [scanReturn, before, high], by simp⟩
        | write1 m v =>
          simp only [ordinary, before, Option.some.injEq] at run
          subst l
          exact Or.inl (scan_full cfg p _ _ _ _ _ localAfter)
        | write2 m v =>
          simp only [ordinary, before, Option.some.injEq] at run
          subst l
          exact Or.inl (scan_full cfg p _ _ _ _ _ localAfter)
        | waitSelf m x =>
          simp only [ordinary, before, Option.some.injEq] at run
          subst l
          split at localAfter
          · exact Or.inl (scan_full cfg p _ _ _ _ _ localAfter)
          · contradiction
        | pass m =>
          simp only [ordinary, before, Option.some.injEq] at run
          subst l
          split at localAfter
          · exact Or.inl (scan_full cfg p _ _ _ _ _ localAfter)
          · contradiction
        | self2 | enter | cs | release =>
          simp only [ordinary, before, Option.some.injEq] at run
          subst l
          contradiction
      · exact Or.inr (preserved (by simp [ht, setLocal, same])
          (by simpa using Ne.symm same) (by simp))

/-- Every open scan in a concrete initial prefix has a real full-enumeration
start. Incomplete and later-aborted scans are included, without pretending
they already have a result. -/
theorem concrete_open_scan {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {now : Nat}
    (initially : trace 0 = initial n) (valid : ValidPrefix cfg trace commands now)
    (p : Proc n) (c : Continuation) (k : Nat) (remaining : List (Leaf n))
    (pc : (trace now p).pc = .scan c k remaining) :
    ∃ start, OpenScan cfg trace commands p c k start now := by
  induction now generalizing remaining with
  | zero => simp [initially, initial] at pc
  | succ now ih =>
    rcases scan_origin_step (valid now (by omega)) pc with new | ⟨⟨before, old⟩, nr, nf⟩
    · refine ⟨now + 1, ⟨le_refl _, ?_, ?_, ?_⟩⟩
      · simpa [new] using pc
      · intros; omega
      · intros; omega
    · obtain ⟨start, hs⟩ := ih (fun t ht => valid t (by omega)) before old
      refine ⟨start, ⟨Nat.le_trans hs.ordered (Nat.le_succ _), hs.started, ?_, ?_⟩⟩
      · intro t lo hi
        by_cases last : t = now
        · simpa [last] using nr
        · exact hs.noReturn t lo (by omega)
      · intro t lo hi
        by_cases last : t = now
        · simpa [last] using nf
        · exact hs.noAbort t lo (by omega)

/-- An unreturned and unaborted scan can consume a low read or wait while
another actor steps; it cannot change its level, continuation or own pair. -/
theorem open_scan_step {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {p : Proc n} {c : Continuation} {k : Nat}
    {remaining : List (Leaf n)} (step : next cfg s command = some t)
    (pc : (s p).pc = .scan c k remaining)
    (noReturn : scanReturn s command p = none) (noAbort : command ≠ .fail p) :
    (∃ rest, (t p).pc = .scan c k rest) ∧ (t p).q = (s p).q := by
  rcases scan_step_classification pc step with run | ⟨fail, _⟩ | ⟨_, same⟩
  · subst command
    cases remaining with
    | nil => simp [scanReturn, pc] at noReturn
    | cons j rest =>
      have low : (visible s j).level < k := by
        by_contra h
        have high : k ≤ (visible s j).level := by omega
        simp [scanReturn, pc, high] at noReturn
      have ht := Option.some.inj ((scan_low_step cfg s p c k j rest pc low).symm.trans step)
      simp [← ht, setLocal]
  · exact (noAbort fail).elim
  · exact ⟨⟨remaining, by simpa [same] using pc⟩, by rw [same]⟩

/-- During an actual open invocation every intermediate point is the same
scan, possibly with a shorter suffix, and has the same own register. -/
theorem OpenScan.at {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {p : Proc n} {c : Continuation} {k start now : Nat}
    (openScan : OpenScan cfg trace commands p c k start now)
    (valid : ValidPrefix cfg trace commands now) (time : Nat)
    (lo : start ≤ time) (hi : time ≤ now) :
    (∃ rest, (trace time p).pc = .scan c k rest) ∧
      (trace time p).q = (trace start p).q := by
  induction time, lo using Nat.le_induction with
  | base => exact ⟨⟨cfg.order p k, openScan.started⟩, rfl⟩
  | succ time lo ih =>
    obtain ⟨⟨rest, pc⟩, q⟩ := ih (by omega)
    obtain ⟨post, same⟩ := open_scan_step (valid time (by omega)) pc
      (openScan.noReturn time lo (by omega)) (openScan.noAbort time lo (by omega))
    exact ⟨post, same.trans q⟩

theorem scanReturn_command {n : Nat} {s : State n} {command : Command n}
    {p : Proc n} {result : Value} (returned : scanReturn s command p = some result) :
    command = .run p := by
  cases command <;> simp only [scanReturn] at returned
  case run actor =>
    by_cases same : actor = p
    · simp [same]
    · simp [same] at returned
  all_goals contradiction

/-- Strengthen the history bridge's endpoint to the return's pre-state.
The sampled result is selected before its separately scheduled continuation;
there is no need to place a sample after a concrete write or next invocation. -/
theorem open_scan_return_observation {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {p : Proc n}
    {c : Continuation} {k start now : Nat} {result : Value}
    (openScan : OpenScan cfg trace commands p c k start now)
    (positive : 0 < k) (valid : ValidPrefix cfg trace commands (now + 1))
    (returned : scanReturn (trace now) (commands now) p = some result)
    (unique : ∀ time, start ≤ time → time ≤ now →
      ScanBridge.Unique (cfg.order p k) k (visible (trace time))) :
    ∃ time, start ≤ time ∧ time ≤ now ∧
      ScanBridge.Represents (cfg.order p k) k (visible (trace time)) result := by
  have ending : FirstScanReturn trace commands p start now result :=
    ⟨openScan.ordered, returned, openScan.noReturn, by
      intro time lo hi
      by_cases last : time = now
      · simp [last, scanReturn_command returned]
      · exact openScan.noAbort time lo (by omega)⟩
  obtain ⟨reads, inv, _, _, scope, _, replay, coverage⟩ :=
    concrete_scan_history positive valid openScan.started ending
  have observed := ScanBridge.qmax_has_historical_observation
    (trace := fun time j => visible (trace time) j)
    (reads := reads) openScan.ordered unique
    (fun time _ hi => next_singleChange (valid time (by omega)))
    (by
      intro resultDead j hj
      have all := coverage (replay.symm.trans resultDead)
      have member : j ∈ reads.map ScanBridge.Read.process := by rw [all]; exact hj
      obtain ⟨r, hr, id⟩ := List.mem_map.mp member
      exact ⟨r, hr, id⟩)
    (by
      intro r hr
      obtain ⟨lo, hi⟩ := scope r hr
      exact ⟨List.IsPrefix.subset inv.processes_prefix (List.mem_map.mpr ⟨r, hr, rfl⟩),
        lo, by omega⟩)
  simpa [replay] using observed

/-- Invocation start and all intermediate control facts are extracted from the
initial execution, including when the caller did not retain a scan history. -/
theorem concrete_return_observation {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {now : Nat}
    (initially : trace 0 = initial n) (valid : ValidPrefix cfg trace commands (now + 1))
    (p : Proc n) (c : Continuation) (k : Nat) (remaining : List (Leaf n))
    (pc : (trace now p).pc = .scan c k remaining) (result : Value)
    (returned : scanReturn (trace now) (commands now) p = some result)
    (unique : ∀ time, time ≤ now → ScanBridge.Unique (cfg.order p k) k (visible (trace time))) :
    ∃ start time, OpenScan cfg trace commands p c k start now ∧
      start ≤ time ∧ time ≤ now ∧
      ScanBridge.Represents (cfg.order p k) k (visible (trace time)) result := by
  obtain ⟨start, hs⟩ := concrete_open_scan initially (fun t ht => valid t (by omega)) p c k remaining pc
  have wf := (reachable_wellFormed (prefix_reachable initially valid now (by omega)) p).2.2
  have positive : 0 < k := by
    cases c <;> simp only [StageWF, pc] at wf <;> exact wf.1
  obtain ⟨time, lo, hi, observation⟩ := open_scan_return_observation hs positive valid returned
    (fun time _ hi => unique time hi)
  exact ⟨start, time, hs, lo, hi, observation⟩

/-- A possible ghost sample is backed by an actual state during the same
still-open concrete invocation. It may be earlier than every later scan read.
This is proof-only history, not an extra shared operation or a snapshot rule. -/
def ObservationSupport {n : Nat} (cfg : Config n) (trace : Nat → State n)
    (commands : Nat → Command n) (p : Proc n) (c : Continuation) (k now : Nat)
    (v : Node.Value) : Prop :=
  ∃ time remaining x, time ≤ now ∧ (trace time p).pc = .scan c k remaining ∧
    (∀ t, time ≤ t → t < now → scanReturn (trace t) (commands t) p = none) ∧
    (∀ t, time ≤ t → t < now → commands t ≠ .fail p) ∧
    ScanBridge.Represents (cfg.order p k) k (visible (trace time)) x ∧
    Node.projectValue k x = v

/-- The actual result belongs to the open invocation's historical observation
support. The only conditional premise left is lower-tree uniqueness; invocation
start, no-abort interval, cursor coverage, and observation timing are derived. -/
theorem concrete_return_supported {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {now : Nat}
    (initially : trace 0 = initial n) (valid : ValidPrefix cfg trace commands (now + 1))
    (p : Proc n) (c : Continuation) (k : Nat) (remaining : List (Leaf n))
    (pc : (trace now p).pc = .scan c k remaining) (result : Value)
    (returned : scanReturn (trace now) (commands now) p = some result)
    (unique : ∀ time, time ≤ now → ScanBridge.Unique (cfg.order p k) k (visible (trace time))) :
    ObservationSupport cfg trace commands p c k now (Node.projectValue k result) := by
  obtain ⟨start, time, hs, lo, hi, observed⟩ :=
    concrete_return_observation initially valid p c k remaining pc result returned unique
  obtain ⟨⟨rest, atTime⟩, _⟩ := hs.at (fun t ht => valid t (by omega)) time lo hi
  exact ⟨time, rest, result, hi, atTime,
    fun t ht hu => hs.noReturn t (by omega) hu,
    fun t ht hu => hs.noAbort t (by omega) hu, observed, rfl⟩

theorem support_current {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {p : Proc n} {c : Continuation} {k now : Nat}
    {remaining : List (Leaf n)} {x : Value}
    (pc : (trace now p).pc = .scan c k remaining)
    (observed : ScanBridge.Represents (cfg.order p k) k (visible (trace now)) x) :
    ObservationSupport cfg trace commands p c k now (Node.projectValue k x) :=
  ⟨now, remaining, x, le_refl _, pc, by intros; omega, by intros; omega, observed, rfl⟩

/-- History support persists while the concrete invocation stays open. -/
theorem support_extend {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {p : Proc n} {c : Continuation} {k now : Nat} {v : Node.Value}
    (supported : ObservationSupport cfg trace commands p c k now v)
    (noReturn : scanReturn (trace now) (commands now) p = none)
    (noAbort : commands now ≠ .fail p) :
    ObservationSupport cfg trace commands p c k (now + 1) v := by
  obtain ⟨time, rest, x, bound, pc, nr, nf, seen, value⟩ := supported
  refine ⟨time, rest, x, by omega, pc, ?_, ?_, seen, value⟩
  · intro t lo hi
    by_cases last : t = now
    · simpa [last] using noReturn
    · exact nr t lo (by omega)
  · intro t lo hi
    by_cases last : t = now
    · simpa [last] using noAbort
    · exact nf t lo (by omega)

/-- At a new state boundary support is either old support in the same
invocation or one new observation of that boundary. No future or aborted
invocation can contribute a cached continuation. -/
theorem support_succ_cases {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {p : Proc n} {c : Continuation} {k now : Nat} {v : Node.Value}
    (supported : ObservationSupport cfg trace commands p c k (now + 1) v) :
    (ObservationSupport cfg trace commands p c k now v ∧
      scanReturn (trace now) (commands now) p = none ∧ commands now ≠ .fail p) ∨
    (∃ rest x, (trace (now + 1) p).pc = .scan c k rest ∧
      ScanBridge.Represents (cfg.order p k) k (visible (trace (now + 1))) x ∧
      Node.projectValue k x = v) := by
  obtain ⟨time, rest, x, bound, pc, nr, nf, seen, value⟩ := supported
  by_cases last : time = now + 1
  · right; exact ⟨rest, x, last ▸ pc, last ▸ seen, value⟩
  · left
    have earlier : time ≤ now := by omega
    exact ⟨⟨time, rest, x, earlier, pc, fun t lo hi => nr t lo (by omega),
      fun t lo hi => nf t lo (by omega), seen, value⟩,
      nr now earlier (by omega), nf now earlier (by omega)⟩

/-- An old support witness implies the actor really is still in its named
scan and has kept its own whole pair since the chosen observation. -/
theorem support_control {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {p : Proc n} {c : Continuation} {k now : Nat} {v : Node.Value}
    (valid : ValidPrefix cfg trace commands now)
    (supported : ObservationSupport cfg trace commands p c k now v) :
    ∃ remaining, (trace now p).pc = .scan c k remaining := by
  obtain ⟨time, rest, x, bound, pc, nr, nf, _, _⟩ := supported
  suffices h : ∀ t, time ≤ t → t ≤ now → ∃ r, (trace t p).pc = .scan c k r by
    exact h now bound (le_refl _)
  intro t lo
  induction t, lo using Nat.le_induction with
  | base => intro _; exact ⟨rest, pc⟩
  | succ t lo ih =>
    intro hi
    obtain ⟨r, before⟩ := ih (by omega)
    exact (open_scan_step (valid t (by omega)) before (nr t lo (by omega))
      (nf t lo (by omega))).1

end EconomicalSolutions.Algorithm2

#print axioms EconomicalSolutions.Algorithm2.concrete_open_scan

#print axioms EconomicalSolutions.Algorithm2.OpenScan.at

#print axioms EconomicalSolutions.Algorithm2.concrete_return_observation

#print axioms EconomicalSolutions.Algorithm2.concrete_return_supported

#print axioms EconomicalSolutions.Algorithm2.support_succ_cases
