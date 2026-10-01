import Peterson.EconomicalSolutions.Algorithm2Foundation

/-! Ordered read histories for one concrete Algorithm 2 QMAX invocation.

The history is proof-only: it is reconstructed from command-indexed pre-states
of the unchanged interpreter.  Failure cannot be crossed because every
constructor retains the same owner's exact scan control until that invocation
returns. -/
namespace EconomicalSolutions.Algorithm2

/-- A natural-indexed execution of the concrete interpreter. -/
def ValidExecution {n : Nat} (cfg : Config n) (trace : Nat → State n)
    (commands : Nat → Command n) : Prop :=
  ∀ time, next cfg (trace time) (commands time) = some (trace (time + 1))

/-- An execution rooted at the reviewed all-idle, all-dead initial state. -/
def InitialExecution {n : Nat} (cfg : Config n) (trace : Nat → State n)
    (commands : Nat → Command n) : Prop :=
  trace 0 = initial n ∧ ValidExecution cfg trace commands

/-- The bounded form used when only a finite prefix is available. -/
def ValidPrefix {n : Nat} (cfg : Config n) (trace : Nat → State n)
    (commands : Nat → Command n) (finish : Nat) : Prop :=
  ∀ time, time < finish →
    next cfg (trace time) (commands time) = some (trace (time + 1))

/-- Cursor-history witness. `start` and `finish` are state times, so every
recorded read time names its pre-state. For a particular concrete invocation,
use `extract_scanInvocation`: its first-return premise prevents `delay` from
crossing an immediate wait return that restarts identical scan control. -/
inductive ScanInvocation {n : Nat} (cfg : Config n) (trace : Nat → State n)
    (commands : Nat → Command n) (p : Proc n) (c : Continuation) (k : Nat) :
    (remaining : List (Leaf n)) → (start finish : Nat) →
      (result : Value) → List (ScanBridge.Read (Leaf n)) → Prop where
  | dead {time : Nat}
      (pc : (trace time p).pc = .scan c k [])
      (command : commands time = .run p) :
      ScanInvocation cfg trace commands p c k [] time (time + 1) dead []
  | high {time : Nat} {j : Leaf n} {rest : List (Leaf n)}
      (pc : (trace time p).pc = .scan c k (j :: rest))
      (command : commands time = .run p)
      (qualifies : k ≤ (visible (trace time) j).level) :
      ScanInvocation cfg trace commands p c k (j :: rest) time (time + 1)
        (visible (trace time) j) [⟨j, time⟩]
  | low {time finish : Nat} {j : Leaf n} {rest : List (Leaf n)}
      {result : Value} {reads : List (ScanBridge.Read (Leaf n))}
      (pc : (trace time p).pc = .scan c k (j :: rest))
      (command : commands time = .run p)
      (below : (visible (trace time) j).level < k)
      (tail : ScanInvocation cfg trace commands p c k rest (time + 1) finish result reads) :
      ScanInvocation cfg trace commands p c k (j :: rest) time finish result
        (⟨j, time⟩ :: reads)
  | delay {time finish : Nat} {remaining : List (Leaf n)}
      {result : Value} {reads : List (ScanBridge.Read (Leaf n))}
      (before : (trace time p).pc = .scan c k remaining)
      (after : (trace (time + 1) p).pc = .scan c k remaining)
      (tail : ScanInvocation cfg trace commands p c k remaining (time + 1) finish result reads) :
      ScanInvocation cfg trace commands p c k remaining time finish result reads

/-- Observable return of the owner's current QMAX instruction. A high wait
sample is a return even when `resume` immediately starts an identical scan.
This metadata adds no state and does not group reads into histories. -/
def scanReturn {n : Nat} (s : State n) (command : Command n) (p : Proc n) : Option Value :=
  match command with
  | .run actor => if actor = p then
      match (s p).pc with
      | .scan _ _ [] => some dead
      | .scan _ k (j :: _) =>
          if k ≤ (visible s j).level then some (visible s j) else none
      | _ => none
    else none
  | _ => none

/-- Return metadata agrees with the actual interpreter's continuation, even
when that continuation immediately starts a new scan. -/
theorem scanReturn_step {n : Nat} {cfg : Config n} {s : State n}
    {command : Command n} {p : Proc n} {c : Continuation} {k : Nat}
    {remaining : List (Leaf n)} {result : Value}
    (pc : (s p).pc = .scan c k remaining)
    (returned : scanReturn s command p = some result) :
    next cfg s command = some (setLocal s p { s p with pc := resume cfg p c k result }) := by
  cases command with
  | run actor =>
    by_cases same : actor = p
    · subst actor
      cases remaining with
      | nil =>
        have value : result = dead := by simpa [scanReturn, pc] using returned.symm
        subst result
        simp [next, ordinary, pc]
      | cons j rest =>
        by_cases high : k ≤ (visible s j).level
        · have value : result = visible s j := by
            simpa [scanReturn, pc, high] using returned.symm
          subst result
          exact scan_high_step cfg s p c k j rest pc high
        · simp [scanReturn, pc, high] at returned
    · simp [scanReturn, same] at returned
  | fail | restart | stutter => simp [scanReturn] at returned

/-- Every valid instruction while the owner scans is its ordinary instruction,
its aborting failure, or a step preserving its entire local state. Restart of
that owner is impossible while scanning. -/
theorem scan_step_classification {n : Nat} {cfg : Config n} {s t : State n}
    {command : Command n} {p : Proc n} {c : Continuation} {k : Nat}
    {remaining : List (Leaf n)}
    (pc : (s p).pc = .scan c k remaining)
    (step : next cfg s command = some t) :
    command = .run p ∨ (command = .fail p ∧ (t p).pc = .down) ∨ (command ≠ .run p ∧ t p = s p) := by
  cases command with
  | run actor =>
    by_cases same : actor = p
    · exact Or.inl (by simp [same])
    · right; right
      refine ⟨by simp [same], ?_⟩
      simp only [next] at step
      cases h : ordinary cfg actor s with
      | none => simp [h] at step
      | some l =>
        have ht : t = setLocal s actor l := by simpa [h] using step.symm
        simp [ht, setLocal, Ne.symm same]
  | fail actor =>
    by_cases same : actor = p
    · subst actor
      have ht : t = setLocal s p ⟨.down, dead⟩ := by
        simpa [next, pc] using step.symm
      exact Or.inr (Or.inl ⟨rfl, by simp [ht, setLocal]⟩)
    · right; right
      refine ⟨by simp, ?_⟩
      simp only [next] at step
      split at step
      · simp at step
      · have ht := Option.some.inj step.symm
        simp [ht, setLocal, Ne.symm same]
  | restart actor =>
    by_cases same : actor = p
    · subst actor; simp [next, pc] at step
    · right; right
      refine ⟨by simp, ?_⟩
      simp only [next] at step
      split at step
      · have ht := Option.some.inj step.symm
        simp [ht, setLocal, Ne.symm same]
      · simp at step
  | stutter =>
    right; right
    refine ⟨by simp, ?_⟩
    have ht := Option.some.inj step.symm
    exact congrFun ht p

/-- The interval ends immediately after its first observed return and contains
no owner failure. Neither cursor decomposition nor history correctness is an
assumption; both will be reconstructed from the interpreter. -/
structure FirstScanReturn {n : Nat} (trace : Nat → State n)
    (commands : Nat → Command n) (p : Proc n) (start returned : Nat) (result : Value) : Prop where
  ordered : start ≤ returned
  returns : scanReturn (trace returned) (commands returned) p = some result
  first : ∀ time, start ≤ time → time < returned →
    scanReturn (trace time) (commands time) p = none
  noAbort : ∀ time, start ≤ time → time ≤ returned → commands time ≠ .fail p

/-- Reconstruct the actual ordered cursor history, stopping at the first
returning instruction even if that instruction starts another wait scan. -/
theorem extract_scanInvocation {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {p : Proc n} {c : Continuation} {k : Nat}
    {remaining : List (Leaf n)} {start returned : Nat} {result : Value}
    (valid : ValidPrefix cfg trace commands (returned + 1))
    (pc : (trace start p).pc = .scan c k remaining)
    (ending : FirstScanReturn trace commands p start returned result) :
    ∃ reads, ScanInvocation cfg trace commands p c k remaining start (returned + 1) result reads := by
  have bound := ending.ordered
  induction distance : returned - start using Nat.strong_induction_on generalizing start remaining with
  | h distance ih =>
    have step := valid start (by omega)
    rcases scan_step_classification pc step with owner | ⟨failure, down⟩ | ⟨notOwner, preserved⟩
    · cases remaining with
      | nil =>
        have ret : scanReturn (trace start) (commands start) p = some dead := by
          simp [scanReturn, owner, pc]
        have same : start = returned := by
          by_contra ne
          have := ending.first start (by omega) (by omega)
          rw [ret] at this
          contradiction
        subst start
        have value : result = dead := Option.some.inj (ending.returns.symm.trans ret)
        subst result
        exact ⟨[], .dead pc owner⟩
      | cons j rest =>
        by_cases high : k ≤ (visible (trace start) j).level
        · have ret : scanReturn (trace start) (commands start) p =
              some (visible (trace start) j) := by simp [scanReturn, owner, pc, high]
          have same : start = returned := by
            by_contra ne
            have := ending.first start (by omega) (by omega)
            rw [ret] at this
            contradiction
          subst start
          have value : result = visible (trace returned) j :=
            Option.some.inj (ending.returns.symm.trans ret)
          subst result
          exact ⟨[⟨j, returned⟩], .high pc owner high⟩
        · have low : (visible (trace start) j).level < k := by omega
          have ret : scanReturn (trace start) (commands start) p = none := by
            simp [scanReturn, owner, pc, high]
          have before : start < returned := by
            by_contra ne
            have same : start = returned := by omega
            rw [same, ending.returns] at ret
            contradiction
          have after : (trace (start + 1) p).pc = .scan c k rest := by
            rw [owner, scan_low_step cfg (trace start) p c k j rest pc low] at step
            have ht := Option.some.inj step.symm
            simp [ht, setLocal]
          have tailEnd : FirstScanReturn trace commands p (start + 1) returned result :=
            ⟨by omega, ending.returns,
             fun time lo hi => ending.first time (by omega) hi,
             fun time lo hi => ending.noAbort time (by omega) hi⟩
          obtain ⟨reads, tail⟩ := ih (returned - (start + 1)) (by omega) after
            tailEnd tailEnd.ordered rfl
          exact ⟨⟨j, start⟩ :: reads, .low pc owner low tail⟩
    · exact (ending.noAbort start (by omega) (by omega) failure).elim
    · have noReturn : scanReturn (trace start) (commands start) p = none := by
        cases hcmd : commands start <;> simp [scanReturn]
        case run actor =>
          have : actor ≠ p := by intro h; subst actor; exact notOwner hcmd
          simp [this]
      have before : start < returned := by
        by_contra ne
        have same : start = returned := by omega
        rw [same, ending.returns] at noReturn
        contradiction
      have after : (trace (start + 1) p).pc = .scan c k remaining := by rw [preserved]; exact pc
      have tailEnd : FirstScanReturn trace commands p (start + 1) returned result :=
        ⟨by omega, ending.returns,
         fun time lo hi => ending.first time (by omega) hi,
         fun time lo hi => ending.noAbort time (by omega) hi⟩
      obtain ⟨reads, tail⟩ := ih (returned - (start + 1)) (by omega) after
        tailEnd tailEnd.ordered rfl
      exact ⟨reads, .delay pc after tail⟩

namespace ScanInvocation

variable {n : Nat} {cfg : Config n} {trace : Nat → State n}
  {commands : Nat → Command n} {p : Proc n} {c : Continuation} {k : Nat}
  {remaining : List (Leaf n)} {start finish : Nat} {result : Value}
  {reads : List (ScanBridge.Read (Leaf n))}

/-- An invocation always consumes at least its returning instruction. -/
theorem start_lt_finish
    (inv : ScanInvocation cfg trace commands p c k remaining start finish result reads) :
    start < finish := by
  induction inv with
  | dead | high => omega
  | low _ _ _ ih | delay _ _ ih => omega

/-- Read metadata is exactly the interpreter's observation of the corresponding
command and pre-state, including the sampled whole pair. -/
theorem read_metadata
    (inv : ScanInvocation cfg trace commands p c k remaining start finish result reads) :
    ∀ r ∈ reads,
      scanRead (trace r.time) (commands r.time) =
        some (p, r.process, visible (trace r.time) r.process) := by
  induction inv with
  | dead => simp
  | high pc command qualifies =>
      intro r member
      simp only [List.mem_singleton] at member
      subst r
      simp [scanRead, command, pc]
  | low pc command below tail ih =>
      intro r member
      rcases List.mem_cons.mp member with rfl | member
      · simp [scanRead, command, pc]
      · exact ih r member
  | delay before after tail ih => exact ih

/-- Recorded times stay inside the invocation's state interval. -/
theorem read_times
    (inv : ScanInvocation cfg trace commands p c k remaining start finish result reads) :
    ∀ r ∈ reads, start ≤ r.time ∧ r.time < finish := by
  induction inv with
  | dead => simp
  | high =>
      intro r member
      simp only [List.mem_singleton] at member
      subst r
      exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
  | low pc command below tail ih =>
      intro r member
      rcases List.mem_cons.mp member with rfl | member
      · constructor
        · rfl
        · simpa using Nat.lt_trans (Nat.lt_succ_self _) tail.start_lt_finish
      · obtain ⟨lo, hi⟩ := ih r member
        exact ⟨by omega, hi⟩
  | delay before after tail ih =>
      intro r member
      obtain ⟨lo, hi⟩ := ih r member
      exact ⟨by omega, hi⟩

/-- The list itself is chronological; interleaving delay steps can leave gaps. -/
theorem chronological
    (inv : ScanInvocation cfg trace commands p c k remaining start finish result reads) :
    reads.Pairwise (fun earlier later => earlier.time < later.time) := by
  induction inv with
  | dead | high => simp
  | low pc command below tail ih =>
      simp only [List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro r member
      have times := read_times tail r member
      omega
  | delay before after tail ih => exact ih

/-- The actual read identities form a prefix of the invocation's remaining
fixed enumeration.  Thus an early qualifying return has its actual prefix,
without hypothetical suffix reads. -/
theorem processes_prefix
    (inv : ScanInvocation cfg trace commands p c k remaining start finish result reads) :
    (reads.map ScanBridge.Read.process).IsPrefix remaining := by
  induction inv with
  | dead => simp
  | high => simp
  | low pc command below tail ih =>
      obtain ⟨suffix, same⟩ := ih
      refine ⟨suffix, ?_⟩
      simp only [List.map_cons, List.cons_append, List.cons.injEq, true_and]
      exact same
  | delay before after tail ih => exact ih

/-- Replaying the recorded reads gives exactly the concrete invocation result. -/
theorem qmax_eq_result
    (inv : ScanInvocation cfg trace commands p c k remaining start finish result reads) :
    ScanBridge.qmax k (fun time j => visible (trace time) j) reads = result := by
  induction inv with
  | dead => rfl
  | high pc command qualifies => simp [ScanBridge.qmax, qualifies]
  | low pc command below tail ih =>
      simp only [ScanBridge.qmax]
      split
      · omega
      · exact ih
  | delay before after tail ih => exact ih

/-- At positive protocol levels, a dead return is possible only after the
cursor has consumed the complete remaining enumeration. -/
theorem dead_enumerates_all (positive : 0 < k)
    (inv : ScanInvocation cfg trace commands p c k remaining start finish result reads)
    (returned : result = Algorithm2.dead) :
    reads.map ScanBridge.Read.process = remaining := by
  induction inv with
  | dead => rfl
  | high pc command qualifies =>
      change visible (trace _) _ = Algorithm2.dead at returned
      have level := congrArg ScanBridge.Value.level returned
      simp [Algorithm2.dead, ScanBridge.dead] at level
      omega
  | low pc command below tail ih =>
      simp only [List.map_cons]
      congr
      exact ih returned
  | delay before after tail ih => exact ih returned

end ScanInvocation

/-- Exact helper-facing facts for a scan that starts at the fixed complete
opponent enumeration. Coverage on dead return is a theorem of cursor execution,
not a premise. -/
theorem complete_scan_history {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {p : Proc n} {c : Continuation} {k : Nat}
    {start finish : Nat} {result : Value} {reads : List (ScanBridge.Read (Leaf n))}
    (positive : 0 < k) (valid : ValidPrefix cfg trace commands finish)
    (inv : ScanInvocation cfg trace commands p c k (cfg.order p k)
      start finish result reads) :
    ScanBridge.qmax k (fun time j => visible (trace time) j) reads = result ∧
    reads.Pairwise (fun earlier later => earlier.time < later.time) ∧
    (∀ r ∈ reads, r.process ∈ cfg.order p k ∧ start ≤ r.time ∧ r.time ≤ finish) ∧
    (result = Algorithm2.dead → ∀ j ∈ cfg.order p k, ∃ r ∈ reads, r.process = j) ∧
    (∀ time, start ≤ time → time < finish →
      next cfg (trace time) (commands time) = some (trace (time + 1))) := by
  refine ⟨inv.qmax_eq_result, inv.chronological, ?_, ?_, ?_⟩
  · intro r member
    have hpref := inv.processes_prefix
    have process_member : r.process ∈ reads.map ScanBridge.Read.process :=
      List.mem_map.mpr ⟨r, member, rfl⟩
    have order_member := List.IsPrefix.subset hpref process_member
    obtain ⟨lo, hi⟩ := inv.read_times r member
    exact ⟨order_member, lo, Nat.le_of_lt hi⟩
  · intro returned j member
    have all := inv.dead_enumerates_all positive returned
    have mapped : j ∈ reads.map ScanBridge.Read.process := by simpa [all] using member
    obtain ⟨r, in_reads, same⟩ := List.mem_map.mp mapped
    exact ⟨r, in_reads, same⟩
  · intro time lower upper
    exact valid time upper

/-- Feed one concrete completed invocation directly to the conditional
historical-observation bridge.  Uniqueness remains a later tree-ownership
obligation and is not used to restrict `ValidPrefix` or `ScanInvocation`. -/
theorem complete_scan_has_historical_observation
    {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {p : Proc n} {c : Continuation} {k : Nat}
    {start finish : Nat} {result : Value} {reads : List (ScanBridge.Read (Leaf n))}
    (positive : 0 < k) (valid : ValidPrefix cfg trace commands finish)
    (inv : ScanInvocation cfg trace commands p c k (cfg.order p k)
      start finish result reads)
    (unique : ∀ time, start ≤ time → time ≤ finish →
      ScanBridge.Unique (cfg.order p k) k (fun j => visible (trace time) j))
    (atomic : ∀ time, start ≤ time → time < finish →
      ScanBridge.SingleChange (fun j => visible (trace time) j)
        (fun j => visible (trace (time + 1)) j)) :
    ∃ time, start ≤ time ∧ time ≤ finish ∧
      ScanBridge.Represents (cfg.order p k) k
        (fun j => visible (trace time) j) result := by
  obtain ⟨replay, chronological, scope, coverage, steps⟩ :=
    complete_scan_history positive valid inv
  have observed := ScanBridge.qmax_has_historical_observation
    (trace := fun time j => visible (trace time) j)
    (reads := reads) (Nat.le_of_lt inv.start_lt_finish) unique atomic
    (by
      intro returned j member
      exact coverage (replay.symm.trans returned) j member)
    scope
  simpa [replay] using observed

/-- Infinite executions supply the same finite extraction without any fairness
or eventual-return assertion. Completion is the observed endpoint premise. -/
theorem execution_extract_scanInvocation {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {p : Proc n}
    {c : Continuation} {k : Nat} {remaining : List (Leaf n)}
    {start returned : Nat} {result : Value}
    (valid : ValidExecution cfg trace commands)
    (pc : (trace start p).pc = .scan c k remaining)
    (ending : FirstScanReturn trace commands p start returned result) :
    ∃ reads, ScanInvocation cfg trace commands p c k remaining start (returned + 1) result reads :=
  extract_scanInvocation (fun time _ => valid time) pc ending

/-- A concrete full-enumeration scan supplies the witness and all its read
facts. In particular, neither the prefix nor dead-return coverage is assumed. -/
theorem concrete_scan_history {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {p : Proc n} {c : Continuation} {k : Nat}
    {start returned : Nat} {result : Value}
    (positive : 0 < k) (valid : ValidPrefix cfg trace commands (returned + 1))
    (pc : (trace start p).pc = .scan c k (cfg.order p k))
    (ending : FirstScanReturn trace commands p start returned result) :
    ∃ reads, ScanInvocation cfg trace commands p c k (cfg.order p k)
        start (returned + 1) result reads ∧
      reads.Pairwise (fun earlier later => earlier.time < later.time) ∧
      (reads.map ScanBridge.Read.process).IsPrefix (cfg.order p k) ∧
      (∀ r ∈ reads, start ≤ r.time ∧ r.time < returned + 1) ∧
      (∀ r ∈ reads, scanRead (trace r.time) (commands r.time) =
        some (p, r.process, visible (trace r.time) r.process)) ∧
      ScanBridge.qmax k (fun time j => visible (trace time) j) reads = result ∧
      (result = dead → reads.map ScanBridge.Read.process = cfg.order p k) := by
  obtain ⟨reads, inv⟩ := extract_scanInvocation valid pc ending
  exact ⟨reads, inv, inv.chronological, inv.processes_prefix, inv.read_times,
    inv.read_metadata, inv.qmax_eq_result, inv.dead_enumerates_all positive⟩

/-- The historical-observation bridge now starts from concrete execution and
return events. Single-register evolution is discharged from the interpreter;
only the later tree-ownership uniqueness obligation remains conditional. -/
theorem concrete_scan_has_historical_observation
    {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {p : Proc n} {c : Continuation} {k : Nat}
    {start returned : Nat} {result : Value}
    (positive : 0 < k) (valid : ValidPrefix cfg trace commands (returned + 1))
    (pc : (trace start p).pc = .scan c k (cfg.order p k))
    (ending : FirstScanReturn trace commands p start returned result)
    (unique : ∀ time, start ≤ time → time ≤ returned + 1 →
      ScanBridge.Unique (cfg.order p k) k (fun j => visible (trace time) j)) :
    ∃ time, start ≤ time ∧ time ≤ returned + 1 ∧
      ScanBridge.Represents (cfg.order p k) k
        (fun j => visible (trace time) j) result := by
  obtain ⟨reads, inv⟩ := extract_scanInvocation valid pc ending
  exact complete_scan_has_historical_observation positive valid inv unique
    (fun time _ hi => next_singleChange (valid time hi))

end EconomicalSolutions.Algorithm2

#print axioms EconomicalSolutions.Algorithm2.ScanInvocation.read_metadata
#print axioms EconomicalSolutions.Algorithm2.ScanInvocation.chronological
#print axioms EconomicalSolutions.Algorithm2.ScanInvocation.processes_prefix
#print axioms EconomicalSolutions.Algorithm2.ScanInvocation.qmax_eq_result
#print axioms EconomicalSolutions.Algorithm2.ScanInvocation.dead_enumerates_all
#print axioms EconomicalSolutions.Algorithm2.complete_scan_history
#print axioms EconomicalSolutions.Algorithm2.complete_scan_has_historical_observation

#print axioms EconomicalSolutions.Algorithm2.scan_step_classification
#print axioms EconomicalSolutions.Algorithm2.extract_scanInvocation
#print axioms EconomicalSolutions.Algorithm2.execution_extract_scanInvocation
#print axioms EconomicalSolutions.Algorithm2.concrete_scan_history
#print axioms EconomicalSolutions.Algorithm2.concrete_scan_has_historical_observation

#print axioms EconomicalSolutions.Algorithm2.scanReturn_step
