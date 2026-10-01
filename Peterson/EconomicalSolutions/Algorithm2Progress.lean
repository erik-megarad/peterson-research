import Peterson.EconomicalSolutions.Algorithm2Refinement
import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-! Source-level scheduling and finite progress for Algorithm 2. All execution
premises refer to the concrete interpreter; no local-node fairness is assumed. -/
namespace EconomicalSolutions.Algorithm2

def pendingPC {n : Nat} : PC n → Bool
  | .scan _ _ _ | .write1 _ _ | .self2 _ | .write2 _ _ | .waitSelf _ _ | .pass _ | .enter => true
  | _ => false

def Pending {n : Nat} (s : State n) (p : Proc n) : Prop := pendingPC (s p).pc = true

def protocolPC {n : Nat} (pc : PC n) : Bool := pendingPC pc || pc == .release

def Acts {n : Nat} (c : Command n) (p : Proc n) : Prop := c = .run p ∨ c = .fail p

structure Run {n : Nat} (cfg : Config n) where
  state : Nat → State n
  command : Nat → Command n
  initialized : state 0 = initial n
  valid : ∀ t, next cfg (state t) (command t) = some (state (t + 1))

def Run.event {n : Nat} {cfg : Config n} (r : Run cfg) (t : Nat) : Label n :=
  label (r.state t) (r.command t)

/-- Every occurrence owes one later ordinary instruction or an abort. Idle and
failed processes owe no participation; arbitrary global stutter is admitted. -/
def ProtocolScheduling {n : Nat} {cfg : Config n} (r : Run cfg) : Prop :=
  ∀ t p, protocolPC (r.state t p).pc = true → ∃ u, t ≤ u ∧ Acts (r.command u) p

/-- Real critical completion is a client premise distinct from scheduling. -/
def CriticalCompletion {n : Nat} {cfg : Config n} (r : Run cfg) : Prop :=
  ∀ t p, (r.state t p).pc = .cs →
    ∃ u, t ≤ u ∧ (r.event u = .complete p ∨ r.event u = .fail p)

/-- Matching service before any intervening own abort or replacement passage. -/
def Served {n : Nat} {cfg : Config n} (r : Run cfg) (p : Proc n) (start finish : Nat) : Prop :=
  start ≤ finish ∧ r.event finish = .entry p ∧
    ∀ t, start ≤ t → t < finish →
      Pending (r.state t) p ∧ r.event t ≠ .fail p ∧ r.event t ≠ .entry p

theorem Run.omega_execution {n : Nat} {cfg : Config n} (r : Run cfg) :
    (lts cfg).OmegaExecution r.state r.event := fun t => ⟨r.command t, r.valid t, rfl⟩

theorem Run.reachable {n : Nat} {cfg : Config n} (r : Run cfg) (t : Nat) :
    Reachable cfg (r.state t) :=
  prefix_reachable r.initialized (fun u _ => r.valid u) t (le_refl _)

theorem Run.wellFormed {n : Nat} {cfg : Config n} (r : Run cfg) (t : Nat) :
    WellFormed (r.state t) := reachable_wellFormed (r.reachable t)

/-- Restart cannot affect a live process; before its next run/failure its
entire local state stays fixed, despite arbitrary commands of every peer. -/
theorem next_live_unchanged {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    {p : Proc n} (valid : next cfg s c = some t) (live : (s p).pc ≠ .down)
    (noAct : ¬ Acts c p) : t p = s p := by
  apply next_other_local p valid
  · exact fun h => noAct (Or.inl h)
  · exact fun h => noAct (Or.inr h)
  · intro h
    subst c
    simp [next, live] at valid

theorem interval_live_unchanged {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {start finish : Nat} (bound : start ≤ finish)
    (live : (r.state start p).pc ≠ .down)
    (noAct : ∀ t, start ≤ t → t < finish → ¬ Acts (r.command t) p) :
    r.state finish p = r.state start p := by
  induction finish, bound using Nat.le_induction with
  | base => rfl
  | succ finish bound ih =>
    have before := ih (fun t lo hi => noAct t lo (by omega))
    exact (next_live_unchanged (r.valid finish) (by simpa [before] using live)
      (noAct finish bound (by omega))).trans before

/-- Minimality makes the instruction scheduled for this occurrence apply to
that same local state, not a later restarted request. -/
theorem first_scheduled_action {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (owed : protocolPC (r.state start p).pc = true) :
    ∃ finish, start ≤ finish ∧ Acts (r.command finish) p ∧
      r.state finish p = r.state start p ∧
      ∀ t, start ≤ t → t < finish → ¬ Acts (r.command t) p := by
  classical
  have hex := fair start p owed
  let finish := Nat.find hex
  have spec := Nat.find_spec hex
  have before : ∀ t, start ≤ t → t < finish → ¬ Acts (r.command t) p := by
    intro t lo hi act
    have := Nat.find_min' hex (show start ≤ t ∧ Acts (r.command t) p from ⟨lo, act⟩)
    omega
  have live : (r.state start p).pc ≠ .down := by
    intro pc
    simp [protocolPC, pendingPC, pc] at owed
  exact ⟨finish, spec.1, spec.2, interval_live_unchanged r spec.1 live before, before⟩

/-- Fair concrete cursor work finishes a finite scan or aborts its owner.
Immediate higher-level wait retries still count as returns of this invocation. -/
theorem scan_eventually_returns_or_fails {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {c : Continuation} {k start : Nat}
    {remaining : List (Leaf n)} (pc : (r.state start p).pc = .scan c k remaining) :
    ∃ finish, start ≤ finish ∧
      ((scanReturn (r.state finish) (r.command finish) p).isSome = true ∨
        r.command finish = .fail p) := by
  induction remaining generalizing start with
  | nil =>
    obtain ⟨finish, bound, act, same, _⟩ := first_scheduled_action r fair
      (p := p) (start := start) (by simp [protocolPC, pendingPC, pc])
    refine ⟨finish, bound, ?_⟩
    rcases act with run | fail
    · left; simp [scanReturn, run, same, pc]
    · exact Or.inr fail
  | cons j rest ih =>
    obtain ⟨time, bound, act, same, _⟩ := first_scheduled_action r fair
      (p := p) (start := start) (by simp [protocolPC, pendingPC, pc])
    rcases act with run | fail
    · by_cases high : k ≤ (visible (r.state time) j).level
      · exact ⟨time, bound, Or.inl (by simp [scanReturn, run, same, pc, high])⟩
      · have pcTime : (r.state time p).pc = .scan c k (j :: rest) := by rw [same]; exact pc
        have after := scan_low_step cfg (r.state time) p c k j rest pcTime (by omega)
        have nextPC : (r.state (time + 1) p).pc = .scan c k rest := by
          have eq := Option.some.inj (after.symm.trans (run ▸ r.valid time))
          simp [← eq, setLocal]
        obtain ⟨finish, bound', result⟩ := ih nextPC
        exact ⟨finish, by omega, result⟩
    · exact ⟨time, bound, Or.inr fail⟩

/-- The first return/failure belongs to the original invocation. In the return
case its complete cursor history can be extracted with existing history lemmas. -/
theorem scan_first_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {c : Continuation} {k start : Nat}
    {remaining : List (Leaf n)} (pc : (r.state start p).pc = .scan c k remaining) :
    ∃ finish, start ≤ finish ∧
      ((∃ result, FirstScanReturn r.state r.command p start finish result) ∨
        (r.command finish = .fail p ∧
          ∀ t, start ≤ t → t < finish →
            scanReturn (r.state t) (r.command t) p = none ∧ r.command t ≠ .fail p)) := by
  classical
  have hex := scan_eventually_returns_or_fails r fair pc
  let finish := Nat.find hex
  have spec := Nat.find_spec hex
  have before : ∀ t, start ≤ t → t < finish →
      scanReturn (r.state t) (r.command t) p = none ∧ r.command t ≠ .fail p := by
    intro t lo hi
    have h := Nat.find_min hex hi
    simp only [not_and, not_or, Bool.not_eq_true] at h
    have facts := h lo
    refine ⟨?_, facts.2⟩
    cases ret : scanReturn (r.state t) (r.command t) p with
    | none => rfl
    | some value => simp [ret] at facts
  refine ⟨finish, spec.1, ?_⟩
  rcases spec.2 with returns | fail
  · obtain ⟨result, ret⟩ := Option.isSome_iff_exists.mp returns
    left
    refine ⟨result, ⟨spec.1, ret, fun t lo hi => (before t lo hi).1, ?_⟩⟩
    intro t lo hi
    by_cases last : t = finish
    · subst t
      intro fail
      have cmd := scanReturn_command ret
      change r.command finish = .run p at cmd
      rw [fail] at cmd
      contradiction
    · exact (before t lo (by omega)).2
  · exact Or.inr ⟨fail, before⟩

/-- A finite control-stage measure, constant throughout one wait loop.
It does not count scheduling delay, scan length, or peer behavior. -/
def phase {n : Nat} : PC n → Nat
  | .scan .first k _ => 7 * (k - 1)
  | .write1 k _ => 7 * (k - 1) + 1
  | .scan .second k _ => 7 * (k - 1) + 2
  | .self2 k => 7 * (k - 1) + 3
  | .write2 k _ => 7 * (k - 1) + 4
  | .scan .wait k _ | .waitSelf k _ => 7 * (k - 1) + 5
  | .pass k => 7 * (k - 1) + 6
  | .enter | .cs | .release => 7 * height n
  | .idle | .down => 0

def WaitingAt {n : Nat} (k : Nat) (pc : PC n) : Prop :=
  (∃ rest, pc = .scan .wait k rest) ∨ (∃ x, pc = .waitSelf k x)

def Outcome {n : Nat} (s : State n) (c : Command n) (p : Proc n) : Prop :=
  label s c = .entry p ∨ label s c = .fail p

theorem phase_bound {n : Nat} {l : Local n} (wf : LocalWF l) :
    phase l.pc ≤ 7 * height n := by
  have stage := wf.2.2
  cases pc : l.pc <;> simp only [StageWF, pc, phase] at *
  case scan c k rest => cases c <;> dsimp at * <;> omega
  all_goals omega

theorem resume_pending_phase {n : Nat} (cfg : Config n) (p : Proc n)
    (c : Continuation) (k : Nat) (x : Value) (rest : List (Leaf n)) :
    pendingPC (resume cfg p c k x) = true ∧
      phase (.scan c k rest) ≤ phase (resume cfg p c k x) ∧
      (c ≠ .wait → phase (.scan c k rest) < phase (resume cfg p c k x)) := by
  cases c <;> simp only [resume]
  · simp [pendingPC, phase]
  · split <;> simp [pendingPC, phase]
  · split
    · simp [pendingPC, phase, scan]
    · split <;> simp [pendingPC, phase]

theorem ordinary_pending_phase {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {l : Local n} (wf : LocalWF (s p)) (pending : Pending s p)
    (noEntry : (s p).pc ≠ .enter) (step : ordinary cfg p s = some l) :
    pendingPC l.pc = true ∧ phase (s p).pc ≤ phase l.pc := by
  have stage := wf.2.2
  cases pc : (s p).pc with
  | down | idle | cs | release => simp [Pending, pendingPC, pc] at pending
  | enter => exact (noEntry pc).elim
  | scan c k rest =>
    cases rest with
    | nil =>
      simp only [ordinary, pc, Option.some.injEq] at step
      subst l
      exact ⟨(resume_pending_phase cfg p c k dead []).1,
        by simpa [pc] using (resume_pending_phase cfg p c k dead []).2.1⟩
    | cons j rest =>
      simp only [ordinary, pc, Option.some.injEq] at step
      subst l
      split
      · exact ⟨(resume_pending_phase cfg p c k (visible s j) (j :: rest)).1,
          by simpa [pc] using (resume_pending_phase cfg p c k (visible s j) (j :: rest)).2.1⟩
      · cases c <;> simp [pendingPC, phase]
  | write1 k v | self2 k | write2 k v =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp [pendingPC, phase, scan]
  | waitSelf k x =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    split <;> simp [pendingPC, phase, scan]
  | pass k =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp only [StageWF, pc] at stage
    split <;> simp [pendingPC, phase, scan] <;> omega

theorem next_pending_phase {n : Nat} {cfg : Config n} {s t : State n}
    {p : Proc n} {c : Command n} (wf : LocalWF (s p)) (pending : Pending s p)
    (valid : next cfg s c = some t) (noOutcome : ¬ Outcome s c p) :
    Pending t p ∧ phase (s p).pc ≤ phase (t p).pc := by
  have noFail : c ≠ .fail p := by
    intro eq; exact noOutcome (Or.inr (by simp [label, eq]))
  by_cases own : c = .run p
  · subst c
    have noEntry : (s p).pc ≠ .enter := by
      intro eq; exact noOutcome (Or.inl (by simp [label, eq]))
    simp only [next] at valid
    cases step : ordinary cfg p s with
    | none => simp [step] at valid
    | some l =>
      have after : t = setLocal s p l := by simpa [step] using valid.symm
      simpa [Pending, after, setLocal] using ordinary_pending_phase wf pending noEntry step
  · have live : (s p).pc ≠ .down := by intro eq; simp [Pending, pendingPC, eq] at pending
    have same := next_live_unchanged valid live (not_or.mpr ⟨own, noFail⟩)
    simpa [Pending, same] using And.intro pending (Nat.le_refl (phase (s p).pc))

/-- No outcome means the original pending request persists; a restarted request
cannot stand in for it. Its finite control-stage measure never decreases. -/
theorem no_outcome_pending {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {start : Nat} (pending : Pending (r.state start) p)
    (never : ∀ t, start ≤ t → ¬ Outcome (r.state t) (r.command t) p) :
    ∀ t, start ≤ t → Pending (r.state t) p ∧
      phase (r.state t p).pc ≤ phase (r.state (t + 1) p).pc := by
  have persists : ∀ t, start ≤ t → Pending (r.state t) p := by
    intro t bound
    induction t, bound using Nat.le_induction with
    | base => exact pending
    | succ t bound ih => exact (next_pending_phase (r.wellFormed t p) ih (r.valid t) (never t bound)).1
  exact fun t bound => ⟨persists t bound,
    (next_pending_phase (r.wellFormed t p) (persists t bound) (r.valid t) (never t bound)).2⟩

theorem bounded_phase_stabilizes (f : Nat → Nat) (upper start : Nat)
    (bound : ∀ t, start ≤ t → f t ≤ upper)
    (mono : ∀ t, start ≤ t → f t ≤ f (t + 1)) :
    ∃ time, start ≤ time ∧ ∀ t, time ≤ t → f t = f time := by
  classical
  have hex : ∃ v, ∃ t, start ≤ t ∧ upper - f t = v := ⟨upper - f start, start, le_rfl, rfl⟩
  obtain ⟨time, lo, value⟩ := Nat.find_spec hex
  refine ⟨time, lo, ?_⟩
  intro t hi
  have lower : f time ≤ f t := by
    induction t, hi using Nat.le_induction with
    | base => exact le_rfl
    | succ t hi ih => exact ih.trans (mono t (by omega))
  have min := Nat.find_min' hex (show ∃ u, start ≤ u ∧ upper - f u = upper - f t from
    ⟨t, by omega, rfl⟩)
  have bt := bound t (by omega)
  have btime := bound time lo
  omega

/-- A concrete unreturned scan stays in that invocation until its first
returning instruction. This also applies to a suffix supplied mid-invocation. -/
theorem unreturned_scan_at {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {c : Continuation} {k start finish : Nat} {remaining : List (Leaf n)}
    (pc : (r.state start p).pc = .scan c k remaining) (bound : start ≤ finish)
    (noReturn : ∀ t, start ≤ t → t < finish → scanReturn (r.state t) (r.command t) p = none)
    (noFailure : ∀ t, start ≤ t → t < finish → r.command t ≠ .fail p) :
    ∃ rest, (r.state finish p).pc = .scan c k rest := by
  induction finish, bound using Nat.le_induction with
  | base => exact ⟨remaining, pc⟩
  | succ finish bound ih =>
    obtain ⟨rest, before⟩ := ih (fun t lo hi => noReturn t lo (by omega))
      (fun t lo hi => noFailure t lo (by omega))
    exact (open_scan_step (r.valid finish) before (noReturn finish bound (by omega))
      (noFailure finish bound (by omega))).1

theorem preparation_scan_grows {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {c : Continuation} {k start : Nat}
    {remaining : List (Leaf n)} (pc : (r.state start p).pc = .scan c k remaining)
    (preparation : c ≠ .wait)
    (noFailure : ∀ t, start ≤ t → r.command t ≠ .fail p) :
    ∃ finish, start ≤ finish ∧ phase (r.state start p).pc < phase (r.state finish p).pc := by
  obtain ⟨time, bound, returns | ⟨fail, _⟩⟩ := scan_first_outcome r fair pc
  · obtain ⟨value, returned⟩ := returns
    obtain ⟨rest, pcTime⟩ := unreturned_scan_at r pc bound returned.first
      (fun t lo _ => noFailure t lo)
    have nextEq := Option.some.inj ((scanReturn_step (cfg := cfg) pcTime returned.returns).symm.trans
      (r.valid time))
    refine ⟨time + 1, by omega, ?_⟩
    have strict := (resume_pending_phase cfg p c k value remaining).2.2 preparation
    simpa [pc, ← nextEq, setLocal] using strict
  · exact (noFailure time bound fail).elim

def simplePC {n : Nat} : PC n → Bool
  | .write1 _ _ | .self2 _ | .write2 _ _ | .pass _ => true
  | _ => false

theorem ordinary_simple_strict {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {l : Local n} (wf : LocalWF (s p))
    (simple : simplePC (s p).pc = true) (step : ordinary cfg p s = some l) :
    phase (s p).pc < phase l.pc := by
  have stage := wf.2.2
  cases pc : (s p).pc with
  | write1 k v | self2 k | write2 k v =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp [phase, scan]
  | pass k =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp only [StageWF, pc] at stage
    by_cases more : k < height n
    · simp [more, phase, scan]; omega
    · simp [more, phase]; omega
  | down | idle | scan | waitSelf | enter | cs | release =>
    simp [simplePC, pc] at simple

/-- A plateau cannot contain a first/second scan, a cached write, or a delayed
level pass/entry. Fair scheduling therefore puts it in an actual wait loop. -/
theorem stationary_phase_waiting {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (pending : Pending (r.state start) p)
    (never : ∀ t, start ≤ t → ¬ Outcome (r.state t) (r.command t) p)
    (stable : ∀ t, start ≤ t → phase (r.state t p).pc = phase (r.state start p).pc) :
    ∃ k, WaitingAt k (r.state start p).pc := by
  have noFailure : ∀ t, start ≤ t → r.command t ≠ .fail p := by
    intro t lo eq
    exact never t lo (Or.inr (by simp [label, eq]))
  have noPrep {c k rest} (pc : (r.state start p).pc = .scan c k rest) (prep : c ≠ .wait) : False := by
    obtain ⟨finish, bound, strict⟩ := preparation_scan_grows r fair pc prep noFailure
    rw [stable finish bound] at strict
    omega
  have noSimple (simple : simplePC (r.state start p).pc = true) : False := by
    obtain ⟨time, bound, act, same, _⟩ := first_scheduled_action r fair
      (p := p) (start := start) (by simp only [protocolPC, Bool.or_eq_true]; exact Or.inl pending)
    have run := act.resolve_right (noFailure time bound)
    have step := r.valid time
    simp only [run, next] at step
    cases ordinaryStep : ordinary cfg p (r.state time) with
    | none => simp [ordinaryStep] at step
    | some l =>
      have eq : r.state (time + 1) = setLocal (r.state time) p l := by
        simpa [ordinaryStep] using step.symm
      have strict := ordinary_simple_strict (r.wellFormed time p)
        (by simpa [same] using simple) ordinaryStep
      have after : phase (r.state (time + 1) p).pc = phase l.pc := by simp [eq, setLocal]
      rw [← after, stable (time + 1) (by omega), same] at strict
      omega
  cases pc : (r.state start p).pc with
  | down | idle | cs | release => simp [Pending, pendingPC, pc] at pending
  | scan c k rest =>
    cases c with
    | first => exact (noPrep pc (by decide)).elim
    | second => exact (noPrep pc (by decide)).elim
    | wait => exact ⟨k, Or.inl ⟨rest, rfl⟩⟩
  | waitSelf k x => exact ⟨k, Or.inr ⟨x, rfl⟩⟩
  | write1 | self2 | write2 | pass => exact (noSimple (by simp [simplePC, pc])).elim
  | enter =>
    obtain ⟨time, bound, act, same, _⟩ := first_scheduled_action r fair
      (p := p) (start := start) (by simp [protocolPC, pendingPC, pc])
    have run := act.resolve_right (noFailure time bound)
    exact (never time bound (Or.inl (by simp [label, run, same, pc]))).elim

/-- A stalled request has a single positive level and has finished both
assignments there. All remaining movement is concrete wait scans/own reads. -/
theorem pending_stabilizes_in_wait {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (pending : Pending (r.state start) p)
    (never : ∀ t, start ≤ t → ¬ Outcome (r.state t) (r.command t) p) :
    ∃ time k, start ≤ time ∧ 0 < k ∧ k ≤ height n ∧
      ∀ t, time ≤ t → WaitingAt k (r.state t p).pc := by
  have persists := no_outcome_pending r pending never
  obtain ⟨time, bound, stable⟩ := bounded_phase_stabilizes
    (fun t => phase (r.state t p).pc) (7 * height n) start
    (fun t _ => phase_bound (r.wellFormed t p)) (fun t lo => (persists t lo).2)
  have waiting : ∀ t, time ≤ t → ∃ k, WaitingAt k (r.state t p).pc := by
    intro t lo
    exact stationary_phase_waiting r fair (persists t (by omega)).1
      (fun u hu => never u (by omega))
      (fun u hu => (stable u (by omega)).trans (stable t lo).symm)
  obtain ⟨k, atTime⟩ := waiting time (le_refl _)
  have waitFacts {t k} (h : WaitingAt k (r.state t p).pc) :
      0 < k ∧ k ≤ height n ∧ phase (r.state t p).pc = 7 * (k - 1) + 5 := by
    have wf := (r.wellFormed t p).2.2
    rcases h with ⟨rest, pc⟩ | ⟨x, pc⟩ <;> simp only [StageWF, pc] at wf
    all_goals exact ⟨wf.1, wf.2.1, by simp [phase, pc]⟩
  have facts := waitFacts atTime
  refine ⟨time, k, bound, facts.1, facts.2.1, ?_⟩
  intro t lo
  obtain ⟨level, atT⟩ := waiting t lo
  have other := waitFacts atT
  have eq := stable t lo
  have same : level = k := by omega
  simpa [same] using atT

theorem next_wait_pair {n : Nat} {cfg : Config n} {s t : State n}
    {p : Proc n} {k : Nat} {c : Command n} (waiting : WaitingAt k (s p).pc)
    (step : next cfg s c = some t) (noFailure : c ≠ .fail p) : (t p).q = (s p).q := by
  by_cases own : c = .run p
  · subst c
    rcases waiting with ⟨rest, pc⟩ | ⟨x, pc⟩
    · cases rest with
      | nil =>
        have eq : t = setLocal s p {s p with pc := resume cfg p .wait k dead} := by
          simpa [next, ordinary, pc] using step.symm
        simp [eq, setLocal]
      | cons j rest =>
        have eq : t = setLocal s p {s p with pc :=
            if k ≤ (visible s j).level then resume cfg p .wait k (visible s j) else .scan .wait k rest} := by
          simpa [next, ordinary, pc] using step.symm
        simp [eq, setLocal]
    · have eq : t = setLocal s p {s p with pc :=
          if (Bool.xor (bit p.val k) (x == (s p).q)) then (scan cfg p .wait k) else .pass k} := by
        simpa [next, ordinary, pc] using step.symm
      simp [eq, setLocal]
  · have live : (s p).pc ≠ .down := by
      rcases waiting with ⟨rest, pc⟩ | ⟨x, pc⟩ <;> simp [pc]
    exact congrArg Local.q (next_live_unchanged step live (not_or.mpr ⟨own, noFailure⟩))

/-- The whole published pair is fixed on the eventual wait suffix. This is a
conclusion about an allegedly unserved original request, not a stability
assumption imposed on any peer or on the population. -/
theorem pending_stabilizes {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (pending : Pending (r.state start) p)
    (never : ∀ t, start ≤ t → ¬ Outcome (r.state t) (r.command t) p) :
    ∃ time k value, start ≤ time ∧ 0 < k ∧ k ≤ height n ∧ value.level = k ∧
      ∀ t, time ≤ t → WaitingAt k (r.state t p).pc ∧ (r.state t p).q = value := by
  obtain ⟨time, k, bound, positive, within, wait⟩ := pending_stabilizes_in_wait r fair pending never
  have level : (r.state time p).q.level = k := by
    have wf := (r.wellFormed time p).2.2
    rcases wait time (le_refl _) with ⟨rest, pc⟩ | ⟨x, pc⟩ <;> simp only [StageWF, pc] at wf
    · exact wf.2.2
    · exact wf.2.2.1
  refine ⟨time, k, (r.state time p).q, bound, positive, within, level, ?_⟩
  intro t lo
  refine ⟨wait t lo, ?_⟩
  induction t, lo using Nat.le_induction with
  | base => rfl
  | succ t lo ih =>
    have noFail : r.command t ≠ .fail p := by
      intro eq; exact never t (by omega) (Or.inr (by simp [label, eq]))
    exact (next_wait_pair (wait t lo) (r.valid t) noFail).trans ih

/-- Concrete safety supplies uniqueness at every scan level; it is not an
extra scheduling premise and includes changing physical representatives. -/
theorem Run.scan_unique {n : Nat} {cfg : Config n} (r : Run cfg)
    (p : Proc n) (k t : Nat) (positive : 0 < k) (within : k ≤ height n) :
    ScanBridge.Unique (cfg.order p k) k (visible (r.state t)) := by
  apply scan_unique_of_treeUnique k positive (r.wellFormed t)
  exact concrete_treeUnique r.initialized (fun u _ => r.valid u) (k - 1) (by omega) t (le_refl _)

/-- A full scan against a permanently published representative returns that
exact whole pair, or the scanner fails. The observation is derived from the
real invocation, including an arbitrary enumeration and all stale-read cases. -/
theorem scan_against_stable_opponent {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p q : Proc n} {c : Continuation}
    {k start : Nat} {value : Value}
    (pc : (r.state start q).pc = .scan c k (cfg.order q k))
    (opponent : Opponent q.val p.val k)
    (positive : 0 < k) (within : k ≤ height n) (active : k ≤ value.level)
    (stable : ∀ t, start ≤ t → (r.state t p).q = value) :
    ∃ finish, start ≤ finish ∧
      (FirstScanReturn r.state r.command q start finish value ∨
        (r.command finish = .fail q ∧
          ∀ t, start ≤ t → t < finish →
            scanReturn (r.state t) (r.command t) q = none ∧ r.command t ≠ .fail q)) := by
  obtain ⟨finish, bound, returned | failed⟩ := scan_first_outcome r fair pc
  · obtain ⟨result, ending⟩ := returned
    have openScan : OpenScan cfg r.state r.command q c k start finish :=
      ⟨bound, pc, ending.first, fun t lo hi => ending.noAbort t lo (by omega)⟩
    obtain ⟨time, lo, hi, observed⟩ := open_scan_return_observation openScan positive
      (fun u _ => r.valid u) ending.returns
      (fun t _ _ => r.scan_unique q k t positive within)
    let leaf : Leaf n := ⟨p.val, Nat.lt_of_lt_of_le p.isLt (real_fits_padding n)⟩
    have member : leaf ∈ cfg.order q k := (cfg.complete q k leaf).mpr opponent
    have visibleP : visible (r.state time) leaf = value :=
      (real_visible (r.state time) p).trans (stable time lo)
    have eq : result = value := by
      rcases observed with ⟨_, absent⟩ | ⟨j, memberJ, high, resultJ⟩
      · have low := absent leaf member
        rw [visibleP] at low
        omega
      · have same := r.scan_unique q k time positive within j memberJ leaf member high
          (by simpa [visibleP] using active)
        exact resultJ.trans (same ▸ visibleP)
    exact ⟨finish, bound, Or.inl (eq ▸ ending)⟩
  · exact ⟨finish, bound, Or.inr failed⟩

theorem waiting_not_pass {n : Nat} {k m : Nat} : ¬ WaitingAt k (PC.pass m : PC n) := by
  simp [WaitingAt]

theorem waiting_no_failure {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {k start : Nat} (wait : ∀ t, start ≤ t → WaitingAt k (r.state t p).pc) :
    ∀ t, start ≤ t → r.command t ≠ .fail p := by
  intro t lo fail
  have live : (r.state t p).pc ≠ .down := by
    rcases wait t lo with ⟨rest, pc⟩ | ⟨x, pc⟩ <;> simp [pc]
  have eq : r.state (t + 1) = setLocal (r.state t) p ⟨.down, dead⟩ := by
    simpa [fail, next, live] using (r.valid t).symm
  have after := wait (t + 1) (by omega)
  simp [eq, setLocal, WaitingAt] at after

theorem waitSelf_eventually_full_scan {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {k start : Nat} {x : Value}
    (pc : (r.state start p).pc = .waitSelf k x)
    (wait : ∀ t, start ≤ t → WaitingAt k (r.state t p).pc) :
    ∃ finish, start ≤ finish ∧ (r.state finish p).pc = scan cfg p .wait k := by
  obtain ⟨time, lo, act, same, _⟩ := first_scheduled_action r fair
    (p := p) (start := start) (by simp [protocolPC, pendingPC, pc])
  have run := act.resolve_right (waiting_no_failure r wait time lo)
  have eq : r.state (time + 1) = setLocal (r.state time) p {r.state time p with pc :=
      if (Bool.xor (bit p.val k) (x == (r.state time p).q)) then (scan cfg p .wait k) else .pass k} := by
    simpa [run, next, ordinary, same, pc] using (r.valid time).symm
  by_cases blocked : Bool.xor (bit p.val k) (x == (r.state time p).q) = true
  · exact ⟨time + 1, by omega, by simp [eq, setLocal, blocked]⟩
  · have after := wait (time + 1) (by omega)
    simp [eq, setLocal, blocked, WaitingAt] at after

/-- An infinite wait suffix repeatedly begins fresh full scans. This is
stronger than counting arbitrary instructions or assuming favorable reads. -/
theorem wait_eventually_full_scan {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {k start : Nat}
    (wait : ∀ t, start ≤ t → WaitingAt k (r.state t p).pc) :
    ∃ finish, start ≤ finish ∧ (r.state finish p).pc = scan cfg p .wait k := by
  rcases wait start (le_refl _) with ⟨rest, pc⟩ | ⟨x, pc⟩
  · obtain ⟨time, lo, returned | ⟨fail, _⟩⟩ := scan_first_outcome r fair pc
    · obtain ⟨value, ending⟩ := returned
      obtain ⟨suffix, pcTime⟩ := unreturned_scan_at r pc lo ending.first
        (fun t ht _ => ending.noAbort t ht (by omega))
      have eq := Option.some.inj ((scanReturn_step (cfg := cfg) pcTime ending.returns).symm.trans
        (r.valid time))
      have afterPC : (r.state (time + 1) p).pc = resume cfg p .wait k value := by
        simp [← eq, setLocal]
      by_cases high : k < value.level
      · exact ⟨time + 1, by omega, by simpa [resume, high] using afterPC⟩
      · by_cases low : value.level < k
        · have after := wait (time + 1) (by omega)
          simp [afterPC, resume, high, low, WaitingAt] at after
        · have self : (r.state (time + 1) p).pc = .waitSelf k value := by
            simpa [resume, high, low] using afterPC
          obtain ⟨finish, bound, full⟩ := waitSelf_eventually_full_scan r fair self
            (fun t ht => wait t (by omega))
          exact ⟨finish, by omega, full⟩
    · exact (waiting_no_failure r wait time lo fail).elim
  · exact waitSelf_eventually_full_scan r fair pc wait

/-- If two published representatives persist at one level and one waits
forever, its role's actual comparison must be unfavorable. Fresh scans and
own reads establish this; a stale cached observation is never assumed fresh. -/
theorem permanent_wait_guard {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p q : Proc n} {k start : Nat} {own peer : Value}
    (positive : 0 < k) (within : k ≤ height n)
    (opponent : Opponent p.val q.val k) (ownLevel : own.level = k) (peerLevel : peer.level = k)
    (wait : ∀ t, start ≤ t → WaitingAt k (r.state t p).pc)
    (ownStable : ∀ t, start ≤ t → (r.state t p).q = own)
    (peerStable : ∀ t, start ≤ t → (r.state t q).q = peer) :
    Bool.xor (bit p.val k) (peer == own) = true := by
  obtain ⟨scanTime, scanBound, full⟩ := wait_eventually_full_scan r fair wait
  obtain ⟨returnTime, returnBound, returned | ⟨fail, _⟩⟩ :=
    scan_against_stable_opponent r fair full opponent positive within (by omega)
      (fun t ht => peerStable t (by omega))
  · obtain ⟨rest, pcReturn⟩ := unreturned_scan_at r full returnBound returned.first
      (fun t lo hi => returned.noAbort t lo (by omega))
    have eq := Option.some.inj ((scanReturn_step (cfg := cfg) pcReturn returned.returns).symm.trans
      (r.valid returnTime))
    have self : (r.state (returnTime + 1) p).pc = .waitSelf k peer := by
      simp [← eq, setLocal, resume, peerLevel]
    obtain ⟨time, bound, act, same, _⟩ := first_scheduled_action r fair
      (p := p) (start := returnTime + 1) (by simp [protocolPC, pendingPC, self])
    have run := act.resolve_right (waiting_no_failure r wait time (by omega))
    have qeq := ownStable time (by omega)
    have after : (r.state (time + 1) p).pc =
        if Bool.xor (bit p.val k) (peer == own) then scan cfg p .wait k else .pass k := by
      have step := r.valid time
      have pre : (r.state time p).pc = .waitSelf k peer := by rw [same]; exact self
      simp only [run, next, ordinary, pre, qeq, Option.map_some, Option.some.injEq] at step
      simp [← step, setLocal]
    by_contra blocked
    have later := wait (time + 1) (by omega)
    simp [after, blocked, WaitingAt] at later
  · exact (waiting_no_failure r wait returnTime (by omega) fail).elim

/-- Two fixed non-failing opponents cannot both remain stuck at the same
level: their role bits are opposite and their whole-pair equality is symmetric. -/
theorem no_permanent_opposing_waiters {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p q : Proc n} {k start : Nat} {left right : Value}
    (positive : 0 < k) (within : k ≤ height n) (opponent : Opponent p.val q.val k)
    (leftLevel : left.level = k) (rightLevel : right.level = k)
    (pwait : ∀ t, start ≤ t → WaitingAt k (r.state t p).pc)
    (qwait : ∀ t, start ≤ t → WaitingAt k (r.state t q).pc)
    (pstable : ∀ t, start ≤ t → (r.state t p).q = left)
    (qstable : ∀ t, start ≤ t → (r.state t q).q = right) : False := by
  have h1 := permanent_wait_guard r fair positive within opponent leftLevel rightLevel pwait pstable qstable
  have opposite : Opponent q.val p.val k := ⟨opponent.1.symm, Ne.symm opponent.2⟩
  have h2 := permanent_wait_guard r fair positive within opposite rightLevel leftLevel qwait qstable pstable
  have bits := opponent.2
  have equal : (left == right) = (right == left) := by
    by_cases eq : left = right <;> simp [eq, Ne.symm]
  rw [equal] at h2
  cases bp : bit p.val k <;> cases bq : bit q.val k <;>
    cases eq : (right == left) <;> simp_all

/-- A scan observed after an inactive state cannot have begun before that
state. The actual no-return/no-abort history rules out an old cached scan. -/
theorem return_after_inactive_is_stable {n : Nat} {cfg : Config n} (r : Run cfg)
    {p q : Proc n} {c : Continuation} {k start now : Nat} {value result : Value}
    {remaining : List (Leaf n)} (bound : start ≤ now)
    (inactive : (r.state start q).pc = .idle ∨ (r.state start q).pc = .down)
    (pc : (r.state now q).pc = .scan c k remaining)
    (returned : scanReturn (r.state now) (r.command now) q = some result)
    (opponent : Opponent q.val p.val k)
    (positive : 0 < k) (within : k ≤ height n) (active : k ≤ value.level)
    (stable : ∀ t, start ≤ t → (r.state t p).q = value) : result = value := by
  obtain ⟨begin, opened⟩ := concrete_open_scan r.initialized (fun t _ => r.valid t) q c k remaining pc
  have beganAfter : start ≤ begin := by
    by_contra earlier
    obtain ⟨⟨rest, atStart⟩, _⟩ := opened.at (fun t _ => r.valid t) start (by omega) bound
    rcases inactive with idle | down <;> simp_all
  obtain ⟨time, lo, hi, observed⟩ := open_scan_return_observation opened positive
    (fun t _ => r.valid t) returned (fun t _ _ => r.scan_unique q k t positive within)
  let leaf : Leaf n := ⟨p.val, Nat.lt_of_lt_of_le p.isLt (real_fits_padding n)⟩
  have member : leaf ∈ cfg.order q k := (cfg.complete q k leaf).mpr opponent
  have visibleP : visible (r.state time) leaf = value :=
    (real_visible (r.state time) p).trans (stable time (by omega))
  rcases observed with ⟨_, absent⟩ | ⟨j, memberJ, high, resultJ⟩
  · have low := absent leaf member
    rw [visibleP] at low
    omega
  · have same := r.scan_unique q k time positive within j memberJ leaf member high
      (by simpa [visibleP] using active)
    exact resultJ.trans (same ▸ visibleP)

/-- A fresh representative adopts a pair that makes its own test wait against
the permanent opposing pair. This is the source's complementary role rule. -/
theorem matching_waits {n : Nat} (p : Proc n) (k : Nat) (value : Value)
    (level : value.level = k) :
    Bool.xor (bit p.val k) (value == matching p k value) = true := by
  rcases value with ⟨m, flag⟩
  dsimp at level
  subst m
  cases flag <;> cases b : bit p.val k <;> simp [matching, b]

def FreshCache {n : Nat} (p : Proc n) (k : Nat) (peer : Value) : PC n → Prop
  | .write1 m v | .write2 m v => m = k → v = matching p k peer
  | .waitSelf m x => m = k → x = peer
  | _ => True

/-- After this process has reset in the presence of a permanent opponent,
it cannot pass that opponent's level and every publication there defers to it.
The predicate also tracks pending cached writes and wait samples. -/
def FreshBelow {n : Nat} (p : Proc n) (k : Nat) (peer : Value) (l : Local n) : Prop :=
  passedLevel l < k ∧ (l.q.level = k → l.q = matching p k peer) ∧ FreshCache p k peer l.pc

theorem fresh_inactive {n : Nat} (p : Proc n) (k : Nat) (peer : Value) (positive : 0 < k)
    (l : Local n) (wf : LocalWF l) (inactive : l.pc = .idle ∨ l.pc = .down) :
    FreshBelow p k peer l := by
  have stage := wf.2.2
  rcases inactive with pc | pc <;> simp only [StageWF, pc] at stage
  all_goals simp [FreshBelow, FreshCache, passedLevel, pc, stage, dead, ScanBridge.dead, Ne.symm (Nat.ne_of_gt positive), positive]

/-- One returned scan preserves the fresh-attempt invariant. At the critical
level its actual result is the permanent opponent's pair, never an assumed
atomic snapshot or a favorable scheduler choice. -/
theorem fresh_resume {n : Nat} (cfg : Config n) (p : Proc n)
    (k m : Nat) (c : Continuation) (q peer x : Value) (rest : List (Leaf n))
    (_wf : LocalWF (⟨.scan c m rest, q⟩ : Local n))
    (fresh : FreshBelow p k peer ⟨.scan c m rest, q⟩)
    (sample : m = k → x = peer) (peerLevel : peer.level = k) :
    FreshBelow p k peer ⟨resume cfg p c m x, q⟩ := by
  obtain ⟨passed, pair, _⟩ := fresh
  change m - 1 < k at passed
  change q.level = k → q = matching p k peer at pair
  have mBound : m ≤ k := by
    omega
  by_cases same : m = k
  · subst m
    have sampleEq := sample rfl
    subst x
    cases c <;> simp [resume, peerLevel, FreshBelow, FreshCache, passedLevel, passed]
    all_goals exact pair
  · have less : m < k := by omega
    cases c with
    | first => exact ⟨passed, pair, fun eq => (same eq).elim⟩
    | second =>
      simp only [resume]
      split
      · exact ⟨passed, pair, fun eq => (same eq).elim⟩
      · exact ⟨passed, pair, trivial⟩
    | wait =>
      simp only [resume]
      split
      · exact ⟨passed, pair, trivial⟩
      · split
        · exact ⟨less, pair, trivial⟩
        · exact ⟨passed, pair, fun eq => (same eq).elim⟩

theorem ordinary_fresh {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {k : Nat} {peer : Value} {l : Local n} (positive : 0 < k) (within : k ≤ height n)
    (peerLevel : peer.level = k) (wf : LocalWF (s p)) (fresh : FreshBelow p k peer (s p))
    (step : ordinary cfg p s = some l)
    (samples : ∀ c rest x, (s p).pc = .scan c k rest →
      scanReturn s (.run p) p = some x → x = peer) : FreshBelow p k peer l := by
  obtain ⟨passed, pair, cache⟩ := fresh
  have stage := wf.2.2
  cases pc : (s p).pc with
  | down => simp [ordinary, pc] at step
  | enter | cs | release => simp [passedLevel, pc] at passed; omega
  | idle =>
    have nonzero : height n ≠ 0 := by omega
    have qdead : (s p).q = dead := by simpa [StageWF, pc] using stage
    simp only [ordinary, pc, nonzero, ite_false, Option.some.injEq] at step
    subst l
    simp [FreshBelow, FreshCache, passedLevel, scan, qdead, dead, ScanBridge.dead,
      positive, Ne.symm (Nat.ne_of_gt positive)]
  | scan c m rest =>
    have wf' : LocalWF (⟨.scan c m rest, (s p).q⟩ : Local n) := by
      simpa [LocalWF, StageWF, pc] using wf
    have fresh' : FreshBelow p k peer (⟨.scan c m rest, (s p).q⟩ : Local n) :=
      ⟨by simpa [passedLevel, pc] using passed, pair, trivial⟩
    cases rest with
    | nil =>
      simp only [ordinary, pc, Option.some.injEq] at step
      subst l
      apply fresh_resume cfg p k m c (s p).q peer dead [] wf' fresh' _ peerLevel
      intro eq; subst m
      exact samples c [] dead pc (by simp [scanReturn, pc])
    | cons j rest =>
      by_cases high : m ≤ (visible s j).level
      · simp only [ordinary, pc, high, ite_true, Option.some.injEq] at step
        subst l
        apply fresh_resume cfg p k m c (s p).q peer (visible s j) (j :: rest) wf' fresh' _ peerLevel
        intro eq; subst m
        exact samples c (j :: rest) (visible s j) pc (by simp [scanReturn, pc, high])
      · simp only [ordinary, pc, high, ite_false, Option.some.injEq] at step
        subst l
        exact ⟨by simpa [passedLevel, pc] using passed, pair, trivial⟩
  | write1 m v =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp only [StageWF, pc] at stage
    have cached : m = k → v = matching p k peer := by simpa [FreshCache, pc] using cache
    refine ⟨by simpa [passedLevel, pc, scan] using passed, ?_, trivial⟩
    intro eq
    exact cached (stage.2.2.2.symm.trans eq)
  | self2 m =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp only [StageWF, pc] at stage
    refine ⟨by simpa [passedLevel, pc] using passed, pair, ?_⟩
    intro eq
    exact pair (stage.2.2.trans eq)
  | write2 m v =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    simp only [StageWF, pc] at stage
    have cached : m = k → v = matching p k peer := by simpa [FreshCache, pc] using cache
    refine ⟨by simpa [passedLevel, pc, scan] using passed, ?_, trivial⟩
    intro eq
    exact cached (stage.2.2.2.symm.trans eq)
  | waitSelf m x =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    by_cases same : m = k
    · subst m
      have sample : x = peer := by simpa [FreshCache, pc] using cache
      have ownLevel : (s p).q.level = k := by
        simp only [StageWF, pc] at stage
        exact stage.2.2.1
      have blocked : Bool.xor (bit p.val k) (x == (s p).q) = true := by
        rw [sample, pair ownLevel]
        exact matching_waits p k peer peerLevel
      simp only [blocked, ite_true]
      exact ⟨by simpa [passedLevel, pc, scan] using passed, pair, trivial⟩
    · have less : m < k := by simp only [passedLevel, pc] at passed; omega
      split
      · exact ⟨by simpa [passedLevel, pc, scan] using passed, pair, trivial⟩
      · exact ⟨less, pair, trivial⟩
  | pass m =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    have less : m < k := by simpa [passedLevel, pc] using passed
    have more : m < height n := by omega
    simp only [more, ite_true]
    exact ⟨by simpa [passedLevel, scan] using less, pair, trivial⟩

/-- Once this opponent has become idle/down after the other pair stabilized,
all its subsequent attempts defer at that level, including infinitely many
failures/restarts and arbitrarily delayed cached writes. -/
theorem fresh_after_inactive {n : Nat} {cfg : Config n} (r : Run cfg)
    {p q : Proc n} {k start : Nat} {peer : Value}
    (positive : 0 < k) (within : k ≤ height n) (peerLevel : peer.level = k)
    (opponent : Opponent q.val p.val k)
    (inactive : (r.state start q).pc = .idle ∨ (r.state start q).pc = .down)
    (stable : ∀ t, start ≤ t → (r.state t p).q = peer) :
    ∀ t, start ≤ t → FreshBelow q k peer (r.state t q) := by
  intro t lo
  induction t, lo using Nat.le_induction with
  | base => exact fresh_inactive q k peer positive (r.state start q) (r.wellFormed start q) inactive
  | succ t lo ih =>
    have step := r.valid t
    by_cases run : r.command t = .run q
    · simp only [run, next] at step
      cases ordinaryStep : ordinary cfg q (r.state t) with
      | none => simp [ordinaryStep] at step
      | some l =>
        have after : r.state (t + 1) q = l := by
          have eq : r.state (t + 1) = setLocal (r.state t) q l := by simpa [ordinaryStep] using step.symm
          simp [eq, setLocal]
        rw [after]
        apply ordinary_fresh positive within peerLevel (r.wellFormed t q) ih ordinaryStep
        intro c rest value pc returned
        apply return_after_inactive_is_stable r lo inactive pc _ opponent positive within (by omega) stable
        simpa [run] using returned
    · by_cases fail : r.command t = .fail q
      · have down : (r.state (t + 1) q).pc = .down := by
          simp only [fail, next] at step
          split at step
          · simp at step
          · simp [← Option.some.inj step, setLocal]
        exact fresh_inactive q k peer positive (r.state (t + 1) q) (r.wellFormed (t + 1) q) (Or.inr down)
      · by_cases restart : r.command t = .restart q
        · have idle : (r.state (t + 1) q).pc = .idle := by
            simp only [restart, next] at step
            split at step
            · simp [← Option.some.inj step, setLocal]
            · simp at step
          exact fresh_inactive q k peer positive (r.state (t + 1) q) (r.wellFormed (t + 1) q) (Or.inl idle)
        · simpa [next_other_local q step run fail restart] using ih

def Inactive {n : Nat} (s : State n) (p : Proc n) : Prop :=
  (s p).pc = .idle ∨ (s p).pc = .down

theorem fail_becomes_inactive {n : Nat} {cfg : Config n} {s t : State n}
    {p : Proc n} (step : next cfg s (.fail p) = some t) : Inactive t p := by
  simp only [next] at step
  split at step
  · simp at step
  · exact Or.inr (by simp [← Option.some.inj step, setLocal])

theorem release_eventually_inactive {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (pc : (r.state start p).pc = .release) : ∃ t, start ≤ t ∧ Inactive (r.state t) p := by
  obtain ⟨time, bound, act, same, _⟩ := first_scheduled_action r fair
    (p := p) (start := start) (by simp [protocolPC, pc])
  refine ⟨time + 1, by omega, ?_⟩
  rcases act with run | fail
  · have step := r.valid time
    simp only [run, next, ordinary, same, pc, Option.map_some, Option.some.injEq] at step
    exact Or.inl (by simp [← step, setLocal])
  · exact fail_becomes_inactive (fail ▸ r.valid time)

theorem event_fail_command {n : Nat} (s : State n) (c : Command n) (p : Proc n)
    (event : label s c = .fail p) : c = .fail p := by
  cases c with
  | run q => cases pc : (s q).pc <;> simp [label, pc] at event
  | fail q => simpa [label] using event
  | restart | stutter => simp [label] at event

theorem event_complete_local {n : Nat} (s : State n) (c : Command n) (p : Proc n)
    (event : label s c = .complete p) : c = .run p ∧ (s p).pc = .cs := by
  cases c with
  | run q =>
    cases pc : (s q).pc <;> simp only [label, pc] at event
    all_goals try contradiction
    have eq : q = p := Label.complete.inj event
    subst q
    exact ⟨rfl, pc⟩
  | fail | restart | stutter => simp [label] at event

theorem event_entry_local {n : Nat} (s : State n) (c : Command n) (p : Proc n)
    (event : label s c = .entry p) : c = .run p ∧ (s p).pc = .enter := by
  cases c with
  | run q =>
    cases pc : (s q).pc <;> simp only [label, pc] at event
    all_goals try contradiction
    have eq : q = p := Label.entry.inj event
    subst q
    exact ⟨rfl, pc⟩
  | fail | restart | stutter => simp [label] at event

theorem critical_eventually_inactive {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (complete : CriticalCompletion r) {p : Proc n} {start : Nat}
    (pc : (r.state start p).pc = .cs) : ∃ t, start ≤ t ∧ Inactive (r.state t) p := by
  obtain ⟨time, bound, completion | failure⟩ := complete start p pc
  · obtain ⟨run, atCS⟩ := event_complete_local _ _ _ completion
    have step := r.valid time
    simp only [run, next, ordinary, atCS, Option.map_some, Option.some.injEq] at step
    have release : (r.state (time + 1) p).pc = .release := by simp [← step, setLocal]
    obtain ⟨finish, after, inactive⟩ := release_eventually_inactive r fair release
    exact ⟨finish, by omega, inactive⟩
  · have fail := event_fail_command _ _ _ failure
    exact ⟨time + 1, by omega, fail_becomes_inactive (fail ▸ r.valid time)⟩

theorem entry_eventually_inactive {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (complete : CriticalCompletion r) {p : Proc n} {start : Nat}
    (entry : r.event start = .entry p) : ∃ t, start ≤ t ∧ Inactive (r.state t) p := by
  obtain ⟨run, atEnter⟩ := event_entry_local _ _ _ entry
  have step := r.valid start
  simp only [run, next, ordinary, atEnter, Option.map_some, Option.some.injEq] at step
  have cs : (r.state (start + 1) p).pc = .cs := by simp [← step, setLocal]
  obtain ⟨finish, bound, inactive⟩ := critical_eventually_inactive r fair complete cs
  exact ⟨finish, by omega, inactive⟩

/-- A process that never again becomes inactive is an actual permanently
pending request. Real critical completion and scheduled release rule out an
unreleased critical occupant without assuming any per-node completion. -/
theorem never_inactive_stabilizes {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (complete : CriticalCompletion r) {p : Proc n} {start : Nat}
    (active : ∀ t, start ≤ t → ¬ Inactive (r.state t) p) :
    ∃ time k value, start ≤ time ∧ 0 < k ∧ k ≤ height n ∧ value.level = k ∧
      ∀ t, time ≤ t → WaitingAt k (r.state t p).pc ∧ (r.state t p).q = value := by
  have noOutcome : ∀ t, start ≤ t → ¬ Outcome (r.state t) (r.command t) p := by
    intro t lo event
    rcases event with entry | failure
    · obtain ⟨finish, bound, inactive⟩ := entry_eventually_inactive r fair complete entry
      exact active finish (by omega) inactive
    · have fail := event_fail_command _ _ _ failure
      exact active (t + 1) (by omega) (fail_becomes_inactive (fail ▸ r.valid t))
  have pending : Pending (r.state start) p := by
    cases pc : (r.state start p).pc
    all_goals try (simp [Pending, pendingPC, pc])
    case idle => exact (active start (le_refl _) (Or.inl pc)).elim
    case down => exact (active start (le_refl _) (Or.inr pc)).elim
    case cs =>
      obtain ⟨t, bound, inactive⟩ := critical_eventually_inactive r fair complete pc
      exact (active t bound inactive).elim
    case release =>
      obtain ⟨t, bound, inactive⟩ := release_eventually_inactive r fair pc
      exact (active t bound inactive).elim
  exact pending_stabilizes r fair pending noOutcome

/-- The alleged locked-out requests, with their concrete stable suffixes.
This is a contradiction witness, not an assumption on an admissible run. -/
def StuckLevel {n : Nat} {cfg : Config n} (r : Run cfg) (k : Nat) : Prop :=
  0 < k ∧ k ≤ height n ∧ ∃ p start value, value.level = k ∧
    ∀ t, start ≤ t → WaitingAt k (r.state t p).pc ∧ (r.state t p).q = value

theorem highest_stuck_level {n : Nat} {cfg : Config n} (r : Run cfg)
    (existsStuck : ∃ k, StuckLevel r k) :
    ∃ k, StuckLevel r k ∧ ∀ j, StuckLevel r j → j ≤ k := by
  classical
  have hex : ∃ d, ∃ k, StuckLevel r k ∧ height n - k = d := by
    obtain ⟨k, h⟩ := existsStuck
    exact ⟨height n - k, k, h, rfl⟩
  obtain ⟨k, stuck, eq⟩ := Nat.find_spec hex
  refine ⟨k, stuck, ?_⟩
  intro j hj
  have min := Nat.find_min' hex (show ∃ a, StuckLevel r a ∧ height n - a = height n - j from
    ⟨j, hj, rfl⟩)
  have kb := stuck.2.1
  have jb := hj.2.1
  omega

/-- Every old opposing attempt eventually stops obstructing a highest stuck
request. An inactive occurrence starts the checked fresh-attempt invariant;
a never-resetting attempt stabilizes strictly below the chosen highest level. -/
theorem opponent_eventually_defers {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (complete : CriticalCompletion r)
    {p q : Proc n} {k start : Nat} {value : Value}
    (positive : 0 < k) (within : k ≤ height n) (level : value.level = k)
    (wait : ∀ t, start ≤ t → WaitingAt k (r.state t p).pc)
    (stable : ∀ t, start ≤ t → (r.state t p).q = value)
    (highest : ∀ j, StuckLevel r j → j ≤ k) (opponent : Opponent p.val q.val k) :
    ∃ time, start ≤ time ∧ ∀ t, time ≤ t →
      (r.state t q).q.level < k ∨ (r.state t q).q = matching q k value := by
  classical
  by_cases resets : ∃ time, start ≤ time ∧ Inactive (r.state time) q
  · obtain ⟨time, bound, inactive⟩ := resets
    have fresh := fresh_after_inactive r positive within level ⟨opponent.1.symm, Ne.symm opponent.2⟩
      inactive (fun t lo => stable t (by omega))
    refine ⟨time, bound, ?_⟩
    intro t lo
    have h := fresh t lo
    have passed := h.1
    have levels := localWF_levels (r.wellFormed t q)
    by_cases equal : (r.state t q).q.level = k
    · exact Or.inr (h.2.1 equal)
    · exact Or.inl (by omega)
  · have active : ∀ t, start ≤ t → ¬ Inactive (r.state t) q := by
      intro t lo inactive
      exact resets ⟨t, lo, inactive⟩
    obtain ⟨time, j, peer, bound, posJ, withinJ, levelJ, stuck⟩ :=
      never_inactive_stabilizes r fair complete active
    have atMost := highest j ⟨posJ, withinJ, q, time, peer, levelJ, stuck⟩
    have notSame : j ≠ k := by
      intro eq
      rw [eq] at levelJ stuck
      exact no_permanent_opposing_waiters r fair positive within opponent level levelJ
        (fun t lo => wait t (by omega)) (fun t lo => (stuck t lo).1)
        (fun t lo => stable t (by omega)) (fun t lo => (stuck t lo).2)
    refine ⟨time, bound, ?_⟩
    intro t lo
    left
    rw [(stuck t lo).2, levelJ]
    omega

theorem opponents_eventually_defer {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (complete : CriticalCompletion r)
    {p : Proc n} {k start : Nat} {value : Value}
    (positive : 0 < k) (within : k ≤ height n) (level : value.level = k)
    (wait : ∀ t, start ≤ t → WaitingAt k (r.state t p).pc)
    (stable : ∀ t, start ≤ t → (r.state t p).q = value)
    (highest : ∀ j, StuckLevel r j → j ≤ k) :
    ∃ time, start ≤ time ∧ ∀ q t, Opponent p.val q.val k → time ≤ t →
      (r.state t q).q.level < k ∨ (r.state t q).q = matching q k value := by
  classical
  have each (q : Proc n) : ∃ time, start ≤ time ∧ ∀ t, time ≤ t →
      Opponent p.val q.val k →
        (r.state t q).q.level < k ∨ (r.state t q).q = matching q k value := by
    by_cases opp : Opponent p.val q.val k
    · obtain ⟨time, bound, after⟩ := opponent_eventually_defers r fair complete
        positive within level wait stable highest opp
      exact ⟨time, bound, fun t lo _ => after t lo⟩
    · exact ⟨start, le_refl _, fun _ _ h => (opp h).elim⟩
  let times : Proc n → Nat := fun q => Nat.find (each q)
  let common := max start (Finset.univ.sup times)
  refine ⟨common, le_max_left _ _, ?_⟩
  intro q t opp lo
  have bound : times q ≤ common :=
    (Finset.le_sup (f := times) (Finset.mem_univ q)).trans (le_max_right _ _)
  change Nat.find (each q) ≤ common at bound
  exact (Nat.find_spec (each q)).2 t (bound.trans lo) opp

theorem opposing_matching_passes {n : Nat} (p q : Proc n) (k : Nat) (value : Value)
    (level : value.level = k) (bits : bit q.val k ≠ bit p.val k) :
    Bool.xor (bit p.val k) (matching q k value == value) = false := by
  rcases value with ⟨m, flag⟩
  dsimp at level
  subst m
  cases flag <;> cases bp : bit p.val k <;> cases bq : bit q.val k <;>
    simp_all [matching]

/-- Once every real opponent defers, an actual fresh full scan returns a
passing sample. Padded leaves remain dead; no observation fairness is used. -/
theorem deferred_scan_result {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {k start finish : Nat} {value result : Value}
    (positive : 0 < k) (within : k ≤ height n) (level : value.level = k)
    (pc : (r.state start p).pc = scan cfg p .wait k)
    (ending : FirstScanReturn r.state r.command p start finish result)
    (defer : ∀ q t, Opponent p.val q.val k → start ≤ t →
      (r.state t q).q.level < k ∨ (r.state t q).q = matching q k value) :
    result.level < k ∨
      (result.level = k ∧ Bool.xor (bit p.val k) (result == value) = false) := by
  have opened : OpenScan cfg r.state r.command p .wait k start finish :=
    ⟨ending.ordered, pc, ending.first, fun t lo hi => ending.noAbort t lo (by omega)⟩
  obtain ⟨time, lo, _, observed⟩ := open_scan_return_observation opened positive
    (fun t _ => r.valid t) ending.returns (fun t _ _ => r.scan_unique p k t positive within)
  rcases observed with ⟨deadEq, _⟩ | ⟨j, member, high, eq⟩
  · left
    simpa [deadEq, ScanBridge.dead] using positive
  · have real : j.val < n := by
      by_contra dummy
      simp [visible, dummy, dead, ScanBridge.dead] at high
      omega
    let q : Proc n := ⟨j.val, real⟩
    have visibleQ : visible (r.state time) j = (r.state time q).q := by simp [visible, real, q]
    have opponent : Opponent p.val q.val k := (cfg.complete p k j).mp member
    rcases defer q time opponent lo with low | pair
    · rw [visibleQ] at high
      omega
    · right
      have resultEq : result = matching q k value := eq.trans (visibleQ.trans pair)
      refine ⟨by simp [resultEq, matching], ?_⟩
      rw [resultEq]
      exact opposing_matching_passes p q k value level opponent.2

/-- The concrete wait loop cannot last forever once every opponent has a
permanently deferring pair or remains below its level. -/
theorem no_wait_with_deferred_opponents {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {k start : Nat} {value : Value}
    (positive : 0 < k) (within : k ≤ height n) (level : value.level = k)
    (wait : ∀ t, start ≤ t → WaitingAt k (r.state t p).pc)
    (stable : ∀ t, start ≤ t → (r.state t p).q = value)
    (defer : ∀ q t, Opponent p.val q.val k → start ≤ t →
      (r.state t q).q.level < k ∨ (r.state t q).q = matching q k value) : False := by
  obtain ⟨scanTime, scanBound, full⟩ := wait_eventually_full_scan r fair wait
  obtain ⟨returnTime, returnBound, returned | ⟨fail, _⟩⟩ := scan_first_outcome r fair full
  · obtain ⟨result, ending⟩ := returned
    have favorable := deferred_scan_result r positive within level full ending
      (fun q t opp lo => defer q t opp (by omega))
    obtain ⟨rest, pcReturn⟩ := unreturned_scan_at r full returnBound ending.first
      (fun t lo hi => ending.noAbort t lo (by omega))
    have eq := Option.some.inj ((scanReturn_step (cfg := cfg) pcReturn ending.returns).symm.trans
      (r.valid returnTime))
    have afterPC : (r.state (returnTime + 1) p).pc = resume cfg p .wait k result := by
      simp [← eq, setLocal]
    rcases favorable with low | ⟨equal, passes⟩
    · have after := wait (returnTime + 1) (by omega)
      have notHigh : ¬ k < result.level := by omega
      simp [afterPC, resume, low, notHigh, WaitingAt] at after
    · have self : (r.state (returnTime + 1) p).pc = .waitSelf k result := by
        simpa [resume, equal] using afterPC
      obtain ⟨time, bound, act, same, _⟩ := first_scheduled_action r fair
        (p := p) (start := returnTime + 1) (by simp [protocolPC, pendingPC, self])
      have run := act.resolve_right (waiting_no_failure r wait time (by omega))
      have pcTime : (r.state time p).pc = .waitSelf k result := by rw [same]; exact self
      have pair := stable time (by omega)
      have step := r.valid time
      simp only [run, next, ordinary, pcTime, pair, passes, Bool.false_eq_true, ite_false,
        Option.map_some, Option.some.injEq] at step
      have after := wait (time + 1) (by omega)
      simp [← step, setLocal, WaitingAt] at after
  · exact waiting_no_failure r wait returnTime (by omega) fail

/-- The paper's highest-stuck-level contradiction, with every scan, reset,
replacement and higher-level critical completion discharged concretely. -/
theorem no_stuck_level {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (complete : CriticalCompletion r) :
    ¬ ∃ k, StuckLevel r k := by
  intro existsStuck
  obtain ⟨k, ⟨positive, within, p, start, value, level, stuck⟩, highest⟩ :=
    highest_stuck_level r existsStuck
  obtain ⟨time, bound, defer⟩ := opponents_eventually_defer r fair complete positive within level
    (fun t lo => (stuck t lo).1) (fun t lo => (stuck t lo).2) highest
  exact no_wait_with_deferred_opponents r fair positive within level
    (fun t lo => (stuck t (by omega)).1) (fun t lo => (stuck t (by omega)).2) defer

/-- Every concrete pending request has an own entry-or-failure event. -/
theorem pending_eventually_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (complete : CriticalCompletion r) {p : Proc n} {start : Nat}
    (pending : Pending (r.state start) p) :
    ∃ finish, start ≤ finish ∧ Outcome (r.state finish) (r.command finish) p := by
  by_contra missing
  have never : ∀ t, start ≤ t → ¬ Outcome (r.state t) (r.command t) p := by
    intro t lo event
    exact missing ⟨t, lo, event⟩
  obtain ⟨time, k, value, _, positive, within, level, stuck⟩ := pending_stabilizes r fair pending never
  exact no_stuck_level r fair complete ⟨k, positive, within, p, time, value, level, stuck⟩

/-- The first own outcome resolves the original request, before an abort or
entry could permit a replacement passage. -/
theorem pending_first_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (complete : CriticalCompletion r) {p : Proc n} {start : Nat}
    (pending : Pending (r.state start) p) :
    ∃ finish, start ≤ finish ∧ (r.event finish = .entry p ∨ r.event finish = .fail p) ∧
      ∀ t, start ≤ t → t < finish →
        Pending (r.state t) p ∧ r.event t ≠ .fail p ∧ r.event t ≠ .entry p := by
  classical
  have hex := pending_eventually_outcome r fair complete pending
  let finish := Nat.find hex
  have spec := Nat.find_spec hex
  have before : ∀ t, start ≤ t → t < finish → ¬ Outcome (r.state t) (r.command t) p := by
    intro t lo hi event
    exact Nat.find_min hex hi ⟨lo, event⟩
  refine ⟨finish, spec.1, spec.2, ?_⟩
  intro t lo hi
  have stays : Pending (r.state t) p := by
    induction t, lo using Nat.le_induction with
    | base => exact pending
    | succ t lo ih =>
      exact (next_pending_phase (r.wellFormed t p) (ih (by omega)) (r.valid t)
        (before t lo (by omega))).1
  have noEvent := before t lo hi
  exact ⟨stays, fun event => noEvent (Or.inr event), fun event => noEvent (Or.inl event)⟩

/-- Theorem 3-5: a non-failing requester receives its own matching entry, with
no failure bound, eventual stability, or participation premise on its peers. -/
theorem per_request_progress {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (complete : CriticalCompletion r) {p : Proc n} {start : Nat}
    (pending : Pending (r.state start) p)
    (noFailure : ∀ t, start ≤ t → r.event t ≠ .fail p) :
    ∃ finish, Served r p start finish := by
  obtain ⟨finish, bound, outcome, before⟩ := pending_first_outcome r fair complete pending
  exact ⟨finish, bound, outcome.resolve_right (noFailure finish bound), before⟩

theorem pending_not_request {n : Nat} (s : State n) (c : Command n) (p : Proc n)
    (pending : Pending s p) : label s c ≠ .request p := by
  cases c with
  | run q =>
    by_cases same : q = p
    · subst q
      cases pc : (s p).pc <;> simp_all [label, Pending, pendingPC]
    · cases pc : (s q).pc <;> simp [label, pc, same]
  | fail | restart | stutter => simp [label]

theorem Served.no_replacement {n : Nat} {cfg : Config n} {r : Run cfg}
    {p : Proc n} {start finish t : Nat} (served : Served r p start finish)
    (lo : start ≤ t) (hi : t < finish) : r.event t ≠ .request p :=
  pending_not_request _ _ _ (served.2.2 t lo hi).1

/-- A pending non-failing requester implies a new entry. -/
theorem deadlock_freedom {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (complete : CriticalCompletion r) {start : Nat}
    (requester : ∃ p, Pending (r.state start) p ∧ ∀ t, start ≤ t → r.event t ≠ .fail p) :
    ∃ finish p, start ≤ finish ∧ r.event finish = .entry p := by
  obtain ⟨p, pending, noFailure⟩ := requester
  obtain ⟨finish, served⟩ := per_request_progress r fair complete pending noFailure
  exact ⟨finish, p, served.1, served.2.1⟩

end EconomicalSolutions.Algorithm2

#print axioms EconomicalSolutions.Algorithm2.scan_first_outcome
#print axioms EconomicalSolutions.Algorithm2.pending_stabilizes
#print axioms EconomicalSolutions.Algorithm2.scan_against_stable_opponent
#print axioms EconomicalSolutions.Algorithm2.no_permanent_opposing_waiters
#print axioms EconomicalSolutions.Algorithm2.fresh_after_inactive
#print axioms EconomicalSolutions.Algorithm2.never_inactive_stabilizes
#print axioms EconomicalSolutions.Algorithm2.opponents_eventually_defer
#print axioms EconomicalSolutions.Algorithm2.no_stuck_level
#print axioms EconomicalSolutions.Algorithm2.pending_first_outcome
#print axioms EconomicalSolutions.Algorithm2.per_request_progress
#print axioms EconomicalSolutions.Algorithm2.Served.no_replacement
#print axioms EconomicalSolutions.Algorithm2.deadlock_freedom
