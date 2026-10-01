import Peterson.EconomicalSolutions.Algorithm5Doorway

/-! Outer per-request progress, with the separately frozen outer completion premise. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm5

/-- Every occurrence of actual outer critical control eventually completes or
fails. The local tournament completion is already a derived result. -/
def CriticalCompletion {n : Nat} {cfg : Config n} (r : Run cfg) : Prop :=
  ∀ t p, (r.state t p).pc = .cs →
    ∃ u, t ≤ u ∧ (r.event u = .complete p ∨ r.event u = .fail p)

def Pending {n : Nat} (pc : PC n) : Prop := Doorway pc ∨ QueuedPending pc

def Outcome {n : Nat} {cfg : Config n} (r : Run cfg) (p : Proc n) (t : Nat) : Prop :=
  r.event t = .entry p ∨ r.event t = .fail p

/-- Ignore positions strictly above a retained requester. A later enqueue is
above it; a single decrement cannot cross its occupied position. -/
def below (k v : Int) : Int := if v ≤ k then v else -1

theorem below_lower {k v : Int} (lo : -1 ≤ v) : -1 ≤ below k v := by
  unfold below; split <;> omega

theorem below_change {n : Nat} {s : State n} {p q : Proc n} {l : Local n}
    (inv : Invariant s) (other : q ≠ p) (change : Change s q l)
    (nonneg : 0 ≤ priority s p) :
    below (priority s p) l.value.priority ≤ below (priority s p) (priority s q) := by
  cases change with
  | same eq => rw [eq]
  | reset eq => rw [eq]; unfold below; split <;> split <;> have := (inv.bounds q).1 <;> omega
  | enqueue _ _ _ above =>
    have h := above p other.symm
    have lo := below_lower (k := priority s p) (inv.bounds q).1
    simp only [below, show ¬ l.value.priority ≤ priority s p by omega, ↓reduceIte]
    exact lo
  | decrement eq lo absent =>
    have neq : priority s q ≠ priority s p := by
      intro h; exact other (inv.unique q p (by omega) h)
    have missing := absent p other.symm
    unfold below
    split <;> split <;> omega

theorem below_next {n : Nat} {cfg : Config n} {s t : State n} {p q : Proc n}
    {c : Command n} (reach : Reachable cfg s) (step : next cfg s c = some t)
    (nonneg : 0 ≤ priority s p) (retained : priority t p = priority s p) :
    below (priority s p) (priority t q) ≤ below (priority s p) (priority s q) := by
  have inv := reachable_invariant reach
  by_cases own : q = p
  · subst q; rw [retained]
  cases c with
  | stutter => simp only [next, Option.some.injEq] at step; subst t; exact le_rfl
  | run actor =>
    simp only [next] at step
    cases ho : ordinary cfg s actor with
    | none => simp [ho] at step
    | some l =>
      simp only [ho, Option.map_some, Option.some.injEq] at step; subst t
      by_cases eq : q = actor
      · subst actor
        simpa only [priority, setLocal_self] using below_change inv own (ordinary_change (inv.facts q) ho) nonneg
      · simp [priority, eq]
  | fail actor | restart actor =>
    simp only [next] at step
    split at step <;> try contradiction
    all_goals simp only [Option.some.injEq] at step; subst t
    all_goals by_cases eq : q = actor
    all_goals try (simp [priority, eq]; done)
    all_goals subst actor
    all_goals simp only [priority, setLocal_self, dead]
    all_goals simpa [below, show (-1 : Int) ≤ priority s p by omega] using
      below_lower (k := priority s p) (inv.bounds q).1

/-- Completion extends instruction scheduling only at actual outer critical
control. Idle and failed processes are still not required to participate. -/
theorem active_scheduling {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    (t : Nat) (p : Proc n) (live : (r.state t p).pc ≠ .down)
    (busy : (r.state t p).pc ≠ .idle) :
    ∃ u, t ≤ u ∧ Acts (r.command u) p := by
  by_cases cs : (r.state t p).pc = .cs
  · obtain ⟨u, lo, event⟩ := completion t p cs
    refine ⟨u, lo, ?_⟩
    cases hc : r.command u with
    | run q =>
      cases hp : (r.state u q).pc <;> simp only [Run.event, hc, label, hp] at event
      all_goals rcases event with event | event
      all_goals try contradiction
      all_goals cases event; exact Or.inl rfl
    | fail q =>
      simp only [Run.event, hc, label, reduceCtorEq, false_or, Label.fail.injEq] at event
      subst q; exact Or.inr rfl
    | restart | stutter => simp [Run.event, hc, label] at event
  · apply fair t p
    cases hp : (r.state t p).pc <;> simp_all [Protocol]

theorem first_active_action {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    {p : Proc n} {start : Nat} (live : (r.state start p).pc ≠ .down)
    (busy : (r.state start p).pc ≠ .idle) :
    ∃ t, start ≤ t ∧ Acts (r.command t) p ∧ r.state t p = r.state start p := by
  classical
  have ex := active_scheduling r fair completion start p live busy
  have spec := Nat.find_spec ex
  have unchanged : ∀ t, start ≤ t → t ≤ Nat.find ex → r.state t p = r.state start p := by
    intro t lo hi
    induction t, lo using Nat.le_induction with
    | base => rfl
    | succ t lo ih =>
      have old := ih (by omega)
      have noAct : ¬ Acts (r.command t) p := by
        intro act
        have := Nat.find_min' ex ⟨lo, act⟩
        omega
      exact (next_live_unchanged (r.valid t) (by simpa [old] using live) noAct).trans old
  exact ⟨Nat.find ex, spec.1, spec.2, unchanged _ spec.1 (le_refl _)⟩

theorem active_descent_impossible {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    (p : Proc n) (start : Nat) (rank : Local n → Nat)
    (owed : ∀ t, start ≤ t → (r.state t p).pc ≠ .down ∧ (r.state t p).pc ≠ .idle)
    (decrease : ∀ t, start ≤ t → Acts (r.command t) p →
      rank (r.state (t + 1) p) < rank (r.state t p)) : False := by
  classical
  have ex : ∃ v, ∃ t, start ≤ t ∧ rank (r.state t p) = v :=
    ⟨rank (r.state start p), start, le_rfl, rfl⟩
  obtain ⟨t, lo, value⟩ := Nat.find_spec ex
  obtain ⟨u, tu, act, unchanged⟩ := first_active_action r fair completion (owed t lo).1 (owed t lo).2
  have less := decrease u (by omega) act
  have min := Nat.find_min' ex
    (show ∃ k, start ≤ k ∧ rank (r.state k p) = rank (r.state (u + 1) p) from
      ⟨u + 1, by omega, rfl⟩)
  rw [unchanged, value] at less
  omega

def zeroRank {n : Nat} : PC n → Nat
  | .complete => 6
  | .depart => 5
  | .test => 4
  | .enter => 3
  | .cs => 2
  | .release => 1
  | _ => 0

theorem zero_ordinary_descent {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {l : Local n} (facts : QueueFacts s p) (zero : priority s p = 0)
    (step : ordinary cfg s p = some l) (same : l.value.priority = 0) :
    zeroRank l.pc < zeroRank (s p).pc := by
  cases hp : (s p).pc
  all_goals try (rename_i rest k; cases rest)
  all_goals simp only [QueueFacts, hp] at facts
  all_goals try omega
  all_goals simp only [ordinary, hp] at step
  all_goals try (simp only [show (s p).value.priority = 0 from zero, ↓reduceIte] at step)
  all_goals simp only [Option.some.injEq] at step
  all_goals subst l
  all_goals simp_all [zeroRank, dead]

/-- No single zero episode can keep its number forever: real entry, outer
completion and final release are separately owed instructions. -/
theorem zero_not_stationary {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    (p : Proc n) (start : Nat)
    (zero : ∀ t, start ≤ t → priority (r.state t) p = 0) : False := by
  apply active_descent_impossible r fair completion p start (fun l => zeroRank l.pc)
  · intro t lo
    have facts := (reachable_invariant (r.reachable t)).facts p
    have value := zero t lo
    cases hp : (r.state t p).pc <;> simp_all [QueueFacts]
  · intro t lo act
    have step := r.valid t
    rcases act with act | act
    · rw [act] at step
      simp only [next] at step
      cases ho : ordinary cfg (r.state t) p with
      | none => simp [ho] at step
      | some l =>
        simp only [ho, Option.map_some, Option.some.injEq] at step
        have loc : r.state (t + 1) p = l := by rw [← step]; simp
        rw [loc]
        exact zero_ordinary_descent ((reachable_invariant (r.reachable t)).facts p) (zero t lo) ho
          (by rw [← loc]; exact zero (t + 1) (by omega))
    · rw [act] at step
      simp only [next] at step
      split at step
      · contradiction
      · simp only [Option.some.injEq] at step
        have gone : priority (r.state (t + 1)) p = -1 := by rw [← step]; simp [priority, dead]
        have := zero (t + 1) (by omega)
        omega

theorem below_eq_iff {k v a : Int} (nonneg : 0 ≤ a) (bound : a ≤ k) :
    below k v = a ↔ v = a := by
  unfold below; split <;> omega

/-- Stabilization of the retained lower part preserves occupancy at each
nonnegative position there, while ignoring arbitrary activity above it. -/
theorem stable_below_value {n : Nat} {cfg : Config n} (r : Run cfg)
    {start : Nat} {k v : Int}
    (stable : ∀ t, start ≤ t → ∀ q, below k (priority (r.state t) q) =
      below k (priority (r.state start) q))
    (nonneg : 0 ≤ v) (bound : v ≤ k) (t : Nat) (lo : start ≤ t) (q : Proc n) :
    priority (r.state t) q = v ↔ priority (r.state start) q = v := by
  rw [← below_eq_iff nonneg bound, stable t lo q, below_eq_iff nonneg bound]

theorem stationary_below_predecessor {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {start : Nat} {k : Int}
    (stable : ∀ t, start ≤ t → ∀ q, below k (priority (r.state t) q) =
      below k (priority (r.state start) q))
    (p : Proc n) (positive : 0 < priority (r.state start) p)
    (bound : priority (r.state start) p ≤ k) :
    ∃ q, priority (r.state start) q = priority (r.state start) p - 1 := by
  by_contra missing
  have fixed : ∀ t, start ≤ t → priority (r.state t) p = priority (r.state start) p := by
    intro t lo
    exact (stable_below_value r stable (by omega) bound t lo p).2 rfl
  have vacant : ∀ t, start ≤ t → ∀ q, priority (r.state t) q ≠ priority (r.state t) p - 1 := by
    intro t lo q eq
    apply missing
    refine ⟨q, (stable_below_value r stable (by omega) (by omega) t lo q).1 ?_⟩
    simpa [fixed t lo] using eq
  apply fair_descent_impossible r fair p start (fun l => descentRank (cfg.order p).length l.pc)
  · intro t lo
    have facts := (reachable_invariant (r.reachable t)).facts p
    have pos : 0 < priority (r.state t) p := by rw [fixed t lo]; exact positive
    cases hp : (r.state t p).pc <;> simp_all [QueueFacts, Protocol]
  · intro t lo act
    have eqp := fixed t lo
    have eqnext := fixed (t + 1) (by omega)
    have step := r.valid t
    rcases act with act | act
    · rw [act] at step
      simp only [next] at step
      cases ho : ordinary cfg (r.state t) p with
      | none => simp [ho] at step
      | some l =>
        simp only [ho, Option.map_some, Option.some.injEq] at step
        have loc : r.state (t + 1) p = l := by rw [← step]; simp
        rw [loc]
        exact vacant_ordinary_descent ((reachable_invariant (r.reachable t)).facts p)
          (by omega) (vacant t lo) ho (by rw [← loc]; exact eqnext.trans eqp.symm)
    · rw [act] at step
      simp only [next] at step
      split at step
      · contradiction
      · simp only [Option.some.injEq] at step
        have gone : priority (r.state (t + 1)) p = -1 := by rw [← step]; simp [priority, dead]
        omega

/-- Any retained nonnegative priority forces a stationary lower chain down to
zero. Outer completion rules out the zero endpoint. This is a consequence of
actual transitions and scheduling, never a supplied vacancy or order oracle. -/
theorem retained_priority_impossible {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    (p : Proc n) (start : Nat) (nonneg : 0 ≤ priority (r.state start) p)
    (fixed : ∀ t, start ≤ t → priority (r.state t) p = priority (r.state start) p) : False := by
  let k := priority (r.state start) p
  have each : ∀ q, ∃ time, start ≤ time ∧ ∀ t, time ≤ t →
      below k (priority (r.state t) q) = below k (priority (r.state time) q) := by
    intro q
    apply priority_stabilizes (fun t => below k (priority (r.state t) q)) start
    · intro t _; exact below_lower ((reachable_invariant (r.reachable t)).bounds q).1
    · intro t lo
      have h := below_next (r.reachable t) (r.valid t)
        (p := p) (q := q) (by rw [fixed t lo]; exact nonneg)
        ((fixed (t + 1) (by omega)).trans (fixed t lo).symm)
      simpa only [fixed t lo] using h
  obtain ⟨time, lo, stable⟩ := finite_stabilization
    (fun t q => below k (priority (r.state t) q)) start each
  have chain : ∀ d : Nat, d ≤ k.toNat →
      ∃ q, priority (r.state time) q = k - d := by
    intro d bound
    induction d with
    | zero => exact ⟨p, by simpa [k] using fixed time lo⟩
    | succ d ih =>
      obtain ⟨q, value⟩ := ih (by omega)
      obtain ⟨a, pred⟩ := stationary_below_predecessor r fair stable q (by dsimp [k] at *; omega) (by omega)
      exact ⟨a, by omega⟩
  obtain ⟨q, zero⟩ := chain k.toNat le_rfl
  have kz : 0 ≤ k := nonneg
  have value : priority (r.state time) q = 0 := by omega
  apply zero_not_stationary r fair completion q time
  intro t ht
  exact (stable_below_value r stable (v := 0) (by omega) kz t ht q).2 value

/-- The post-enqueue portion of this request cannot persist forever. Its own
number only decreases; once fixed, the preceding theorem rules it out. -/
theorem queued_eventually_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    {p : Proc n} {start : Nat} (pending : QueuedPending (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ Outcome r p finish := by
  classical
  by_contra no
  have none : ∀ t, start ≤ t → ¬ Outcome r p t := by simpa only [not_exists, not_and] using no
  have stays : ∀ t, start ≤ t → QueuedPending (r.state t p).pc := by
    intro t lo
    induction t, lo using Nat.le_induction with
    | base => exact pending
    | succ t lo ih =>
      exact (queued_next (reachable_invariant (r.reachable t)) ih
        (fun e => none t lo (Or.inl e)) (fun e => none t lo (Or.inr e)) (r.valid t)).1
  have nonneg : ∀ t, start ≤ t → 0 ≤ priority (r.state t) p := by
    intro t lo; exact queued_nonnegative ((reachable_invariant (r.reachable t)).facts p) (stays t lo)
  obtain ⟨time, lo, fixed⟩ := priority_stabilizes (fun t => priority (r.state t) p) start
    (fun t lo => by have := nonneg t lo; omega) (by
      intro t lo
      have change := (queued_next (reachable_invariant (r.reachable t)) (stays t lo)
        (fun e => none t lo (Or.inl e)) (fun e => none t lo (Or.inr e)) (r.valid t)).2
      rcases change with change | change <;> omega)
  exact retained_priority_impossible r fair completion p time (nonneg time lo) fixed

theorem pending_next {n : Nat} {cfg : Config n} {s t : State n} {p : Proc n}
    {c : Command n} (reach : Reachable cfg s) (pending : Pending (s p).pc)
    (step : next cfg s c = some t) (ne : label s c ≠ .entry p)
    (nf : label s c ≠ .fail p) : Pending (t p).pc := by
  rcases pending with doorway | queued
  · by_cases en : label s c = .enqueue p
    · exact Or.inr (enqueue_next reach step en).1
    · exact Or.inl (doorway_next doorway step en nf)
  · exact Or.inr (queued_next (reachable_invariant reach) queued ne nf step).1

/-- Covers initial outer request preparation, the entire doorway and every
queued pending control, including a delayed final entry instruction. -/
theorem pending_eventually_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    {p : Proc n} {start : Nat} (pending : Pending (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ Outcome r p finish := by
  rcases pending with doorway | queued
  · obtain ⟨t, lo, event⟩ := doorway_eventually_outcome r fair doorway
    rcases event with enqueue | failure
    · obtain ⟨u, bound, outcome⟩ := queued_eventually_outcome r fair completion
        (enqueue_next (r.reachable t) (r.valid t) enqueue).1
      exact ⟨u, by omega, outcome⟩
    · exact ⟨t, lo, Or.inr failure⟩
  · exact queued_eventually_outcome r fair completion queued

/-- The least outcome belongs to this pending occurrence. Every intervening
state is still pending, and neither own entry nor abort occurred earlier. -/
theorem pending_first_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    {p : Proc n} {start : Nat} (pending : Pending (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ Outcome r p finish ∧
      ∀ t, start ≤ t → t < finish →
        Pending (r.state t p).pc ∧ ¬ Outcome r p t := by
  classical
  have ex := pending_eventually_outcome r fair completion pending
  obtain ⟨lo, event⟩ := Nat.find_spec ex
  have before : ∀ t, start ≤ t → t < Nat.find ex → ¬ Outcome r p t := by
    intro t lo hi event
    have := Nat.find_min' ex ⟨lo, event⟩
    omega
  refine ⟨Nat.find ex, lo, event, ?_⟩
  intro t st tf
  refine ⟨?_, before t st tf⟩
  induction t, st using Nat.le_induction with
  | base => exact pending
  | succ t st ih =>
    exact pending_next (r.reachable t) (ih (by omega)) (r.valid t)
      (fun e => before t st (by omega) (Or.inl e))
      (fun e => before t st (by omega) (Or.inr e))

theorem surviving_request_enters {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r)
    {p : Proc n} {start : Nat} (pending : Pending (r.state start p).pc)
    (survives : ∀ t, start ≤ t → r.event t ≠ .fail p) :
    ∃ finish, start ≤ finish ∧ r.event finish = .entry p ∧
      ∀ t, start ≤ t → t < finish →
        Pending (r.state t p).pc ∧ ¬ Outcome r p t := by
  obtain ⟨t, lo, event, before⟩ := pending_first_outcome r fair completion pending
  exact ⟨t, lo, event.resolve_right (survives t lo), before⟩

/-- A pending surviving request guarantees a new outer entry event. -/
theorem deadlock_freedom {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (completion : CriticalCompletion r) (start : Nat)
    (request : ∃ p, Pending (r.state start p).pc ∧
      ∀ t, start ≤ t → r.event t ≠ .fail p) :
    ∃ t, start ≤ t ∧ ∃ p, r.event t = .entry p := by
  obtain ⟨p, pending, survives⟩ := request
  obtain ⟨t, lo, entry, _⟩ := surviving_request_enters r fair completion pending survives
  exact ⟨t, lo, p, entry⟩

/-- Pending control cannot issue a replacement request or restart. Together
with first-outcome absence of abort this protects the original occurrence. -/
theorem pending_no_replacement {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {p : Proc n} (pending : Pending (s p).pc)
    (step : next cfg s c = some t) :
    label s c ≠ .request p ∧ label s c ≠ .restart p := by
  cases c with
  | run q =>
    by_cases eq : q = p
    · subst q
      cases hp : (s p).pc <;> simp_all [Pending, Doorway, QueuedPending, label]
    · cases hp : (s q).pc <;> simp [label, hp, eq]
  | restart q =>
    by_cases eq : q = p
    · subst q
      have live : (s p).pc ≠ .down := by
        intro hp; simp [hp, Pending, Doorway, QueuedPending] at pending
      simp [next, live] at step
    · simp [label, eq]
  | fail | stutter => simp [label]

end EconomicalSolutions.Algorithm5

#print axioms EconomicalSolutions.Algorithm5.below_next
#print axioms EconomicalSolutions.Algorithm5.zero_not_stationary
#print axioms EconomicalSolutions.Algorithm5.stationary_below_predecessor
#print axioms EconomicalSolutions.Algorithm5.retained_priority_impossible
#print axioms EconomicalSolutions.Algorithm5.queued_eventually_outcome
#print axioms EconomicalSolutions.Algorithm5.pending_first_outcome
#print axioms EconomicalSolutions.Algorithm5.surviving_request_enters
#print axioms EconomicalSolutions.Algorithm5.deadlock_freedom
#print axioms EconomicalSolutions.Algorithm5.pending_no_replacement
