import Peterson.EconomicalSolutions.Algorithm5FIFO

/-! Local admission progress under instruction-or-failure scheduling alone. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm5

def Admission {n : Nat} : PC n → Prop
  | .capacity _ _ | .choose _ _ | .enqueue _ => True
  | _ => False

def Protocol {n : Nat} : PC n → Prop
  | .down | .idle | .cs => False
  | _ => True

structure Run {n : Nat} (cfg : Config n) where
  state : Nat → State n
  command : Nat → Command n
  initialized : state 0 = initial n
  valid : ∀ t, next cfg (state t) (command t) = some (state (t + 1))

def Run.event {n : Nat} {cfg : Config n} (r : Run cfg) (t : Nat) : Label n :=
  label (r.state t) (r.command t)

def Acts {n : Nat} (c : Command n) (p : Proc n) : Prop := c = .run p ∨ c = .fail p

/-- Only protocol instructions are owed; a process in outer `cs` may stay
there forever. Neither local tournament completion nor vacancy is a premise. -/
def ProtocolScheduling {n : Nat} {cfg : Config n} (r : Run cfg) : Prop :=
  ∀ t p, Protocol (r.state t p).pc → ∃ u, t ≤ u ∧ Acts (r.command u) p

def AdmissionOutcome {n : Nat} {cfg : Config n} (r : Run cfg) (p : Proc n) (t : Nat) : Prop :=
  r.event t = .enqueue p ∨ r.event t = .fail p

theorem Run.reachable {n : Nat} {cfg : Config n} (r : Run cfg) (t : Nat) :
    Reachable cfg (r.state t) := by
  induction t with
  | zero => rw [r.initialized]; exact .initial
  | succ t ih => exact .step ih ⟨r.command t, r.valid t, rfl⟩

theorem admission_holding {n : Nat} {pc : PC n} (h : Admission pc) : Holding pc := by
  cases pc <;> simp_all [Admission, Holding]

theorem admission_priority {n : Nat} {s : State n} {p : Proc n}
    (inv : Invariant s) (h : Admission (s p).pc) : priority s p = -1 := by
  have facts := inv.facts p
  cases hp : (s p).pc <;> simp_all [Admission, QueueFacts]

theorem next_live_unchanged {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    {p : Proc n} (step : next cfg s c = some t) (live : (s p).pc ≠ .down)
    (noAct : ¬ Acts c p) : t p = s p := by
  cases c with
  | stutter => simp only [next, Option.some.injEq] at step; subst t; rfl
  | run q =>
    have other : p ≠ q := by intro h; subst q; exact noAct (Or.inl rfl)
    simp only [next] at step
    cases h : ordinary cfg s q <;> simp only [h, Option.map_none, Option.map_some, Option.some.injEq] at step
    · contradiction
    · subst t; simp [other]
  | fail q =>
    have other : p ≠ q := by intro h; subst q; exact noAct (Or.inr rfl)
    simp only [next] at step
    split at step <;> try contradiction
    simp only [Option.some.injEq] at step; subst t; simp [other]
  | restart q =>
    simp only [next] at step
    split at step
    · rename_i down
      have other : p ≠ q := by intro h; subst q; exact live down
      simp only [Option.some.injEq] at step; subst t; simp [other]
    · contradiction

theorem first_scheduled_action {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (owed : Protocol (r.state start p).pc) :
    ∃ t, start ≤ t ∧ Acts (r.command t) p ∧ r.state t p = r.state start p := by
  classical
  have ex := fair start p owed
  have spec := Nat.find_spec ex
  have live : (r.state start p).pc ≠ .down := by intro h; simp [h, Protocol] at owed
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

theorem admission_next {n : Nat} {cfg : Config n} {s t : State n} {p : Proc n}
    {c : Command n} (h : Admission (s p).pc) (step : next cfg s c = some t)
    (ne : label s c ≠ .enqueue p) (nf : label s c ≠ .fail p) : Admission (t p).pc := by
  by_cases act : Acts c p
  · rcases act with rfl | rfl
    · cases hp : (s p).pc <;> simp only [Admission, hp] at h
      all_goals try (rename_i rest m; cases rest)
      all_goals simp only [next, ordinary, hp] at step
      all_goals try (split at step)
      all_goals simp only [Option.map_some, Option.some.injEq] at step
      all_goals subst t; simp_all [Admission, label]
    · exact (nf rfl).elim
  · have live : (s p).pc ≠ .down := by intro hp; simp [Admission, hp] at h
    simpa [next_live_unchanged step live act] using h

theorem no_outcome_admission {n : Nat} {cfg : Config n} (r : Run cfg)
    {p : Proc n} {start : Nat} (h : Admission (r.state start p).pc)
    (none : ∀ t, start ≤ t → ¬ AdmissionOutcome r p t) :
    ∀ t, start ≤ t → Admission (r.state t p).pc := by
  intro t lo
  induction t, lo using Nat.le_induction with
  | base => exact h
  | succ t lo ih =>
    exact admission_next ih (r.valid t) (fun e => none t lo (Or.inl e))
      (fun e => none t lo (Or.inr e))

/-- Every peer's number decreases or stays fixed while this exact owner holds
admission. Failed peers may restart arbitrarily, but cannot re-enqueue. -/
theorem held_peer_nonincreasing {n : Nat} {cfg : Config n} {s t : State n}
    {p q : Proc n} {c : Command n} (reach : Reachable cfg s)
    (held : Holding (s p).pc) (other : q ≠ p) (step : next cfg s c = some t) :
    priority t q ≤ priority s q := by
  have inv := reachable_invariant reach
  cases c with
  | stutter => simp only [next, Option.some.injEq] at step; subst t; exact le_refl _
  | run actor =>
    simp only [next] at step
    cases ho : ordinary cfg s actor with
    | none => simp [ho] at step
    | some l =>
      simp only [ho, Option.map_some, Option.some.injEq] at step; subst t
      by_cases eq : q = actor
      · subst actor
        simpa only [priority, setLocal_self] using
          change_le reach held other (ordinary_change (inv.facts q) ho) (inv.bounds q).1 (le_refl _)
      · simp [priority, eq]
  | fail actor | restart actor =>
    simp only [next] at step
    split at step <;> try contradiction
    all_goals simp only [Option.some.injEq] at step; subst t
    all_goals by_cases eq : q = actor
    all_goals simp [priority, setLocal, eq, dead]
    all_goals exact (inv.bounds actor).1

/-- Bounded integer descent eventually stops; no process-membership or failure
stability is assumed. -/
theorem priority_stabilizes (f : Nat → Int) (start : Nat)
    (lower : ∀ t, start ≤ t → -1 ≤ f t)
    (mono : ∀ t, start ≤ t → f (t + 1) ≤ f t) :
    ∃ time, start ≤ time ∧ ∀ t, time ≤ t → f t = f time := by
  classical
  have ex : ∃ v : Nat, ∃ t, start ≤ t ∧ (f t + 1).toNat = v :=
    ⟨(f start + 1).toNat, start, le_rfl, rfl⟩
  obtain ⟨time, lo, value⟩ := Nat.find_spec ex
  refine ⟨time, lo, ?_⟩
  intro t hi
  have le : f t ≤ f time := by
    induction t, hi using Nat.le_induction with
    | base => exact le_refl _
    | succ t hi ih => exact (mono t (by omega)).trans ih
  have min := Nat.find_min' ex
    (show ∃ u, start ≤ u ∧ (f u + 1).toNat = (f t + 1).toNat from ⟨t, by omega, rfl⟩)
  have := lower t (by omega)
  have := lower time lo
  omega

theorem finite_stabilization {n : Nat} (f : Nat → Fin n → Int) (start : Nat)
    (each : ∀ p, ∃ time, start ≤ time ∧ ∀ t, time ≤ t → f t p = f time p) :
    ∃ time, start ≤ time ∧ ∀ t, time ≤ t → ∀ p, f t p = f time p := by
  classical
  choose times lo stable using each
  let finish := (List.finRange n).foldl (fun a p => max a (times p)) start
  have bound : ∀ (xs : List (Fin n)) a, a ≤ xs.foldl (fun a p => max a (times p)) a ∧
      ∀ p ∈ xs, times p ≤ xs.foldl (fun a p => max a (times p)) a := by
    intro xs
    induction xs with
    | nil => intro a; simp
    | cons p xs ih =>
      intro a
      obtain ⟨le, all⟩ := ih (max a (times p))
      constructor
      · exact (Nat.le_max_left _ _).trans le
      · intro q mem
        rcases List.mem_cons.mp mem with rfl | mem
        · exact (Nat.le_max_right _ _).trans le
        · exact all q mem
  have b := bound (List.finRange n) start
  refine ⟨finish, b.1, ?_⟩
  intro t ht p
  have hp : times p ≤ finish := b.2 p (by simp)
  exact (stable p t (by omega)).trans (stable p finish hp).symm

/-- Every minimum local rank eventually faces its own real run/failure.
The applications below prove descent directly from `ordinary`/`next`. -/
theorem fair_descent_impossible {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) (p : Proc n) (start : Nat) (rank : Local n → Nat)
    (owed : ∀ t, start ≤ t → Protocol (r.state t p).pc)
    (decrease : ∀ t, start ≤ t → Acts (r.command t) p →
      rank (r.state (t + 1) p) < rank (r.state t p)) : False := by
  classical
  have ex : ∃ v, ∃ t, start ≤ t ∧ rank (r.state t p) = v :=
    ⟨rank (r.state start p), start, le_rfl, rfl⟩
  obtain ⟨t, lo, value⟩ := Nat.find_spec ex
  obtain ⟨u, tu, act, unchanged⟩ := first_scheduled_action r fair (owed t lo)
  have less := decrease u (by omega) act
  have min := Nat.find_min' ex
    (show ∃ k, start ≤ k ∧ rank (r.state k p) = rank (r.state (u + 1) p) from
      ⟨u + 1, by omega, rfl⟩)
  rw [unchanged, value] at less
  omega

def descentRank {n : Nat} (width : Nat) : PC n → Nat
  | .complete => width + 6
  | .depart => width + 5
  | .test => width + 4
  | .absent rest _ => rest.length + 3
  | .prepare _ => 2
  | .decrement _ => 1
  | _ => 0

/-- With a vacant predecessor, each real instruction reduces the finite
control rank or actually changes the priority. Retained scans and delayed
writes are included. -/
theorem vacant_ordinary_descent {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {l : Local n} (facts : QueueFacts s p) (positive : 0 < priority s p)
    (vacant : ∀ q, priority s q ≠ priority s p - 1)
    (step : ordinary cfg s p = some l) (same : l.value.priority = priority s p) :
    descentRank (cfg.order p).length l.pc < descentRank (cfg.order p).length (s p).pc := by
  cases hp : (s p).pc
  all_goals try (rename_i rest k; cases rest)
  all_goals simp only [QueueFacts, hp] at facts
  all_goals try omega
  all_goals simp only [ordinary, hp] at step
  case test =>
    have nz : (s p).value.priority ≠ 0 := by change priority s p ≠ 0; omega
    simp only [nz, ↓reduceIte, Option.some.injEq] at step
    subst l; simp [descentRank]
  case absent.cons q rest =>
    have missing : (s q).value.priority ≠ k - 1 := by
      have := vacant q; simpa only [facts.1] using this
    simp only [missing, ↓reduceIte, Option.some.injEq] at step
    subst l; simp [descentRank]
  all_goals simp only [Option.some.injEq] at step
  all_goals subst l
  all_goals simp only [descentRank, hp]; try omega
  all_goals dsimp [priority] at facts same positive
  all_goals omega

/-- In a stationary priority vector every positive occupied place has an
occupied predecessor; otherwise fair actual steps force a decrement/failure. -/
theorem stationary_predecessor {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {start : Nat}
    (stable : ∀ t, start ≤ t → ∀ q, priority (r.state t) q = priority (r.state start) q)
    (p : Proc n) (positive : 0 < priority (r.state start) p) :
    ∃ q, priority (r.state start) q = priority (r.state start) p - 1 := by
  by_contra missing
  have vacant : ∀ q, priority (r.state start) q ≠ priority (r.state start) p - 1 := by
    simpa only [not_exists] using missing
  apply fair_descent_impossible r fair p start (fun l => descentRank (cfg.order p).length l.pc)
  · intro t lo
    have facts := (reachable_invariant (r.reachable t)).facts p
    have pos : 0 < priority (r.state t) p := by rw [stable t lo]; exact positive
    cases hp : (r.state t p).pc <;> simp_all [QueueFacts, Protocol]
  · intro t lo act
    have eqp := stable t lo p
    have eqnext := stable (t + 1) (by omega) p
    have facts := (reachable_invariant (r.reachable t)).facts p
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
        apply vacant_ordinary_descent facts (by omega) _ ho
        · rw [← loc]; exact eqnext.trans eqp.symm
        · intro q
          rw [stable t lo q, eqp]
          exact vacant q
    · rw [act] at step
      simp only [next] at step
      split at step
      · contradiction
      · simp only [Option.some.injEq] at step
        have gone : priority (r.state (t + 1)) p = -1 := by rw [← step]; simp [priority, dead]
        omega

/-- A stationary top would force all n priorities to be occupied. The owner
is still unqueued, so the n real processes cannot fill those n places. -/
theorem stationary_top_vacant {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {start : Nat} (owner : Proc n)
    (unqueued : priority (r.state start) owner = -1)
    (stable : ∀ t, start ≤ t → ∀ q, priority (r.state t) q = priority (r.state start) q) :
    ∀ q, priority (r.state start) q < (n : Int) - 1 := by
  classical
  intro q
  have bound := (reachable_invariant (r.reachable start)).bounds q
  by_contra high
  have top : priority (r.state start) q = (n : Int) - 1 := by omega
  have chain : ∀ d, d < n → ∃ p, priority (r.state start) p = (n : Int) - 1 - d := by
    intro d dn
    induction d with
    | zero => exact ⟨q, by simpa using top⟩
    | succ d ih =>
      obtain ⟨p, value⟩ := ih (by omega)
      obtain ⟨a, pred⟩ := stationary_predecessor r fair stable p (by omega)
      exact ⟨a, by omega⟩
  have all : ∀ k : Fin n, ∃ p, priority (r.state start) p = (k : Nat) := by
    intro k
    obtain ⟨p, value⟩ := chain (n - 1 - k.val) (by omega)
    exact ⟨p, by omega⟩
  choose occupant value using all
  have injective : Function.Injective occupant := by
    intro a b eq
    have av := value a
    have bv := value b
    rw [eq] at av
    apply Fin.ext
    omega
  obtain ⟨k, eq⟩ := Finite.surjective_of_injective injective owner
  have val := value k
  rw [eq, unqueued] at val
  omega

def admissionRank {n : Nat} (width : Nat) : PC n → Nat
  | .capacity rest m => if m < (n : Int) - 1 then rest.length + width + 3
      else rest.length + 2 * width + 4
  | .choose rest _ => rest.length + 2
  | .enqueue _ => 1
  | _ => 0

/-- A stale capacity maximum may require one retry. Its larger rank pays for
that retry; all later samples are below the top, so it cannot recur. -/
theorem clear_top_ordinary_descent {n : Nat} {cfg : Config n} {s : State n}
    {p : Proc n} {l : Local n} (admission : Admission (s p).pc)
    (clear : ∀ q, priority s q < (n : Int) - 1)
    (step : ordinary cfg s p = some l) (ne : label s (.run p) ≠ .enqueue p) :
    admissionRank (cfg.order p).length l.pc < admissionRank (cfg.order p).length (s p).pc := by
  have pos : 0 < n := Nat.zero_lt_of_lt p.isLt
  cases hp : (s p).pc <;> simp only [Admission, hp] at admission
  all_goals try (rename_i rest m; cases rest)
  all_goals simp only [ordinary, hp] at step
  all_goals try (split at step)
  all_goals simp only [Option.some.injEq] at step
  all_goals subst l
  all_goals simp only [admissionRank, hp, List.length_cons]
  all_goals try (simp only [label, hp, ne_eq, not_true_eq_false] at ne)
  all_goals try (split)
  all_goals try (split)
  all_goals try omega
  all_goals have samples : ∀ q, (s q).value.priority < (n : Int) - 1 := clear
  all_goals simp only [max_lt_iff] at *
  all_goals simp_all only [samples, and_true]

/-- The exact admission episode cannot remain forever without enqueue or
failure. Priority stabilization is derived from the concrete serialized
admission, not supplied by a caller or inferred from a stable population. -/
theorem admission_eventually_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (admission : Admission (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ AdmissionOutcome r p finish := by
  classical
  by_contra no
  have none : ∀ t, start ≤ t → ¬ AdmissionOutcome r p t := by simpa only [not_exists, not_and] using no
  have owner := no_outcome_admission r admission none
  have decrease : ∀ t, start ≤ t → ∀ q, priority (r.state (t + 1)) q ≤ priority (r.state t) q := by
    intro t lo q
    by_cases eq : q = p
    · subst q
      rw [admission_priority (reachable_invariant (r.reachable t)) (owner t lo),
        admission_priority (reachable_invariant (r.reachable (t + 1))) (owner (t + 1) (by omega))]
    · exact held_peer_nonincreasing (r.reachable t) (admission_holding (owner t lo)) eq (r.valid t)
  have each : ∀ q, ∃ time, start ≤ time ∧ ∀ t, time ≤ t →
      priority (r.state t) q = priority (r.state time) q := by
    intro q
    exact priority_stabilizes (fun t => priority (r.state t) q) start
      (fun t _ => ((reachable_invariant (r.reachable t)).bounds q).1) (fun t lo => decrease t lo q)
  obtain ⟨time, lo, stable⟩ := finite_stabilization (fun t q => priority (r.state t) q) start each
  have clear := stationary_top_vacant r fair p
    (admission_priority (reachable_invariant (r.reachable time)) (owner time lo)) stable
  apply fair_descent_impossible r fair p time (fun l => admissionRank (cfg.order p).length l.pc)
  · intro t ht
    have h := owner t (by omega)
    cases hp : (r.state t p).pc <;> simp_all [Admission, Protocol]
  · intro t ht act
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
        apply clear_top_ordinary_descent (owner t (by omega)) _ ho
        · intro event
          apply none t (by omega)
          exact Or.inl (by simpa only [Run.event, act] using event)
        · intro q; rw [stable t ht q]; exact clear q
    · exact (none t (by omega) (Or.inr (by simp [Run.event, act, label]))).elim

/-- First outcome and the intervening live controls identify this occurrence,
so an enqueue by a replacement request cannot discharge the obligation. -/
theorem admission_first_outcome {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (admission : Admission (r.state start p).pc) :
    ∃ finish, start ≤ finish ∧ AdmissionOutcome r p finish ∧
      ∀ t, start ≤ t → t < finish →
        Admission (r.state t p).pc ∧ ¬ AdmissionOutcome r p t := by
  classical
  have ex := admission_eventually_outcome r fair admission
  obtain ⟨lo, event⟩ := Nat.find_spec ex
  have before : ∀ t, start ≤ t → t < Nat.find ex → ¬ AdmissionOutcome r p t := by
    intro t lo hi event
    have := Nat.find_min' ex ⟨lo, event⟩
    omega
  refine ⟨Nat.find ex, lo, event, ?_⟩
  intro t st tf
  refine ⟨?_, before t st tf⟩
  induction t, st using Nat.le_induction with
  | base => exact admission
  | succ t st ih =>
    have old := ih (by omega)
    exact admission_next old (r.valid t)
      (fun e => before t st (by omega) (Or.inl e))
      (fun e => before t st (by omega) (Or.inr e))

theorem admission_surviving_enqueues {n : Nat} {cfg : Config n} (r : Run cfg)
    (fair : ProtocolScheduling r) {p : Proc n} {start : Nat}
    (admission : Admission (r.state start p).pc)
    (survives : ∀ t, start ≤ t → r.event t ≠ .fail p) :
    ∃ finish, start ≤ finish ∧ r.event finish = .enqueue p ∧
      ∀ t, start ≤ t → t < finish →
        Admission (r.state t p).pc ∧ ¬ AdmissionOutcome r p t := by
  obtain ⟨t, lo, event, before⟩ := admission_first_outcome r fair admission
  exact ⟨t, lo, event.resolve_right (survives t lo), before⟩

end EconomicalSolutions.Algorithm5

#print axioms EconomicalSolutions.Algorithm5.stationary_predecessor
#print axioms EconomicalSolutions.Algorithm5.stationary_top_vacant
#print axioms EconomicalSolutions.Algorithm5.admission_eventually_outcome
#print axioms EconomicalSolutions.Algorithm5.admission_first_outcome
#print axioms EconomicalSolutions.Algorithm5.admission_surviving_enqueues
