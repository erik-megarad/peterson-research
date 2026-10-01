import Peterson.EconomicalSolutions.Algorithm7

/-! Concrete safety barriers for the frozen Algorithm 7 interpreter.
These results do not assert mutual exclusion or a clock-observation oracle. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm7

@[simp] theorem setLocal_self {n : Nat} (s : State n) (p : Proc n) (l : Local n) :
    setLocal s p l p = l := by simp [setLocal]

@[simp] theorem setLocal_other {n : Nat} (s : State n) (p q : Proc n) (l : Local n)
    (other : q ≠ p) : setLocal s p l q = s q := by simp [setLocal, other]

def ValidPrefix {n : Nat} (cfg : Config n) (trace : Nat → State n)
    (commands : Nat → Command n) (finish : Nat) : Prop :=
  trace 0 = initial n ∧ ∀ t, t < finish → next cfg (trace t) (commands t) = some (trace (t + 1))

/-- The actual stage 11 guard, applied to one whole-register sample. -/
def Blocks {n : Nat} (p q : Proc n) (v : Value) : Prop :=
  match v with
  | .cs => True
  | .live .three _ _ => q.val < p.val
  | _ => False

/-- Control credit for having passed q in the current eligibility scan.
Publication, actual entry and delayed release retain this credit. -/
def PassedPeer {n : Nat} (q : Proc n) : PC n → Prop
  | .eligible rest => q ∉ rest
  | .publish | .enter | .cs | .release => True
  | _ => False

def EligibilityRead {n : Nat} (s : State n) (c : Command n) (p q : Proc n) : Prop :=
  c = .run p ∧ ∃ rest, (s p).pc = .eligible (q :: rest) ∧ ¬ Blocks p q (s q).value

theorem ordinary_passed_peer {n : Nat} {cfg : Config n} {s : State n} {p q : Proc n}
    {l : Local n} (other : q ≠ p) (step : ordinary cfg s p = some l)
    (after : PassedPeer q l.pc) :
    PassedPeer q (s p).pc ∨ EligibilityRead s (.run p) p q := by
  cases pc : (s p).pc
  case' join clock first cp => cases cp
  case' attempt phase clock cp => cases clock <;> cases cp
  case' tickWrite phase clock pending => cases clock
  case' pairDone phase => cases phase
  case' build rest => cases rest
  case' delete rest => cases rest
  case' add rest => cases rest
  case' eligible rest => cases rest
  case eligible.cons head rest =>
    by_cases eq : q = head
    · subst head
      right
      refine ⟨rfl, rest, pc, ?_⟩
      cases value : (s q).value
      case' live level b0 b1 => cases level
      all_goals simp only [ordinary, pc, value] at step
      all_goals try (split at step)
      all_goals simp only [Option.some.injEq] at step
      all_goals subst l
      all_goals simp_all [Blocks, PassedPeer]
    · left
      cases value : (s head).value
      case' live level b0 b1 => cases level
      all_goals simp only [ordinary, pc, value] at step
      all_goals try (split at step)
      all_goals simp only [Option.some.injEq] at step
      all_goals subst l
      all_goals simp_all [Blocks, PassedPeer]
  all_goals simp only [ordinary, pc] at step
  all_goals try contradiction
  all_goals try (rw [Option.map_eq_some_iff] at step; obtain ⟨out, _, rfl⟩ := step)
  all_goals repeat (split at step)
  all_goals try contradiction
  all_goals try (simp only [Option.some.injEq] at step; subst l)
  all_goals simp only [PassedPeer, afterAttempt] at after ⊢
  all_goals try (simp_all [PassedPeer, afterAttempt, cfg.complete])
  all_goals try (split_ifs at after <;> simp_all [PassedPeer])
  all_goals simp only [bind, Option.bind_eq_some_iff] at step
  all_goals obtain ⟨out, _, step⟩ := step
  all_goals split at step
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at step
  all_goals subst l
  all_goals contradiction

theorem next_passed_peer {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    {p q : Proc n} (other : q ≠ p) (step : next cfg s c = some t)
    (after : PassedPeer q (t p).pc) :
    PassedPeer q (s p).pc ∨ EligibilityRead s c p q := by
  cases c with
  | stutter =>
    have eq := Option.some.inj step
    exact Or.inl (by simpa [← eq] using after)
  | run actor =>
    obtain ⟨out, ordinaryStep, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor
      exact ordinary_passed_peer other ordinaryStep (by simpa using after)
    · exact Or.inl (by simpa [eq] using after)
  | request actor | fail actor | restart actor | complete actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp_all [reset, PassedPeer])
      | exact Or.inl (by simpa [eq] using after)

/-- Every retained eligibility credit has a real successful read, after the
last boundary at which that credit was absent. The witness includes the full
interval of credit, so failed/replaced requests cannot hide in the suffix. -/
theorem eligibility_read_history {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (ab : a ≤ b) (bf : b ≤ finish)
    (other : q ≠ p) (before : ¬ PassedPeer q (trace a p).pc)
    (after : PassedPeer q (trace b p).pc) :
    ∃ r, a ≤ r ∧ r < b ∧ EligibilityRead (trace r) (commands r) p q ∧
      ∀ u, r < u → u ≤ b → PassedPeer q (trace u p).pc := by
  classical
  induction b, ab using Nat.le_induction with
  | base => exact (before after).elim
  | succ b ab ih =>
    by_cases previous : PassedPeer q (trace b p).pc
    · obtain ⟨r, lo, hi, read, kept⟩ := ih (by omega) previous
      refine ⟨r, lo, by omega, read, ?_⟩
      intro u ru ub
      by_cases last : u = b + 1
      · simpa [last] using after
      · exact kept u ru (by omega)
    · rcases next_passed_peer other (valid.2 b (by omega)) after with old | read
      · exact (previous old).elim
      · refine ⟨b, ab, by omega, read, ?_⟩
        intro u bu ub
        have eq : u = b + 1 := by omega
        simpa [eq] using after

/-- A continuously blocking register prevents a fresh eligibility passage,
including arbitrary delays before publishing cs and entering actual code. -/
theorem stable_blocker_exclusion {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (ab : a ≤ b) (bf : b ≤ finish)
    (other : q ≠ p) (before : ¬ PassedPeer q (trace a p).pc)
    (blocks : ∀ r, a ≤ r → r < b → Blocks p q (trace r q).value) :
    ¬ PassedPeer q (trace b p).pc := by
  intro after
  obtain ⟨r, lo, hi, read, _⟩ := eligibility_read_history valid ab bf other before after
  exact read.2.choose_spec.2 (blocks r lo hi)

/-- At actual critical occupancy, each peer has a successful historical
eligibility read, followed only by controls retaining that read's credit. -/
theorem critical_eligibility_history {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (other : q ≠ p) (critical : (trace b p).pc = .cs) :
    ∃ r, r < b ∧ EligibilityRead (trace r) (commands r) p q ∧
      ∀ u, r < u → u ≤ b → PassedPeer q (trace u p).pc := by
  obtain ⟨r, _, hi, read, kept⟩ := eligibility_read_history valid (Nat.zero_le b) bf other
    (by simp [valid.1, initial, reset, PassedPeer]) (by simp [critical, PassedPeer])
  exact ⟨r, hi, read, kept⟩

/-- The stage 6-8 controls before the empty-list exit. -/
def Maintaining {n : Nat} : PC n → Prop
  | .delete _ | .add _ | .attempt .maintain _ _ | .tickWrite .maintain _ _
  | .pairDone .maintain => True
  | _ => False

def WaitingFor {n : Nat} (q : Proc n) (l : Local n) : Prop :=
  Maintaining l.pc ∧ q ∈ l.behind

/-- Other identifiers may be added or removed, but an exposed identifier
already in B survives every maintenance instruction and prevents its exit. -/
theorem ordinary_waiting_for {n : Nat} {cfg : Config n} {s : State n} {p q : Proc n}
    {l : Local n} (before : WaitingFor q (s p)) (peer : exposed (s q).value = true)
    (step : ordinary cfg s p = some l) : WaitingFor q l := by
  obtain ⟨maintain, member⟩ := before
  cases pc : (s p).pc <;> simp only [pc, Maintaining] at maintain
  case' attempt phase clock cp => cases phase
  case' tickWrite phase clock pending => cases phase
  case' pairDone phase => cases phase
  all_goals try contradiction
  case' attempt.maintain => cases clock <;> cases cp
  case' tickWrite.maintain => cases clock
  case' delete rest => cases rest
  case' add rest => cases rest
  all_goals simp only [ordinary, pc] at step
  all_goals try (rw [Option.map_eq_some_iff] at step; obtain ⟨out, _, rfl⟩ := step)
  all_goals repeat (split at step)
  all_goals try contradiction
  all_goals try (simp only [Option.some.injEq] at step; subst l)
  all_goals try (simp_all [WaitingFor, Maintaining, afterAttempt, Finset.mem_erase])
  all_goals try (split_ifs <;> trivial)
  all_goals try (intro eq; subst q; simp_all)
  all_goals simp only [bind, Option.bind_eq_some_iff] at step
  all_goals obtain ⟨out, _, step⟩ := step
  all_goals split at step
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at step
  all_goals subst l
  all_goals simpa [WaitingFor, Maintaining] using member

theorem next_waiting_for {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    {p q : Proc n} (before : WaitingFor q (s p)) (peer : exposed (s q).value = true)
    (noAbort : c ≠ .fail p) (step : next cfg s c = some t) : WaitingFor q (t p) := by
  cases c with
  | stutter => have eq := Option.some.inj step; simpa [← eq] using before
  | run actor =>
    obtain ⟨out, ordinaryStep, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor
      simpa using ordinary_waiting_for before peer ordinaryStep
    · simpa [eq] using before
  | request actor | complete actor | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp_all [WaitingFor, Maintaining])
      | simpa [eq] using before

/-- All interleavings are allowed. Only the observed peer's continued exposure
and absence of the waiter's own abort are needed to retain this one member. -/
theorem waiting_for_persists {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (ab : a ≤ b) (bf : b ≤ finish)
    (before : WaitingFor q (trace a p))
    (peer : ∀ r, a ≤ r → r < b → exposed (trace r q).value = true)
    (noAbort : ∀ r, a ≤ r → r < b → commands r ≠ .fail p) :
    WaitingFor q (trace b p) := by
  induction b, ab using Nat.le_induction with
  | base => exact before
  | succ b ab ih =>
    exact next_waiting_for
      (ih (by omega) (by intro r lo hi; exact peer r lo (by omega))
        (by intro r lo hi; exact noAbort r lo (by omega)))
      (peer b ab (by omega)) (noAbort b ab (by omega)) (valid.2 b (by omega))

/-- This is a stage 7 whole-register read, not a bit read inside either clock. -/
def AdditionRead {n : Nat} (s : State n) (c : Command n) (p q : Proc n) : Prop :=
  c = .run p ∧ ∃ rest b0 b1,
    (s p).pc = .add (q :: rest) ∧ (s q).value = .live .three b0 b1

theorem addition_starts_waiting {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {p q : Proc n} (read : AdditionRead s c p q)
    (step : next cfg s c = some t) : WaitingFor q (t p) := by
  obtain ⟨rfl, rest, b0, b1, pc, value⟩ := read
  simp only [next, ordinary, pc, value, Option.map_some, Option.some.injEq] at step
  subst t
  simp [WaitingFor, Maintaining]

/-- Once stage 7 has actually observed level three, p cannot even reach
permission while q remains exposed, unless p's original request aborts.
A later replacement request never discharges the original conclusion. -/
theorem addition_excludes_permission {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (ab : a < b) (bf : b ≤ finish)
    (read : AdditionRead (trace a) (commands a) p q)
    (peer : ∀ r, a < r → r < b → exposed (trace r q).value = true)
    (noAbort : ∀ r, a < r → r < b → commands r ≠ .fail p) :
    WaitingFor q (trace b p) ∧ ¬ PassedPeer q (trace b p).pc := by
  have kept := waiting_for_persists valid (by omega : a + 1 ≤ b) bf
    (addition_starts_waiting read (valid.2 a (by omega)))
    (by intro r lo hi; exact peer r (by omega) hi)
    (by intro r lo hi; exact noAbort r (by omega) hi)
  refine ⟨kept, ?_⟩
  have maintaining := kept.1
  cases pc : (trace b p).pc <;> simp_all [Maintaining, PassedPeer]

/-- Unconditional finite-history consequence: after the observed addition,
critical occupancy requires either the waiter's abort or a real loss of peer
exposure. These events are conclusions, never scheduling assumptions. -/
theorem critical_after_addition_requires_break {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish a b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (ab : a < b) (bf : b ≤ finish)
    (read : AdditionRead (trace a) (commands a) p q)
    (critical : (trace b p).pc = .cs) :
    ∃ r, a < r ∧ r < b ∧
      (commands r = .fail p ∨ exposed (trace r q).value = false) := by
  classical
  by_contra absent
  have peer : ∀ r, a < r → r < b → exposed (trace r q).value = true := by
    intro r lo hi
    cases h : exposed (trace r q).value
    · exact (absent ⟨r, lo, hi, Or.inr h⟩).elim
    · rfl
  have noAbort : ∀ r, a < r → r < b → commands r ≠ .fail p := by
    intro r lo hi abort
    exact absent ⟨r, lo, hi, Or.inl abort⟩
  have blocked := (addition_excludes_permission valid ab bf read peer noAbort).2
  exact blocked (by simp [critical, PassedPeer])

end EconomicalSolutions.Algorithm7

#print axioms EconomicalSolutions.Algorithm7.eligibility_read_history
#print axioms EconomicalSolutions.Algorithm7.stable_blocker_exclusion
#print axioms EconomicalSolutions.Algorithm7.critical_eligibility_history
#print axioms EconomicalSolutions.Algorithm7.waiting_for_persists
#print axioms EconomicalSolutions.Algorithm7.addition_excludes_permission
#print axioms EconomicalSolutions.Algorithm7.critical_after_addition_requires_break
