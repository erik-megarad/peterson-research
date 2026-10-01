import Peterson.EconomicalSolutions.Algorithm7Safety

/-! The list-control half of Algorithm 7's clock-observation bridge.
Two maintenance writes in the same clock require a new stage 7 scan, unless
the owner actually leaves maintenance in between. No ticking oracle is used. -/
set_option linter.unusedSimpArgs false
namespace EconomicalSolutions.Algorithm7

/-- A stage 7 read, regardless of the sampled level. -/
def AdditionScanRead {n : Nat} (s : State n) (c : Command n) (p q : Proc n) : Prop :=
  c = .run p ∧ ∃ rest, (s p).pc = .add (q :: rest)

/-- A real successful maintenance write in the selected clock. -/
def MaintenanceWrite {n : Nat} (s : State n) (c : Command n) (p : Proc n)
    (clock : Bool) : Prop :=
  c = .run p ∧ ∃ pending, (s p).pc = .tickWrite .maintain clock pending

/-- After a selected-clock write, another such write owes a fresh addition
read of q. Clock 0 may still have the current pair's clock-1 work in flight. -/
def OwesAddition {n : Nat} (q : Proc n) (clock : Bool) : PC n → Prop
  | .attempt .maintain true _ | .tickWrite .maintain true _ => clock = false
  | .pairDone .maintain | .delete _ => True
  | .add rest => q ∈ rest
  | _ => False

theorem maintenance_write_starts_owing {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {p q : Proc n} {clock : Bool}
    (write : MaintenanceWrite s c p clock) (step : next cfg s c = some t) :
    OwesAddition q clock (t p).pc := by
  obtain ⟨rfl, pending, pc⟩ := write
  simp only [next, ordinary, pc, Option.map_some, Option.some.injEq] at step
  subst t
  cases clock <;> simp [OwesAddition, afterAttempt]

theorem ordinary_owes_addition {n : Nat} {cfg : Config n} {s : State n}
    {p q : Proc n} {clock : Bool} {out : Local n} (other : q ≠ p)
    (before : OwesAddition q clock (s p).pc)
    (noRead : ¬ AdditionScanRead s (.run p) p q)
    (after : Maintaining out.pc) (step : ordinary cfg s p = some out) :
    OwesAddition q clock out.pc := by
  cases pc : (s p).pc <;> simp only [pc, OwesAddition] at before
  case' attempt phase active cp => cases phase <;> cases active
  case' tickWrite phase active pending => cases phase <;> cases active
  case' pairDone phase => cases phase
  all_goals try contradiction
  case' attempt.maintain.true => cases cp
  case' delete rest => cases rest
  case' add rest => cases rest
  case add.cons head rest =>
    by_cases eq : q = head
    · subst head
      exact (noRead ⟨rfl, rest, pc⟩).elim
    · cases value : (s head).value
      case' live level b0 b1 => cases level
      all_goals simp only [ordinary, pc, value, Option.some.injEq] at step
      all_goals subst out
      all_goals simpa [OwesAddition, eq] using before
  all_goals simp only [ordinary, pc] at step
  all_goals try (rw [Option.map_eq_some_iff] at step; obtain ⟨result, _, rfl⟩ := step)
  all_goals repeat (split at step)
  all_goals try contradiction
  all_goals try (simp only [Option.some.injEq] at step; subst out)
  all_goals try (simp_all [OwesAddition, Maintaining, afterAttempt, cfg.complete])
  all_goals try (split_ifs <;> simp_all [OwesAddition, Maintaining])
  all_goals simp only [bind, Option.bind_eq_some_iff] at step
  all_goals obtain ⟨result, _, step⟩ := step
  all_goals split at step
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at step
  all_goals subst out
  all_goals simp [OwesAddition, afterAttempt, before]

theorem next_owes_addition {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {p q : Proc n} {clock : Bool} (other : q ≠ p)
    (before : OwesAddition q clock (s p).pc)
    (noRead : ¬ AdditionScanRead s c p q) (after : Maintaining (t p).pc)
    (step : next cfg s c = some t) : OwesAddition q clock (t p).pc := by
  cases c with
  | stutter => have eq := Option.some.inj step; simpa [← eq] using before
  | run actor =>
    obtain ⟨out, ordinaryStep, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor
      simpa using ordinary_owes_addition other before noRead (by simpa using after) ordinaryStep
    · simpa [eq] using before
  | request actor | complete actor | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp_all [reset, Maintaining, OwesAddition])
      | simpa [eq] using before

/-- Between actual maintenance writes in one clock, every peer is sampled
by stage 7, or the owner has a non-maintenance control at an intervening state.
The latter explicitly includes the delayed empty-list exit and replacement
requests. Clock attempts and other-clock writes are not counted as samples. -/
theorem maintenance_writes_require_scan_or_departure {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish a b : Nat}
    {p q : Proc n} {clock : Bool} (valid : ValidPrefix cfg trace commands finish)
    (ab : a < b) (bf : b < finish) (other : q ≠ p)
    (first : MaintenanceWrite (trace a) (commands a) p clock)
    (second : MaintenanceWrite (trace b) (commands b) p clock) :
    ∃ r, a < r ∧ r < b ∧
      (AdditionScanRead (trace r) (commands r) p q ∨ ¬ Maintaining (trace r p).pc) := by
  classical
  by_contra absent
  have endMaintaining : Maintaining (trace b p).pc := by
    obtain ⟨_, pending, pc⟩ := second
    simp [pc, Maintaining]
  have kept : ∀ t, a + 1 ≤ t → t ≤ b → OwesAddition q clock (trace t p).pc := by
    intro t lo
    induction t, lo using Nat.le_induction with
    | base =>
      intro _
      exact maintenance_write_starts_owing first (valid.2 a (by omega))
    | succ t lo ih =>
      intro hi
      apply next_owes_addition other (ih (by omega))
      · intro read
        exact absent ⟨t, by omega, by omega, Or.inl read⟩
      · by_cases last : t + 1 = b
        · simpa [last] using endMaintaining
        · by_contra departed
          exact absent ⟨t + 1, by omega, by omega, Or.inr departed⟩
      · exact valid.2 t (by omega)
  have owing := kept b (by omega) (le_refl _)
  obtain ⟨_, pending, pc⟩ := second
  cases clock <;> simp_all [OwesAddition]

/-- During continuous level-three exposure, the intervening sample is exactly
the real addition used by the checked safety barrier. The departure alternative
is disjoint from remaining in maintenance throughout the open interval. -/
theorem maintenance_writes_observe_level_three_or_depart {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish a b : Nat}
    {p q : Proc n} {clock : Bool} (valid : ValidPrefix cfg trace commands finish)
    (ab : a < b) (bf : b < finish) (other : q ≠ p)
    (first : MaintenanceWrite (trace a) (commands a) p clock)
    (second : MaintenanceWrite (trace b) (commands b) p clock)
    (three : ∀ r, a < r → r < b → ∃ b0 b1, (trace r q).value = .live .three b0 b1) :
    (∃ r, a < r ∧ r < b ∧ AdditionRead (trace r) (commands r) p q) ∨
      (∃ r, a < r ∧ r < b ∧ ¬ Maintaining (trace r p).pc) := by
  obtain ⟨r, lo, hi, read | depart⟩ :=
    maintenance_writes_require_scan_or_departure valid ab bf other first second
  · obtain ⟨b0, b1, value⟩ := three r lo hi
    obtain ⟨cmd, rest, pc⟩ := read
    exact Or.inl ⟨r, lo, hi, cmd, rest, b0, b1, pc, value⟩
  · exact Or.inr ⟨r, lo, hi, depart⟩

/-- The list-control part of the observation bridge, composed with the
existing addition barrier. In one uninterrupted maintenance interval, a
second write in the selected clock forces waiting for a continuously exposed
level-three peer. An abort cannot be hidden in the maintenance interval. -/
theorem two_maintenance_writes_force_waiting {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish a b : Nat}
    {p q : Proc n} {clock : Bool} (valid : ValidPrefix cfg trace commands finish)
    (ab : a < b) (bf : b < finish) (other : q ≠ p)
    (first : MaintenanceWrite (trace a) (commands a) p clock)
    (second : MaintenanceWrite (trace b) (commands b) p clock)
    (maintain : ∀ r, a < r → r < b → Maintaining (trace r p).pc)
    (three : ∀ r, a < r → r < b → ∃ b0 b1, (trace r q).value = .live .three b0 b1) :
    ∃ r, a < r ∧ r < b ∧ AdditionRead (trace r) (commands r) p q ∧
      WaitingFor q (trace b p) ∧ ¬ PassedPeer q (trace b p).pc := by
  rcases maintenance_writes_observe_level_three_or_depart valid ab bf other first second three
    with ⟨r, lo, hi, read⟩ | ⟨r, lo, hi, depart⟩
  · have noAbort : ∀ u, r < u → u < b → commands u ≠ .fail p := by
      intro u ru ub fail
      have step := valid.2 u (by omega)
      rw [fail] at step
      have nextMaint : Maintaining (trace (u + 1) p).pc := by
        by_cases last : u + 1 = b
        · obtain ⟨_, pending, pc⟩ := second
          simp [last, pc, Maintaining]
        · exact maintain (u + 1) (by omega) (by omega)
      simp only [next] at step
      split at step
      · contradiction
      · simp only [Option.some.injEq] at step
        rw [← step] at nextMaint
        simp [reset, Maintaining] at nextMaint
    have barrier := addition_excludes_permission valid hi (by omega) read
      (by
        intro u ru ub
        obtain ⟨b0, b1, value⟩ := three u (by omega) ub
        simp [value, exposed]) noAbort
    exact ⟨r, lo, hi, read, barrier⟩
  · exact (depart (maintain r lo hi)).elim

end EconomicalSolutions.Algorithm7

#print axioms EconomicalSolutions.Algorithm7.maintenance_writes_require_scan_or_departure
#print axioms EconomicalSolutions.Algorithm7.maintenance_writes_observe_level_three_or_depart

#print axioms EconomicalSolutions.Algorithm7.two_maintenance_writes_force_waiting
