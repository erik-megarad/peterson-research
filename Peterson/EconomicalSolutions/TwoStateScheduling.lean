import Peterson.EconomicalSolutions.TwoStateNecessary

/-! The binary scheduling obstruction for Theorem 3-3. The program grammar,
initialization, safety and progress premises are those of TwoStateNecessary.
No symmetry or finite private-memory assumption is added. -/
namespace EconomicalSolutions.TwoState.Program

variable {V : Type u} {M : Type v} (P : Program V M)

/-- A fresh request after initialization or failure/restart. Ordinary repeated
requests in the underlying model still retain their full private history. -/
def waitingStart (p : Bool) : Local V M := ⟨.trying, P.start p, P.dead⟩

/-- The complete local instruction history when every peer read returns g. -/
def against (P : Program V M) (g : V) (p : Bool) : Nat → Local V M
  | 0 => P.waitingStart p
  | n + 1 => P.execute p (P.against g p n) g

/-- An actual reset/restart/request sequence, not an assignment of hidden state. -/
def newRequest (s : State V M) (p : Bool) : State V M :=
  P.next (P.next (P.next s (.fail p)) (.restart p)) (.request p)

@[simp] theorem newRequest_self (s : State V M) (p : Bool) :
    P.newRequest s p p = P.waitingStart p := by simp [newRequest, next, waitingStart]

@[simp] theorem newRequest_other (s : State V M) (p : Bool) :
    P.newRequest s p (!p) = s (!p) := by cases p <;> simp [newRequest, next]

theorem newRequest_reachable {s : State V M} (hs : P.Reachable s) (p : Bool) :
    P.Reachable (P.newRequest s p) :=
  .step (.request p) (.step (.restart p) (.step (.fail p) hs))

/-- Progress really supplies the comparison state: p has a fresh pending
request beside a critical peer publishing g. The finite prefix may fail p. -/
theorem initial_critical_twin (safe : P.Safe) (progress : P.Progress) (g : V)
    (binary : ∀ v : V, v = P.dead ∨ v = g) (p : Bool) :
    ∃ s, P.Reachable s ∧ s p = P.waitingStart p ∧
      (s (!p)).phase = .cs ∧ (s (!p)).value = g := by
  let a := P.next (P.next P.initial (.request (!p))) (.fail p)
  have ra : P.Reachable a := .step (.fail p) (.step (.request (!p)) .initial)
  have pa : (a (!p)).phase = .trying := by cases p <;> simp [a, next, initial]
  have da : (a (!(!p))).phase = .down := by simp [a, next]
  obtain ⟨n, hn⟩ := P.solo_entry progress ra (!p) pa da
  let s := P.newRequest (P.solo a (!p) n) p
  have rs : P.Reachable s := P.newRequest_reachable (P.solo_reachable ra (!p) n) p
  have sp : s p = P.waitingStart p := P.newRequest_self _ p
  have sc : (s (!p)).phase = .cs := by simpa only [s, newRequest_other] using hn
  refine ⟨s, rs, sp, sc, ?_⟩
  apply P.critical_binary safe progress g binary rs (!p) sc
  simp [sp, waitingStart]

theorem against_eq_solo (s : State V M) (g : V) (p : Bool)
    (hp : s p = P.waitingStart p) (hg : (s (!p)).value = g) :
    ∀ n, P.solo s p n p = P.against g p n := by
  intro n
  induction n with
  | zero => exact hp
  | succ n ih => simp only [solo, run_self, solo_other, ih, hg, against]

/-- Safety forbids entry along either actor's constant-g history. Each finite
prefix is replayed next to its own reachable critical twin; actor code need
not coincide. Delaying that critical visit is only a finite safety argument. -/
theorem against_pending (safe : P.Safe) (progress : P.Progress) (g : V)
    (binary : ∀ v : V, v = P.dead ∨ v = g) (p : Bool) :
    ∀ n, (P.against g p n).phase = .trying := by
  obtain ⟨s, rs, sp, sc, sg⟩ := P.initial_critical_twin safe progress g binary p
  have eq := P.against_eq_solo s g p sp sg
  have nc : ∀ n, (P.solo s p n p).phase ≠ .cs := by
    intro n hc
    have peer : (P.solo s p n (!p)).phase = .cs := by simpa using sc
    exact safe _ (P.solo_reachable rs p n) p hc peer
  have pend := P.solo_pending s p (by simp [sp, waitingStart]) nc
  intro n
  rw [← eq n]
  exact pend n

/-- If both constant-g histories eventually stay at g, their two tail records
can be reached together. First advance false beside a critical true; then
actually reset true and advance it while false keeps g. -/
theorem stable_joint_reachable (safe : P.Safe) (progress : P.Progress) (g : V)
    (binary : ∀ v : V, v = P.dead ∨ v = g) (k : Bool → Nat)
    (stable : ∀ p n, k p ≤ n → (P.against g p n).value = g) :
    ∃ s, P.Reachable s ∧ ∀ p, s p = P.against g p (k p) := by
  obtain ⟨a, ra, ap, _, ag⟩ := P.initial_critical_twin safe progress g binary false
  let b := P.solo a false (k false)
  have rb : P.Reachable b := P.solo_reachable ra false (k false)
  have bp : b false = P.against g false (k false) :=
    P.against_eq_solo a g false ap ag _
  let c := P.newRequest b true
  have rc : P.Reachable c := P.newRequest_reachable rb true
  have cp : c true = P.waitingStart true := P.newRequest_self b true
  have cq : c false = P.against g false (k false) := by
    exact (P.newRequest_other b true).trans bp
  have cg : (c (!true)).value = g := by simpa only [Bool.not_true, cq] using stable false _ (Nat.le_refl _)
  let s := P.solo c true (k true)
  refine ⟨s, P.solo_reachable rc true _, ?_⟩
  intro p
  cases p with
  | false => exact (P.solo_other c true (k true)).trans cq
  | true => exact P.against_eq_solo c g true cp cg _

/-- A concrete fair round-robin schedule and the number of instructions of
each actor in its finite prefixes. Counts do not bound private state. -/
def alternatingActor (n : Nat) : Bool := n % 2 == 1

def instructionCount (p : Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => instructionCount p n + if alternatingActor n = p then 1 else 0

def alternating (P : Program V M) (s : State V M) : Nat → State V M
  | 0 => s
  | n + 1 => P.next (P.alternating s n) (.run (alternatingActor n))

def alternatingRun (s : State V M) : P.Run where
  state := P.alternating s
  command := fun n => .run (alternatingActor n)
  valid _ := rfl

theorem alternatingActor_next (n : Nat) : alternatingActor (n + 1) = !(alternatingActor n) := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h
  · have h' : (n + 1) % 2 = 1 := by omega
    simp [alternatingActor, h, h']
  · have h' : (n + 1) % 2 = 0 := by omega
    simp [alternatingActor, h, h']

theorem alternating_local (s : State V M) (g : V) (k : Bool → Nat)
    (hs : ∀ p, s p = P.against g p (k p))
    (stable : ∀ p n, k p ≤ n → (P.against g p n).value = g) :
    ∀ n p, P.alternating s n p = P.against g p (k p + instructionCount p n) := by
  intro n
  induction n with
  | zero => intro p; simpa only [alternating, instructionCount, Nat.add_zero] using hs p
  | succ n ih =>
    intro p
    by_cases e : alternatingActor n = p
    · simp only [alternating, run_self, ih, instructionCount, e, ↓reduceIte]
      rw [stable (!p) _ (Nat.le_add_right _ _)]
      rw [← Nat.add_assoc]
      rfl
    · have ep : p = !(alternatingActor n) := by
        cases p <;> cases ha : alternatingActor n <;> simp_all
      rw [alternating, ep, run_other, ih]
      congr 2
      simp only [instructionCount, ← ep, ite_eq_right (by exact e), Nat.add_zero]

/-- When both constant-g histories stabilize at g, the reachable joined state
has a concrete admissible infinite continuation with both requests pending.
This discharges scheduling and completion, rather than assuming deadlock. -/
theorem stable_joint_obstruction (safe : P.Safe) (progress : P.Progress) (g : V)
    (binary : ∀ v : V, v = P.dead ∨ v = g) (k : Bool → Nat)
    (stable : ∀ p n, k p ≤ n → (P.against g p n).value = g) : False := by
  obtain ⟨s, rs, hs⟩ := P.stable_joint_reachable safe progress g binary k stable
  have pend : ∀ n p, (P.alternating s n p).phase = .trying := by
    intro n p
    rw [P.alternating_local s g k hs stable n p]
    exact P.against_pending safe progress g binary p _
  have adm : P.Admissible (P.alternatingRun s) := by
    constructor
    · intro n p _
      by_cases e : alternatingActor n = p
      · exact ⟨n, Nat.le_refl _, Or.inl (by simp [alternatingRun, e])⟩
      · have ep : (!(alternatingActor n)) = p := by
          cases p <;> cases ha : alternatingActor n <;> simp_all
        exact ⟨n + 1, Nat.le_succ _, Or.inl (by simp [alternatingRun, alternatingActor_next, ep])⟩
    · intro n p hc
      have hp := pend n p
      simp only [alternatingRun] at hc
      rw [hp] at hc
      cases hc
  obtain ⟨m, _, hm⟩ := P.progress_reachable progress rs (P.alternatingRun s) rfl adm
    0 false (pend 0 false)
  rcases hm with hm | hm
  · have hp := pend (m + 1) false
    have hc : (P.alternating s (m + 1) false).phase = .cs := hm.2.2
    rw [hp] at hc
    cases hc
  · cases hm

/-- Binary-specific necessary scheduling condition. In at least one actor's
actual instruction history against a constant nondead peer, dead is published
arbitrarily late. The remaining lower-bound obligation is to turn those
arbitrarily late dead observations into an admissible infinite bypass run. -/
theorem binary_cofinal_dead (safe : P.Safe) (progress : P.Progress) (g : V)
    (binary : ∀ v : V, v = P.dead ∨ v = g) :
    ∃ p, ∀ n, ∃ m, n ≤ m ∧ (P.against g p m).value = P.dead := by
  classical
  by_contra h
  have stable : ∀ p, ∃ n, ∀ m, n ≤ m → (P.against g p m).value = g := by
    intro p
    have hp : ¬ ∀ n, ∃ m, n ≤ m ∧ (P.against g p m).value = P.dead := by
      intro hh; exact h ⟨p, hh⟩
    push Not at hp
    obtain ⟨n, hn⟩ := hp
    exact ⟨n, fun m hm => (binary _).resolve_left (hn m hm)⟩
  choose k hk using stable
  exact P.stable_joint_obstruction safe progress g binary k hk

end EconomicalSolutions.TwoState.Program

#print axioms EconomicalSolutions.TwoState.Program.initial_critical_twin
#print axioms EconomicalSolutions.TwoState.Program.against_pending
#print axioms EconomicalSolutions.TwoState.Program.stable_joint_reachable
#print axioms EconomicalSolutions.TwoState.Program.stable_joint_obstruction
#print axioms EconomicalSolutions.TwoState.Program.binary_cofinal_dead
