module

public import CircularElection.Model
public import Mathlib.Data.Nat.Log

@[expose] public section
namespace CircularElection
variable {n : Nat} {Id : Type} [LinearOrder Id]

/-- Maximum is a property of immutable owners, never of the current carrier. -/
def IsMaximum (owner : Fin n → Id) (p : Fin n) : Prop := ∀ q, owner q ≤ owner p

/-- Unproved target: every first announcement has the maximum original owner. -/
def ElectionSafety (owner : Fin n → Id) : Prop :=
  ∀ as s, BeforeFirst owner (initial owner) as s →
    ∀ p, (s.process p).pc = .elected → IsMaximum owner p

structure Execution (owner : Fin n → Id) where
  state : Nat → State n Id
  action : Nat → Action n
  starts : state 0 = initial owner
  steps : ∀ t, (lts owner).Tr (state t) (action t) (state (t + 1))

/-- Ordinal k names an occurrence on one FIFO edge, independently of its value.
All sent occurrences must eventually leave that edge and enter its inbox. -/
def DeliveryFair {owner : Fin n → Id} (e : Execution owner) : Prop :=
  ∀ p t k, k < (e.state t).sent p →
    ∃ u, t ≤ u ∧ k < (e.state u).delivered p

def LocalEnabled (owner : Fin n → Id) (s : State n Id) (p : Fin n) : Prop :=
  ∃ a t, actProcess a = some p ∧ (lts owner).Tr s a t

/-- Weak fairness: continuous enabledness implies a later local instruction.
It places no bound on delay and makes no deadlock-freedom assumption. -/
def LocalFair {owner : Fin n → Id} (e : Execution owner) : Prop :=
  ∀ p t, (∀ u, t ≤ u → LocalEnabled owner (e.state u) p) →
    ∃ u, t ≤ u ∧ actProcess (e.action u) = some p

/-- Unproved target. Infinite stuttering is permitted in executions; only the
explicit delivery/local fairness premises restrict it. -/
def EventualElection (owner : Fin n → Id) : Prop :=
  ∀ e : Execution owner, DeliveryFair e → LocalFair e →
    ∃ t, Announced (e.state t)

/-- Unproved uniform target, including n=1 and every unfair finite prefix.
The actual send counter increments on every active and relay edge send. -/
def MessageComplexity : Prop :=
  ∃ C : Nat, 0 < C ∧ ∀ (n : Nat), 0 < n →
    ∀ (Id : Type) [LinearOrder Id] (owner : Fin n → Id), Function.Injective owner →
      ∀ as s, BeforeFirst owner (initial owner) as s →
        s.sends ≤ C * n * (1 + Nat.log 2 n)

/-- R2 correctness targets have positive size and distinct identifier premises.
This is a proposition naming work still to prove, not an axiom or theorem. -/
def CorrectElection : Prop :=
  ∀ (n : Nat), 0 < n → ∀ (Id : Type) [LinearOrder Id] (owner : Fin n → Id),
    Function.Injective owner → ElectionSafety owner ∧ EventualElection owner

end CircularElection
