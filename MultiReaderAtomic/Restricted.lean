import MultiReaderAtomic.Counterexample

/-! Explicit reconstruction: writer cancellation operands execute RC then FC.
Reader operands retain both orders; all accepted accesses remain original Steps. -/
namespace MultiReaderAtomic

/-- Every original Step is available except an FC-first transition when the
writer is currently at one of its cancellation-pair order nodes. -/
def RestrictedStep (v₀ : α) (s : State n α) (a : Action n) (s' : State n α) : Prop :=
  Step v₀ s a s' ∧
  (a ≠ .localStep .writer ∨ ∀ t next, s.threads .writer = some t →
    t.phase = .ready (.order next) →
    s'.threads .writer = some {t with phase := .ready (next true)})

theorem writer_pair_rc_before_fc
    (j : Fin n) (next : Sample Token → Sample Token → Program n α) :
    (fun leftFirst : Bool => if leftFirst then
      Program.read (.rc j) (fun x => Program.read (.fc j) (fun y => next x y))
      else Program.read (.fc j) (fun y => Program.read (.rc j) (fun x => next x y))) true =
      Program.read (.rc j) (fun x => Program.read (.fc j) (fun y => next x y)) := rfl

def restrictedLts (v₀ : α) : Cslib.LTS (State n α) (Action n) := ⟨RestrictedStep v₀⟩

def RestrictedReachable (v₀ : α) (s : State n α) : Prop :=
  ∃ trace, (restrictedLts v₀).MTr initial trace s

def RestrictedRun (v₀ : α) (states : Nat → State n α) : Prop :=
  states 0 = initial ∧ ∀ k, ∃ a, RestrictedStep v₀ (states k) a (states (k+1))

theorem restricted_step_original {v₀ : α} {s s' : State n α} {a : Action n}
    (h : RestrictedStep v₀ s a s') : Step v₀ s a s' := h.1

theorem restricted_reachable_original {v₀ : α} {s : State n α}
    (h : RestrictedReachable v₀ s) : Reachable v₀ s := by
  rcases h with ⟨trace, ht⟩
  have convert : ∀ {x y : State n α} {trace : List (Action n)},
      (restrictedLts v₀).MTr x trace y → (lts v₀).MTr x trace y := by
    intro x y trace run
    induction run with
    | refl => exact Cslib.LTS.MTr.refl
    | stepL edge rest ih =>
        exact Cslib.LTS.MTr.stepL (lts := lts v₀) edge.1 ih
  exact ⟨trace, convert ht⟩

theorem restricted_run_original {v₀ : α} {states : Nat → State n α}
    (h : RestrictedRun v₀ states) : Run v₀ states := by
  exact ⟨h.1, fun k => by rcases h.2 k with ⟨a, ha⟩; exact ⟨a, ha.1⟩⟩

def RestrictedFiniteCorrectness (n : Nat) (α : Type) : Prop :=
  ∀ v₀ (s : State n α), 0 < n → RestrictedReachable v₀ s →
    Provenance v₀ (fun c => c ∈ s.calls) APIBefore ∧
    Provenance v₀ (fun c => c ∈ s.calls) (SourceBefore s.primitives) ∧
    IndexedCriterion (fun c => c ∈ s.calls) APIBefore ∧
    IndexedCriterion (fun c => c ∈ s.calls) (SourceBefore s.primitives) ∧
    AtomicOrder v₀ (fun c => c ∈ s.calls) APIBefore ∧
    AtomicOrder v₀ (fun c => c ∈ s.calls) (SourceBefore s.primitives)

def RestrictedRunHistory (states : Nat → State n α) (c : Call n α) : Prop :=
  RunHistory states c

def RestrictedRunSourceBefore (states : Nat → State n α) (a b : Call n α) : Prop :=
  RunSourceBefore states a b

def RestrictedWholeRunCorrectness (n : Nat) (α : Type) : Prop :=
  ∀ v₀ (states : Nat → State n α), 0 < n → RestrictedRun v₀ states →
    Provenance v₀ (RestrictedRunHistory states) APIBefore ∧
    Provenance v₀ (RestrictedRunHistory states) (RestrictedRunSourceBefore states) ∧
    IndexedCriterion (RestrictedRunHistory states) APIBefore ∧
    IndexedCriterion (RestrictedRunHistory states) (RestrictedRunSourceBefore states) ∧
    AtomicOrder v₀ (RestrictedRunHistory states) APIBefore ∧
    AtomicOrder v₀ (RestrictedRunHistory states) (RestrictedRunSourceBefore states)

def RestrictedCriterionBridge (n : Nat) (α : Type) : Prop :=
  ∀ v₀ (s : State n α), 0 < n → RestrictedReachable v₀ s →
    Provenance v₀ (fun c => c ∈ s.calls) (SourceBefore s.primitives) →
    IndexedCriterion (fun c => c ∈ s.calls) (SourceBefore s.primitives) →
    AtomicOrder v₀ (fun c => c ∈ s.calls) (SourceBefore s.primitives)

def RestrictedOwnCompletion (n : Nat) (α : Type) : Prop :=
  ∀ v₀ (states : Nat → State n α) p, 0 < n → RestrictedRun v₀ states →
    ContinuedOwnScheduling states p → TerminatingPrimitives states p →
    ∀ k c, c ∈ (states k).calls → c.process = p →
      ∃ m completed, k ≤ m ∧ completed ∈ (states m).calls ∧
        completed.id = c.id ∧ Completed completed ∧
        ((states m).primitives.filter (fun e => e.call == c.id)).length ≤ primitiveBudget n p

theorem initial_restricted_reachable (v₀ : α) :
    RestrictedReachable (n := n) v₀ initial := by
  exact ⟨[], Cslib.LTS.MTr.refl⟩

end MultiReaderAtomic
