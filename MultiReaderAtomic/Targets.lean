import MultiReaderAtomic.Model

/-! Protected M2b/M3 obligations. These are propositions, not asserted theorems.
All histories are taken from the Figure 1 transition system, not assumed atomic. -/
namespace MultiReaderAtomic

def Completed (c : Call n α) : Prop := ∃ time result, c.response = some (time, result)
def Returned (c : Call n α) (sample : Sample α) : Prop :=
  ∃ j time, c.process = .reader j ∧ c.response = some (time, some sample)

def APIBefore (a b : Call n α) : Prop :=
  ∃ time result, a.response = some (time, result) ∧ time < b.invoked

def PrimitiveBefore (a b : Primitive n) : Prop :=
  ∃ time, a.finish = some time ∧ time < b.start

/-- Source high-level operations must be complete and nonempty: no vacuous
ordering of an empty pending call. All their primitive events are compared. -/
def SourceBefore (events : List (Primitive n)) (a b : Call n α) : Prop :=
  Completed a ∧ Completed b ∧
  (∃ e ∈ events, e.call = a.id) ∧ (∃ e ∈ events, e.call = b.id) ∧
  ∀ ea ∈ events, ∀ eb ∈ events,
    ea.call = a.id → eb.call = b.id → PrimitiveBefore ea eb

/-- W₀ is the separately established initial write; real write identities are
assigned by the serial writer at invocation. Repeated values do not identify writes. -/
def WriteValue (v₀ : α) (history : Call n α → Prop) (index : Nat) (value : α) : Prop :=
  (index = 0 ∧ value = v₀) ∨
  ∃ c, history c ∧ c.process = .writer ∧ c.writeIndex = index ∧ c.argument = some value

def Provenance (v₀ : α) (history : Call n α → Prop)
    (before : Call n α → Call n α → Prop) : Prop :=
  ∀ c sample, history c → Returned c sample →
    WriteValue v₀ history sample.source sample.value ∧
    (sample.source = 0 ∨ ∃ w, history w ∧ w.process = .writer ∧
      w.writeIndex = sample.source ∧ ¬ before c w)

/-- The BC criterion is an output obligation for each selected precedence. -/
def IndexedCriterion (history : Call n α → Prop)
    (before : Call n α → Call n α → Prop) : Prop :=
  (∀ r r' x y, history r → history r' → Returned r x → Returned r' y →
    before r r' → x.source ≤ y.source) ∧
  (∀ w r x, history w → history r → w.process = .writer → Returned r x →
    before w r → w.writeIndex ≤ x.source)

structure OrderEntry (n : Nat) (α : Type) where
  id : Nat
  process : Process n
  value : α
  source : Nat

/-- A selected pending call may receive a response; an actual response is fixed. -/
def Fits (c : Call n α) (e : OrderEntry n α) : Prop :=
  e.id = c.id ∧ e.process = c.process ∧
  (c.process = .writer → c.argument = some e.value ∧ e.source = c.writeIndex) ∧
  (∀ time result, c.response = some (time, result) →
    match c.process, result with
    | .writer, none => True
    | .reader _, some sample => e.value = sample.value ∧ e.source = sample.source
    | _, _ => False)

/-- One shared order, with finite positions, for all selected operations.
Positions need not be contiguous. Thus this definition covers both a finite
prefix and a whole natural-number-indexed run without merely a per-prefix claim. -/
def AtomicOrder (v₀ : α) (history : Call n α → Prop)
    (before : Call n α → Call n α → Prop) : Prop :=
  ∃ selected : Nat → Option (OrderEntry n α), ∃ rank : Nat → Nat,
    selected 0 = some ⟨0, .writer, v₀, 0⟩ ∧ rank 0 = 0 ∧
    (∀ id e, selected id = some e → e.id = id) ∧
    (∀ id e, id ≠ 0 → selected id = some e → ∃ c, history c ∧ Fits c e) ∧
    (∀ c, history c → Completed c → ∃ e, selected c.id = some e ∧ Fits c e) ∧
    (∀ c e, history c → selected c.id = some e → Fits c e) ∧
    (∀ i j a b, selected i = some a → selected j = some b → rank i = rank j → i = j) ∧
    (∀ id e, id ≠ 0 → selected id = some e → 0 < rank id) ∧
    (∀ a b ea eb, history a → history b → selected a.id = some ea →
      selected b.id = some eb → before a b → rank a.id < rank b.id) ∧
    (∀ a b ea eb, history a → history b → selected a.id = some ea →
      selected b.id = some eb → a.process = b.process → a.invoked < b.invoked →
      rank a.id < rank b.id) ∧
    (∀ id e j, selected id = some e → e.process = .reader j →
      ∃ wid w, selected wid = some w ∧ w.process = .writer ∧
        w.source = e.source ∧ w.value = e.value ∧ rank wid < rank id ∧
        ∀ otherId other, selected otherId = some other → other.process = .writer →
          rank otherId < rank id → rank otherId ≤ rank wid)

def FiniteCorrectness (n : Nat) (α : Type) : Prop :=
  ∀ v₀ (s : State n α), 0 < n → Reachable v₀ s →
    Provenance v₀ (fun c => c ∈ s.calls) APIBefore ∧
    Provenance v₀ (fun c => c ∈ s.calls) (SourceBefore s.primitives) ∧
    IndexedCriterion (fun c => c ∈ s.calls) APIBefore ∧
    IndexedCriterion (fun c => c ∈ s.calls) (SourceBefore s.primitives) ∧
    AtomicOrder v₀ (fun c => c ∈ s.calls) APIBefore ∧
    AtomicOrder v₀ (fun c => c ∈ s.calls) (SourceBefore s.primitives)

/-- A whole-run history uses completed versions when a response eventually
exists, otherwise the unique indefinitely pending version. -/
def RunHistory (states : Nat → State n α) (c : Call n α) : Prop :=
  (∃ k, c ∈ (states k).calls) ∧
  (Completed c ∨ ¬ ∃ k later, later ∈ (states k).calls ∧ later.id = c.id ∧ Completed later)

def RunSourceBefore (states : Nat → State n α) (a b : Call n α) : Prop :=
  ∃ k, a ∈ (states k).calls ∧ b ∈ (states k).calls ∧ SourceBefore (states k).primitives a b

def WholeRunCorrectness (n : Nat) (α : Type) : Prop :=
  ∀ v₀ (states : Nat → State n α), 0 < n → Run v₀ states →
    Provenance v₀ (RunHistory states) APIBefore ∧
    Provenance v₀ (RunHistory states) (RunSourceBefore states) ∧
    IndexedCriterion (RunHistory states) APIBefore ∧
    IndexedCriterion (RunHistory states) (RunSourceBefore states) ∧
    AtomicOrder v₀ (RunHistory states) APIBefore ∧
    AtomicOrder v₀ (RunHistory states) (RunSourceBefore states)

/-- Source-facing criterion-to-order bridge, to be proved on actual histories;
criterion is not a Step or Reachable premise. -/
def CriterionBridge (n : Nat) (α : Type) : Prop :=
  ∀ v₀ (s : State n α), 0 < n → Reachable v₀ s →
    Provenance v₀ (fun c => c ∈ s.calls) (SourceBefore s.primitives) →
    IndexedCriterion (fun c => c ∈ s.calls) (SourceBefore s.primitives) →
    AtomicOrder v₀ (fun c => c ∈ s.calls) (SourceBefore s.primitives)

/-- Count actual accesses, including both reads in every expression. -/
def primitiveBudget (n : Nat) : Process n → Nat
  | .writer => 3*n + 5
  | .reader _ => 2*n + 8

/-- Scheduling and primitive termination are explicit separate hypotheses. -/
def ContinuedOwnScheduling (states : Nat → State n α) (p : Process n) : Prop :=
  ∀ k t, (states k).threads p = some t →
    (∃ m, k ≤ m ∧ (states m).threads p = none) ∨
    ∃ m u, k ≤ m ∧ (states m).threads p = some u ∧
      (states (m+1)).threads p ≠ some u

def TerminatingPrimitives (states : Nat → State n α) (p : Process n) : Prop :=
  ∀ k t, (states k).threads p = some t →
    (∀ r start next, t.phase = .reading r start next →
      ∃ m e, k ≤ m ∧ e ∈ (states m).primitives ∧ e.id = start ∧ e.finish.isSome) ∧
    (∀ r start next, t.phase = .writing r start next →
      ∃ m e, k ≤ m ∧ e ∈ (states m).primitives ∧ e.id = start ∧ e.finish.isSome)

def OwnCompletion (n : Nat) (α : Type) : Prop :=
  ∀ v₀ (states : Nat → State n α) p, 0 < n → Run v₀ states →
    ContinuedOwnScheduling states p → TerminatingPrimitives states p →
    ∀ k c, c ∈ (states k).calls → c.process = p →
      ∃ m completed, k ≤ m ∧ completed ∈ (states m).calls ∧
        completed.id = c.id ∧ Completed completed ∧
        ((states m).primitives.filter (fun e => e.call == c.id)).length ≤ primitiveBudget n p

end MultiReaderAtomic
