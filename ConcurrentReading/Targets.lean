import ConcurrentReading.Model

namespace ConcurrentReading

/-- General integrity obligation; not a proved theorem. -/
def Integrity : Prop :=
  ∀ (α : Type) (n : Nat), 0 < n → ∀ (v : α) (privateData : Fin n → α) s,
    Reachable v privateData s → ∀ t i call sample,
    (t, Event.readReturn i call sample) ∈ s.history →
    sample.torn = false ∧ ∃ k ti,
      sample.datum.origin = some k ∧
      (ti, Event.writeInvoke k sample.datum.value) ∈ s.history ∧ ti < t

inductive OpId (n : Nat) where
  | write (index : Nat) | read (i : Fin n) (call : Nat)
  deriving DecidableEq, Repr

def Invoked (h : List (Nat × Event α n)) (o : OpId n) (t : Nat) : Prop :=
  match o with
  | .write k => ∃ v, (t, .writeInvoke k v) ∈ h
  | .read i c => (t, .readInvoke i c) ∈ h

def Responded (h : List (Nat × Event α n)) (o : OpId n) (t : Nat) : Prop :=
  match o with
  | .write k => (t, .writeReturn k) ∈ h
  | .read i c => ∃ s, (t, .readReturn i c s) ∈ h

def Before (xs : List (OpId n)) (a b : OpId n) : Prop :=
  ∃ l m r, xs = l ++ [a] ++ m ++ [b] ++ r

/-- A sequential register execution includes W0 first; read values come from the
latest preceding write. Read sources are ghost indices, never value matching. -/
inductive Sequential : Nat → α → List (OpId n × Option (Datum α)) → Prop where
  | nil : Sequential k v []
  | write : Sequential k v rest → Sequential old oldv ((.write k, some ⟨v, some k⟩) :: rest)
  | read : Sequential k v rest → Sequential k v ((.read i c, some ⟨v, some k⟩) :: rest)

def responseId : Event α n → Option (OpId n)
  | .writeReturn k => some (.write k)
  | .readReturn i c _ => some (.read i c)
  | _ => none

/-- Selected pending operations get responses only at/after the prefix boundary. -/
structure Linearization (s : State α n) where
  extension : List (Nat × Event α n)
  order : List (OpId n × Option (Datum α))
  extensionResponses : ∀ t e, (t, e) ∈ extension → s.clock ≤ t ∧
    match e with
    | .writeReturn k => (∃ ti, Invoked s.history (.write k) ti) ∧
        ¬ ∃ tr, Responded s.history (.write k) tr
    | .readReturn i c _ => (∃ ti, Invoked s.history (.read i c) ti) ∧
        ¬ ∃ tr, Responded s.history (.read i c) tr
    | _ => False
  responseUnique : ((s.history ++ extension).filterMap (fun te => responseId te.2)).Nodup
  eventTimes : (s.history ++ extension).Pairwise (fun a b => a.1 < b.1)
  unique : (order.map Prod.fst).Nodup
  /-- Exactly completed operations of the extended history are retained. -/
  coverage : ∀ o, o ∈ order.map Prod.fst ↔ ∃ t, Responded (s.history ++ extension) o t
  invoked : ∀ o, o ∈ order.map Prod.fst → ∃ t, Invoked s.history o t
  realtime : ∀ a b ta tb, Responded (s.history ++ extension) a ta →
    Invoked s.history b tb → ta < tb → b ∈ order.map Prod.fst → Before (order.map Prod.fst) a b
  initialFirst : ∃ v rest, order = (.write 0, some ⟨v, some 0⟩) :: rest
  writeValues : ∀ k d, (.write k, d) ∈ order →
    ∃ t v, (t, .writeInvoke k v) ∈ s.history ∧ d = some ⟨v, some k⟩
  readValues : ∀ t i c sample, (t, .readReturn i c sample) ∈ s.history ++ extension →
    (.read i c, some sample.datum) ∈ order
  legal : ∃ v, Sequential 0 v order

/-- One order for all readers, with selected pending responses. Unproved. -/
def CommonOrdering : Prop :=
  ∀ (α : Type) (n : Nat), 0 < n → ∀ (v : α) (privateData : Fin n → α) s,
    Reachable v privateData s → Nonempty (Linearization s)

/-- The proposed source-index proof interface, not a model assumption. -/
def SourceOrder : Prop :=
  ∀ (α : Type) (n : Nat), 0 < n → ∀ (v : α) (privateData : Fin n → α) s,
    Reachable v privateData s → ∀ t i c sample,
    (t, Event.readReturn i c sample) ∈ s.history → ∃ k,
      sample.datum.origin = some k ∧
      (∀ j tj, (tj, Event.writeReturn j) ∈ s.history → tj < c → j ≤ k) ∧
      (∃ ti val, (ti, Event.writeInvoke k val) ∈ s.history ∧ ti < t) ∧
      (∀ t' i' c' sample', (t', Event.readReturn i' c' sample') ∈ s.history →
        t < c' → ∃ k', sample'.datum.origin = some k' ∧ k ≤ k')

inductive Process (n : Nat) where
  | writer | reader (i : Fin n)
  deriving DecidableEq

def owner : Action α n → Process n
  | .invokeWrite _ | .writer => .writer
  | .invokeRead i | .reader i _ => .reader i

def busy (s : State α n) : Process n → Prop
  | .writer => s.writer.pc ≠ 0
  | .reader i => (s.readers i).pc ≠ 0

/-- No invocation can remain pending throughout an interval containing this many
of its own primitive actions. Raw begin/end actions abstract terminating physical
operations; physical waiting contributes no protocol action. Unproved. -/
def OwnCompletion : Prop :=
  ∀ (α : Type) (n : Nat), 0 < n → ∀ (v : α) (privateData : Fin n → α)
    (states : Nat → State α n) (actions : Nat → Action α n),
    Reachable v privateData (states 0) →
    (∀ t, step (states t) (actions t) = some (states (t + 1))) →
    ∀ p T, busy (states 0) p →
      ((List.range T).filter (fun t => decide (owner (actions t) = p))).length ≥ 16 + 6 * n →
      ∃ t, t ≤ T ∧ ¬ busy (states t) p

end ConcurrentReading
