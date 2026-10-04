import MultiReaderAtomic.Protocol

namespace MultiReaderAtomic

structure WriteRecord (α : Type) where
  id : Nat
  call : Nat
  index : Nat
  value : α
  start : Nat
  finish : Option Nat
  deriving DecidableEq

/-- Preceding writes finished strictly before invocation. -/
def Precedes (w : WriteRecord α) (start : Nat) : Prop :=
  ∃ finish, w.finish = some finish ∧ finish < start

/-- Initialization is a real alternative only until superseded before invocation.
A read can select any overlapping write, including a now-completed one. -/
def Eligible (ws : List (WriteRecord α)) (start finish : Nat)
    (witness : Option Nat) : Prop :=
  match witness with
  | none => ∀ w ∈ ws, ¬ Precedes w start
  | some id => ∃ w ∈ ws, w.id = id ∧ w.start < finish ∧
      ((Precedes w start ∧ ∀ other ∈ ws,
        Precedes other start → other.start ≤ w.start) ∨
       (∀ t, w.finish = some t → start < t))

/-- The value and ghost source come from the actual eligible write. -/
def Supplies (v₀ : α) (ws : List (WriteRecord α)) (sample : Sample α) : Prop :=
  match sample.witness with
  | none => sample.value = v₀ ∧ sample.source = 0
  | some id => ∃ w ∈ ws, w.id = id ∧ sample.value = w.value ∧ sample.source = w.index

structure Primitive (n : Nat) where
  id : Nat
  call : Nat
  register : Register n
  isWrite : Bool
  start : Nat
  finish : Option Nat := none
  witness : Option Nat := none

structure Call (n : Nat) (α : Type) where
  id : Nat
  process : Process n
  invoked : Nat
  writeIndex : Nat
  argument : Option α
  response : Option (Nat × Option (Sample α)) := none

inductive Phase (n : Nat) (α : Type) where
  | ready (program : Program n α)
  | reading (r : Register n) (start : Nat) (next : Sample (Value α r) → Program n α)
  | writing (r : Register n) (start : Nat) (next : Program n α)

structure Thread (n : Nat) (α : Type) where
  call : Nat
  writeIndex : Nat
  phase : Phase n α

structure State (n : Nat) (α : Type) where
  clock : Nat := 1
  nextWrite : Nat := 1
  threads : Process n → Option (Thread n α) := fun _ => none
  writes : (r : Register n) → List (WriteRecord (Value α r)) := fun _ => []
  primitives : List (Primitive n) := []
  calls : List (Call n α) := []

def initial : State n α := {}

def withThread (s : State n α) (p : Process n) (t : Option (Thread n α)) : State n α :=
  { s with clock := s.clock + 1, threads := Function.update s.threads p t }

def closePrimitive (events : List (Primitive n)) (id time : Nat)
    (witness : Option Nat := none) : List (Primitive n) :=
  events.map fun e => if e.id = id then { e with finish := some time, witness := witness } else e

def closeWrite (ws : List (WriteRecord α)) (id time : Nat) : List (WriteRecord α) :=
  ws.map fun w => if w.id = id then { w with finish := some time } else w

inductive Action (n : Nat) where
  | invoke (p : Process n) | localStep (p : Process n)
  | beginAccess (p : Process n) | endAccess (p : Process n) | respond (p : Process n)
  | idle
  deriving DecidableEq

/-- Only actual control-flow transitions are premises. No safety criterion is assumed. -/
inductive Step (v₀ : α) : State n α → Action n → State n α → Prop where
  | invokeWriter (s) (v : α) (free : s.threads .writer = none) :
      Step v₀ s (.invoke .writer)
        { withThread s .writer (some ⟨s.clock, s.nextWrite, .ready (writerProgram v)⟩) with
          nextWrite := s.nextWrite + 1
          calls := s.calls ++ [⟨s.clock, .writer, s.clock, s.nextWrite, some v, none⟩] }
  | invokeReader (s) (j : Fin n) (free : s.threads (.reader j) = none) :
      Step v₀ s (.invoke (.reader j))
        { withThread s (.reader j) (some ⟨s.clock, 0, .ready (readerProgram j)⟩) with
          calls := s.calls ++ [⟨s.clock, .reader j, s.clock, 0, none, none⟩] }
  | order (s) (p) (t : Thread n α) (next : Bool → Program n α) (b : Bool)
      (active : s.threads p = some t) (control : t.phase = .ready (.order next)) :
      Step v₀ s (.localStep p) (withThread s p (some {t with phase := .ready (next b)}))
  | token (s) (p) (t : Thread n α) (a b choice : Token) (next : Token → Program n α)
      (active : s.threads p = some t) (control : t.phase = .ready (.token a b next))
      (differentA : choice ≠ a) (differentB : choice ≠ b) :
      Step v₀ s (.localStep p) (withThread s p (some {t with phase := .ready (next choice)}))
  | beginRead (s) (p) (t : Thread n α) (r : Register n)
      (next : Sample (Value α r) → Program n α)
      (active : s.threads p = some t) (control : t.phase = .ready (.read r next)) :
      Step v₀ s (.beginAccess p)
        { withThread s p (some {t with phase := .reading r s.clock next}) with
          primitives := s.primitives ++ [⟨s.clock, t.call, r, false, s.clock, none, none⟩] }
  | endRead (s) (p) (t : Thread n α) (r : Register n) (start : Nat)
      (next : Sample (Value α r) → Program n α) (sample : Sample (Value α r))
      (active : s.threads p = some t) (control : t.phase = .reading r start next)
      (regular : Eligible (s.writes r) start s.clock sample.witness)
      (value : Supplies (initialValue v₀ r) (s.writes r) sample) :
      Step v₀ s (.endAccess p)
        { withThread s p (some {t with phase := .ready (next sample)}) with
          primitives := closePrimitive s.primitives start s.clock sample.witness }
  | beginWrite (s) (p) (t : Thread n α) (r : Register n) (v : Value α r)
      (next : Program n α) (active : s.threads p = some t)
      (control : t.phase = .ready (.write r v next)) (owner : registerOwner r = p) :
      Step v₀ s (.beginAccess p)
        { withThread s p (some {t with phase := .writing r s.clock next}) with
          primitives := s.primitives ++ [⟨s.clock, t.call, r, true, s.clock, none, none⟩]
          writes := Function.update s.writes r
            (s.writes r ++ [⟨s.clock, t.call, t.writeIndex, v, s.clock, none⟩]) }
  | endWrite (s) (p) (t : Thread n α) (r : Register n) (start : Nat)
      (next : Program n α) (active : s.threads p = some t)
      (control : t.phase = .writing r start next) :
      Step v₀ s (.endAccess p)
        { withThread s p (some {t with phase := .ready next}) with
          primitives := closePrimitive s.primitives start s.clock
          writes := Function.update s.writes r (closeWrite (s.writes r) start s.clock) }
  | respond (s) (p) (t : Thread n α) (result : Option (Sample α))
      (active : s.threads p = some t) (control : t.phase = .ready (.done result)) :
      Step v₀ s (.respond p)
        { withThread s p none with
          calls := s.calls.map fun c => if c.id = t.call then
            { c with response := some (s.clock, result) } else c }
  | idle (s) : Step v₀ s .idle {s with clock := s.clock + 1}

def lts (v₀ : α) : Cslib.LTS (State n α) (Action n) := ⟨Step v₀⟩
def Reachable (v₀ : α) (s : State n α) : Prop := ∃ trace, (lts v₀).MTr initial trace s

def Run (v₀ : α) (states : Nat → State n α) : Prop :=
  states 0 = initial ∧ ∀ k, ∃ a, Step v₀ (states k) a (states (k+1))

end MultiReaderAtomic
