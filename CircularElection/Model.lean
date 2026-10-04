module

public import Cslib.Foundations.Semantics.LTS.Basic

/-! Publication-specific asynchronous ring model. Edges are indexed by their sender.
The counters are ghost observations and never affect local control. -/
@[expose] public section

namespace CircularElection

inductive PC where
  | firstSend | firstReceive | secondSend | secondReceive | compare
  | relayReceive | relaySend | elected
  deriving DecidableEq, Repr

structure Local (Id : Type) where
  pc : PC
  tid : Id
  ntid : Option Id := none
  nntid : Option Id := none
  deriving DecidableEq, Repr

structure State (n : Nat) (Id : Type) where
  process : Fin n → Local Id
  edge : Fin n → List Id
  inbox : Fin n → List Id
  sent : Fin n → Nat
  delivered : Fin n → Nat
  sends : Nat

inductive Action (n : Nat) where
  | send (p : Fin n)
  | receive (p : Fin n)
  | compare (p : Fin n)
  | deliver (p : Fin n)
  | idle
  deriving DecidableEq, Repr

variable {n : Nat} {Id : Type} [LinearOrder Id]

def next (p : Fin n) : Fin n := ⟨(p.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt p.isLt)⟩

def initial (owner : Fin n → Id) : State n Id where
  process p := ⟨.firstSend, owner p, none, none⟩
  edge _ := []
  inbox _ := []
  sent _ := 0
  delivered _ := 0
  sends := 0

/-- A local instruction's result: local state, remaining inbox, optional real send. -/
def localStep (owner : Id) (a : Action n) (l : Local Id) (q : List Id) :
    Option (Local Id × List Id × Option Id) :=
  match a, l.pc with
  | .send _, .firstSend => some ({l with pc := .firstReceive}, q, some l.tid)
  | .send _, .secondSend => match l.ntid with
    | some v => some ({l with pc := .secondReceive}, q, some (max l.tid v))
    | none => none
  | .send _, .relaySend => some ({l with pc := .relayReceive}, q, some l.tid)
  | .receive _, .firstReceive => match q with
    | [] => none
    | v :: rest => some ({l with
        pc := if v = owner then .elected else .secondSend,
        ntid := some v}, rest, none)
  | .receive _, .secondReceive => match q with
    | [] => none
    | v :: rest => some ({l with
        pc := if v = owner then .elected else .compare,
        nntid := some v}, rest, none)
  | .receive _, .relayReceive => match q with
    | [] => none
    | v :: rest => some ({l with
        pc := if v = owner then .elected else .relaySend,
        tid := v}, rest, none)
  | .compare _, .compare => match l.ntid, l.nntid with
    | some v, some w =>
      if max l.tid w ≤ v then
        some (⟨.firstSend, v, none, none⟩, q, none)
      else some (⟨.relayReceive, l.tid, none, none⟩, q, none)
    | _, _ => none
  | _, _ => none

def actProcess : Action n → Option (Fin n)
  | .send p | .receive p | .compare p => some p
  | _ => none

def commitLocal (s : State n Id) (p : Fin n)
    (r : Local Id × List Id × Option Id) : State n Id :=
  let base := {s with
    process := Function.update s.process p r.1,
    inbox := Function.update s.inbox p r.2.1}
  match r.2.2 with
  | none => base
  | some v => {base with
      edge := Function.update s.edge p (s.edge p ++ [v]),
      sent := Function.update s.sent p (s.sent p + 1),
      sends := s.sends + 1}

/-- Total scheduler interface; `none` means that instruction is disabled. -/
def execute (owner : Fin n → Id) (s : State n Id) (a : Action n) : Option (State n Id) :=
  match a with
  | .idle => some s
  | .deliver p => match s.edge p with
    | [] => none
    | v :: rest => some {s with
        edge := Function.update s.edge p rest,
        inbox := Function.update s.inbox (next p) (s.inbox (next p) ++ [v]),
        delivered := Function.update s.delivered p (s.delivered p + 1)}
  | .send p | .receive p | .compare p =>
      (localStep (owner p) a (s.process p) (s.inbox p)).map (commitLocal s p)

def lts (owner : Fin n → Id) : Cslib.LTS (State n Id) (Action n) where
  Tr s a t := execute owner s a = some t

def Reachable (owner : Fin n → Id) (s : State n Id) : Prop :=
  ∃ as, (lts owner).MTr (initial owner) as s

def Announced (s : State n Id) : Prop := ∃ p, (s.process p).pc = .elected

/-- Every source state precedes detection; the last state may announce. -/
inductive BeforeFirst (owner : Fin n → Id) : State n Id → List (Action n) → State n Id → Prop
  | nil (s) : BeforeFirst owner s [] s
  | cons {s t u a as} : ¬ Announced s → (lts owner).Tr s a t →
      BeforeFirst owner t as u → BeforeFirst owner s (a :: as) u

/-- Executable finite trace, using precisely the same transition relation. -/
def runPrefix (owner : Fin n → Id) (s : State n Id) : List (Action n) → Option (State n Id)
  | [] => some s
  | a :: as => (execute owner s a).bind (fun t => runPrefix owner t as)

end CircularElection
