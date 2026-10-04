module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.Nat.Log
public import Peterson.EconomicalSolutions.Algorithm2ScanBridge

@[expose] public section

/-! Algorithm 2's source-close interpreter. Every shared access is a separate
step. The arbitrary fixed enumeration is configuration, never a scheduler
restriction; no tree-uniqueness premise occurs in the transition relation. -/
namespace EconomicalSolutions.Algorithm2

abbrev Value := ScanBridge.Value
abbrev dead := ScanBridge.dead

def height (n : Nat) : Nat := Nat.clog 2 n
def capacity (n : Nat) : Nat := 2 ^ height n
abbrev Leaf (n : Nat) := Fin (capacity n)
abbrev Proc (n : Nat) := Fin n

def bit (i k : Nat) : Bool := (i / 2 ^ (k - 1)) % 2 == 1

def Opponent (i j k : Nat) : Prop :=
  j / 2 ^ k = i / 2 ^ k ∧ bit j k ≠ bit i k

/-- All real populations n>=1 and all fixed complete, duplicate-free scan
orders. No run property, ownership or uniqueness is part of this structure. -/
structure Config (n : Nat) where
  positive : 0 < n
  order : Proc n → Nat → List (Leaf n)
  nodup : ∀ p k, (order p k).Nodup
  complete : ∀ p k j, j ∈ order p k ↔ Opponent p.val j.val k

inductive Continuation where
  | first | second | wait
  deriving DecidableEq, Repr

/-- Payloads are private state, including the remaining enumeration and cached
whole pairs. Pass and empty-scan return are separately scheduled local steps. -/
inductive PC (n : Nat) where
  | down | idle
  | scan (c : Continuation) (k : Nat) (remaining : List (Leaf n))
  | write1 (k : Nat) (v : Value)
  | self2 (k : Nat)
  | write2 (k : Nat) (v : Value)
  | waitSelf (k : Nat) (x : Value)
  | pass (k : Nat)
  | enter | cs | release
  deriving DecidableEq, Repr

structure Local (n : Nat) where
  pc : PC n
  q : Value
  deriving DecidableEq, Repr

abbrev State (n : Nat) := Proc n → Local n

/-- Dummy leaves have no local state, cannot be scheduled, and always read dead. -/
def visible {n : Nat} (s : State n) (j : Leaf n) : Value :=
  if h : j.val < n then (s ⟨j.val, h⟩).q else dead

def setLocal {n : Nat} (s : State n) (p : Proc n) (l : Local n) : State n :=
  fun i => if i = p then l else s i

def scan {n : Nat} (cfg : Config n) (p : Proc n) (c : Continuation) (k : Nat) : PC n :=
  .scan c k (cfg.order p k)

def matching {n : Nat} (p : Proc n) (k : Nat) (x : Value) : Value :=
  ⟨k, Bool.xor (bit p.val k) x.flag⟩

/-- Interpret a returned sample without another shared access. In particular,
second-assignment fallback still requires a separate own-register read. -/
def resume {n : Nat} (cfg : Config n) (p : Proc n) (c : Continuation)
    (k : Nat) (x : Value) : PC n :=
  match c with
  | .first => .write1 k (if x.level = k then matching p k x else ⟨k, true⟩)
  | .second => if x.level = k then .write2 k (matching p k x) else .self2 k
  | .wait => if k < x.level then scan cfg p .wait k
      else if x.level < k then .pass k else .waitSelf k x

/-- One ordinary instruction. The only opponent read is at a nonempty scan;
only self2 and waitSelf read the owner's whole pair for a decision/cache. -/
def ordinary {n : Nat} (cfg : Config n) (p : Proc n) (s : State n) : Option (Local n) :=
  let l := s p
  match l.pc with
  | .down => none
  | .idle => some { l with pc := if height n = 0 then .enter else scan cfg p .first 1 }
  | .scan c k [] => some { l with pc := resume cfg p c k dead }
  | .scan c k (j :: rest) =>
      let x := visible s j
      some { l with pc := if k ≤ x.level then resume cfg p c k x else .scan c k rest }
  | .write1 k v => some ⟨scan cfg p .second k, v⟩
  | .self2 k => some { l with pc := .write2 k l.q }
  | .write2 k v => some ⟨scan cfg p .wait k, v⟩
  | .waitSelf k x => some { l with pc :=
      if (Bool.xor (bit p.val k) (x == l.q)) then scan cfg p .wait k else .pass k }
  | .pass k => some { l with pc :=
      if (k < height n) then scan cfg p .first (k + 1) else .enter }
  | .enter => some { l with pc := .cs }
  | .cs => some { l with pc := .release }
  | .release => some ⟨.idle, dead⟩

inductive Command (n : Nat) where
  | run (p : Proc n) | fail (p : Proc n) | restart (p : Proc n) | stutter
  deriving DecidableEq, Repr

inductive Label (n : Nat) where
  | request (p : Proc n) | instruction (p : Proc n) | entry (p : Proc n)
  | complete (p : Proc n) | fail (p : Proc n) | restart (p : Proc n) | stutter
  deriving DecidableEq, Repr

/-- Failure replaces the entire local state; no pending read, scan suffix,
write cache, or critical occupancy survives. Only real processes can act. -/
def next {n : Nat} (cfg : Config n) (s : State n) : Command n → Option (State n)
  | .run p => (ordinary cfg p s).map (setLocal s p)
  | .fail p => if (s p).pc = .down then none else some (setLocal s p ⟨.down, dead⟩)
  | .restart p => if (s p).pc = .down then some (setLocal s p ⟨.idle, dead⟩) else none
  | .stutter => some s

def label {n : Nat} (s : State n) : Command n → Label n
  | .run p => match (s p).pc with
      | .idle => .request p
      | .enter => .entry p
      | .cs => .complete p
      | _ => .instruction p
  | .fail p => .fail p
  | .restart p => .restart p
  | .stutter => .stutter

/-- Observational metadata for the actual one-register QMAX read. This is
computed from the pre-state, not stored communication or a second transition. -/
def scanRead {n : Nat} (s : State n) : Command n → Option (Proc n × Leaf n × Value)
  | .run p => match (s p).pc with
      | .scan _ _ (j :: _) => some (p, j, visible s j)
      | _ => none
  | _ => none

def lts {n : Nat} (cfg : Config n) : Cslib.LTS (State n) (Label n) :=
  ⟨fun s a t => ∃ c, next cfg s c = some t ∧ label s c = a⟩

def initial (n : Nat) : State n := fun _ => ⟨.idle, dead⟩

inductive Reachable {n : Nat} (cfg : Config n) : State n → Prop where
  | initial : Reachable cfg (initial n)
  | step {s t : State n} {a : Label n} : Reachable cfg s → (lts cfg).Tr s a t → Reachable cfg t

def MutualExclusion {n : Nat} (s : State n) : Prop :=
  ∀ p q, (s p).pc = .cs → (s q).pc = .cs → p = q

/-- The exact all-n safety target is proved in Algorithm2Refinement. No fairness, failure bound,
representative uniqueness, or order choice narrows this proposition. -/
def SafetyTarget : Prop :=
  ∀ n (cfg : Config n) s, Reachable cfg s → MutualExclusion s

end EconomicalSolutions.Algorithm2
