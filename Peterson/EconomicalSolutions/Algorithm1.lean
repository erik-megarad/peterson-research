module

public import Cslib.Foundations.Semantics.LTS.Basic

@[expose] public section

/-! Peterson–Fischer, Economical Solutions, Algorithm 1 (restoration p. 3).
The collection’s economical-solutions guide describes the reviewed operation boundary.
Each shared access is one step. Payloads in write/guard locations are private
cached values; failure replaces the entire local state, so none can survive. -/
namespace EconomicalSolutions.Algorithm1

abbrev Proc := Bool

inductive Value where
  | O | T | F
  deriving DecidableEq, Repr

/-- Only locations needing a cache carry one. Dead caches are discarded. -/
inductive PC where
  | down | idle | read1 | write1 (v : Value) | read2 | self2
  | write2 (v : Value) | waitPeer | waitSelf (x : Value)
  | enter | cs | release
  deriving DecidableEq, Repr

structure Local where
  pc : PC
  q : Value
  deriving DecidableEq, Repr

structure State where
  p0 : Local
  p1 : Local
  deriving DecidableEq, Repr

/-- False names P0 (copy); true names P1 (complement). O uses the first
assignment's T default; the second assignment treats O separately. -/
def matching (p : Proc) : Value → Value
  | .O => .T
  | .T => if p then .F else .T
  | .F => if p then .T else .F

/-- One ordinary instruction, including private request and critical completion.
The peer parameter is consulted only in peer-read locations. -/
def ordinary (p : Proc) (l : Local) (peer : Value) : Option Local :=
  match l.pc with
  | .down => none
  | .idle => some { l with pc := .read1 }
  | .read1 => some { l with pc := .write1 (matching p peer) }
  | .write1 v => some ⟨.read2, v⟩
  | .read2 => some { l with pc := if peer = .O then .self2 else .write2 (matching p peer) }
  | .self2 => some { l with pc := .write2 l.q }
  | .write2 v => some ⟨.waitPeer, v⟩
  | .waitPeer => some { l with pc := if p && peer == .O then .enter else .waitSelf peer }
  | .waitSelf x => some { l with pc :=
      if (if p then x == l.q else x != l.q) then .enter else .waitPeer }
  | .enter => some { l with pc := .cs }
  | .cs => some { l with pc := .release }
  | .release => some ⟨.idle, .O⟩

inductive Command where
  | run (p : Proc) | fail (p : Proc) | restart (p : Proc) | stutter
  deriving DecidableEq, Repr

inductive Label where
  | request (p : Proc) | instruction (p : Proc) | entry (p : Proc)
  | complete (p : Proc) | fail (p : Proc) | restart (p : Proc) | stutter
  deriving DecidableEq, Repr

def State.local (s : State) (p : Proc) : Local := if p then s.p1 else s.p0

def State.setLocal (s : State) (p : Proc) (l : Local) : State :=
  if p then { s with p1 := l } else { s with p0 := l }

/-- Failure is enabled at every live location, including cs and pending writes.
It atomically removes the occupant, resets its register, and aborts its caches. -/
def next (s : State) : Command → Option State
  | .run p => (ordinary p (s.local p) (s.local (!p)).q).map (s.setLocal p)
  | .fail p => if (s.local p).pc = .down then none
      else some (s.setLocal p ⟨.down, .O⟩)
  | .restart p => if (s.local p).pc = .down then some (s.setLocal p ⟨.idle, .O⟩)
      else none
  | .stutter => some s

def label (s : State) : Command → Label
  | .run p => match (s.local p).pc with
      | .idle => .request p
      | .enter => .entry p
      | .cs => .complete p
      | _ => .instruction p
  | .fail p => .fail p
  | .restart p => .restart p
  | .stutter => .stutter

/-- The LTS directly wraps the operation interpreter, without a second semantics. -/
def lts : Cslib.LTS State Label :=
  ⟨fun s a t => ∃ c, next s c = some t ∧ label s c = a⟩

def initial : State := ⟨⟨.idle, .O⟩, ⟨.idle, .O⟩⟩

inductive Reachable : State → Prop where
  | initial : Reachable initial
  | step {s t : State} {a : Label} : Reachable s → lts.Tr s a t → Reachable t

def MutualExclusion (s : State) : Prop := ¬ (s.p0.pc = .cs ∧ s.p1.pc = .cs)

end EconomicalSolutions.Algorithm1
