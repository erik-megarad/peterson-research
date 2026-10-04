module

public import Peterson.EssentialDekker.TwoProcess
public import Mathlib.Data.Nat.Find

@[expose] public section

/-! Figure 4 per-request progress. A finite certificate is checked by the kernel;
the infinite-execution proof uses only scheduling fairness and critical completion. -/
namespace Peterson.EssentialDekker.TwoProcess.Progress

structure Execution where
  state : Nat → State
  event : Nat → Option Proc

def Valid (E : Execution) : Prop :=
  (∃ turn, E.state 0 = initial turn) ∧
  ∀ n, E.state (n + 1) = match E.event n with
    | none => E.state n
    | some p => next (E.state n) p

def Pending (s : State) (p : Proc) : Prop :=
  s.pc p = .readTurn ∨ s.pc p = .readPeer ∨ s.pc p = .writeFalse ∨
  s.pc p = .writeTrue ∨ s.pc p = .guardSelf ∨ s.pc p = .guardPeer

def Request (E : Execution) (p : Proc) (n : Nat) : Prop :=
  (E.state n).pc p = .idle ∧ E.event n = some p

def Entry (E : Execution) (p : Proc) (n : Nat) : Prop :=
  (E.state n).pc p = .guardPeer ∧ (E.state n).flag (!p) = false ∧
  E.event n = some p

def ProtocolEnabled (s : State) (p : Proc) : Prop :=
  s.pc p ≠ .idle ∧ s.pc p ≠ .critical

/-- An actor continuously in the protocol must eventually take a step.
This never requires a successful observation or a request from an idle client. -/
def WeakProtocolFair (E : Execution) : Prop :=
  ∀ p n, (∀ m, n ≤ m → ProtocolEnabled (E.state m) p) →
    ∃ k, n ≤ k ∧ E.event k = some p

/-- Every critical occupancy eventually takes its actual completion step. -/
def CriticalCompletes (E : Execution) : Prop :=
  ∀ p n, (E.state n).pc p = .critical →
    ∃ k, n ≤ k ∧ (E.state k).pc p = .critical ∧ E.event k = some p

-- BEGIN GENERATED CERTIFICATE
def certificate (s : State) : Nat :=
  match s.pc0, s.pc1 with
  | .idle, .idle => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 1 else 1)))
  | .idle, .readTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 1 else 0) else (if s.turn then 1 else 1)))
  | .idle, .readPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 1 else 0) else (if s.turn then 1 else 1)))
  | .idle, .writeFalse => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 1 else 0) else (if s.turn then 1 else 0)))
  | .idle, .writeTrue => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 1 else 0) else (if s.turn then 1 else 1)))
  | .idle, .guardSelf => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 1 else 1) else (if s.turn then 1 else 0)))
  | .idle, .guardPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 1 else 1) else (if s.turn then 0 else 0)))
  | .idle, .critical => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 1 else 1) else (if s.turn then 0 else 0)))
  | .idle, .writeTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 1 else 1) else (if s.turn then 0 else 0)))
  | .idle, .clearFlag => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 1) else (if s.turn then 0 else 0)))
  | .readTurn, .idle => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 30)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 150 else 40)))
  | .readTurn, .readTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 64 else 19) else (if s.turn then 0 else 12)) else (if s.flag1 then (if s.turn then 59 else 0) else (if s.turn then 148 else 40)))
  | .readTurn, .readPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 17) else (if s.turn then 0 else 12)) else (if s.flag1 then (if s.turn then 171 else 0) else (if s.turn then 168 else 40)))
  | .readTurn, .writeFalse => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 15) else (if s.turn then 0 else 12)) else (if s.flag1 then (if s.turn then 197 else 0) else (if s.turn then 182 else 88)))
  | .readTurn, .writeTrue => (if s.flag0 then (if s.flag1 then (if s.turn then 64 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 57 else 0) else (if s.turn then 146 else 40)))
  | .readTurn, .guardSelf => (if s.flag0 then (if s.flag1 then (if s.turn then 64 else 23) else (if s.turn then 0 else 12)) else (if s.flag1 then (if s.turn then 55 else 40) else (if s.turn then 180 else 86)))
  | .readTurn, .guardPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 64 else 21) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 53 else 40) else (if s.turn then 0 else 0)))
  | .readTurn, .critical => (if s.flag0 then (if s.flag1 then (if s.turn then 116 else 37) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 51 else 40) else (if s.turn then 0 else 0)))
  | .readTurn, .writeTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 114 else 35) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 49 else 40) else (if s.turn then 0 else 0)))
  | .readTurn, .clearFlag => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 33) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 40) else (if s.turn then 0 else 0)))
  | .readPeer, .idle => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 106)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 144 else 46)))
  | .readPeer, .readTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 62 else 0) else (if s.turn then 0 else 104)) else (if s.flag1 then (if s.turn then 59 else 0) else (if s.turn then 142 else 46)))
  | .readPeer, .readPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 104)) else (if s.flag1 then (if s.turn then 171 else 0) else (if s.turn then 166 else 46)))
  | .readPeer, .writeFalse => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 104)) else (if s.flag1 then (if s.turn then 197 else 0) else (if s.turn then 178 else 0)))
  | .readPeer, .writeTrue => (if s.flag0 then (if s.flag1 then (if s.turn then 62 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 57 else 0) else (if s.turn then 140 else 46)))
  | .readPeer, .guardSelf => (if s.flag0 then (if s.flag1 then (if s.turn then 62 else 0) else (if s.turn then 0 else 104)) else (if s.flag1 then (if s.turn then 55 else 46) else (if s.turn then 176 else 0)))
  | .readPeer, .guardPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 62 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 53 else 46) else (if s.turn then 0 else 0)))
  | .readPeer, .critical => (if s.flag0 then (if s.flag1 then (if s.turn then 112 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 51 else 46) else (if s.turn then 0 else 0)))
  | .readPeer, .writeTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 110 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 49 else 46) else (if s.turn then 0 else 0)))
  | .readPeer, .clearFlag => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 108) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 46) else (if s.turn then 0 else 0)))
  | .writeFalse, .idle => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 96)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 44)))
  | .writeFalse, .readTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 60 else 0) else (if s.turn then 0 else 94)) else (if s.flag1 then (if s.turn then 59 else 0) else (if s.turn then 192 else 44)))
  | .writeFalse, .readPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 94)) else (if s.flag1 then (if s.turn then 171 else 0) else (if s.turn then 0 else 44)))
  | .writeFalse, .writeFalse => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 94)) else (if s.flag1 then (if s.turn then 197 else 0) else (if s.turn then 0 else 0)))
  | .writeFalse, .writeTrue => (if s.flag0 then (if s.flag1 then (if s.turn then 60 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 57 else 0) else (if s.turn then 190 else 44)))
  | .writeFalse, .guardSelf => (if s.flag0 then (if s.flag1 then (if s.turn then 60 else 0) else (if s.turn then 0 else 94)) else (if s.flag1 then (if s.turn then 55 else 44) else (if s.turn then 194 else 0)))
  | .writeFalse, .guardPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 60 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 53 else 44) else (if s.turn then 0 else 0)))
  | .writeFalse, .critical => (if s.flag0 then (if s.flag1 then (if s.turn then 102 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 51 else 44) else (if s.turn then 0 else 0)))
  | .writeFalse, .writeTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 100 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 49 else 44) else (if s.turn then 0 else 0)))
  | .writeFalse, .clearFlag => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 98) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 44) else (if s.turn then 0 else 0)))
  | .writeTrue, .idle => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 28)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 138 else 38)))
  | .writeTrue, .readTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 19) else (if s.turn then 0 else 10)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 136 else 38)))
  | .writeTrue, .readPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 17) else (if s.turn then 0 else 10)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 164 else 38)))
  | .writeTrue, .writeFalse => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 15) else (if s.turn then 0 else 10)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 174 else 84)))
  | .writeTrue, .writeTrue => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 134 else 38)))
  | .writeTrue, .guardSelf => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 23) else (if s.turn then 0 else 10)) else (if s.flag1 then (if s.turn then 132 else 38) else (if s.turn then 172 else 82)))
  | .writeTrue, .guardPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 21) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 130 else 38) else (if s.turn then 0 else 0)))
  | .writeTrue, .critical => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 37) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 128 else 38) else (if s.turn then 0 else 0)))
  | .writeTrue, .writeTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 35) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 126 else 38) else (if s.turn then 0 else 0)))
  | .writeTrue, .clearFlag => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 33) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 38) else (if s.turn then 0 else 0)))
  | .guardSelf, .idle => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 80 else 8)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 42)))
  | .guardSelf, .readTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 74 else 19) else (if s.turn then 78 else 6)) else (if s.flag1 then (if s.turn then 59 else 0) else (if s.turn then 186 else 42)))
  | .guardSelf, .readPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 17) else (if s.turn then 162 else 6)) else (if s.flag1 then (if s.turn then 171 else 0) else (if s.turn then 0 else 42)))
  | .guardSelf, .writeFalse => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 15) else (if s.turn then 160 else 6)) else (if s.flag1 then (if s.turn then 197 else 0) else (if s.turn then 0 else 92)))
  | .guardSelf, .writeTrue => (if s.flag0 then (if s.flag1 then (if s.turn then 74 else 0) else (if s.turn then 76 else 26)) else (if s.flag1 then (if s.turn then 57 else 0) else (if s.turn then 184 else 42)))
  | .guardSelf, .guardSelf => (if s.flag0 then (if s.flag1 then (if s.turn then 74 else 23) else (if s.turn then 158 else 6)) else (if s.flag1 then (if s.turn then 55 else 42) else (if s.turn then 188 else 90)))
  | .guardSelf, .guardPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 74 else 21) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 53 else 42) else (if s.turn then 0 else 0)))
  | .guardSelf, .critical => (if s.flag0 then (if s.flag1 then (if s.turn then 124 else 37) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 51 else 42) else (if s.turn then 0 else 0)))
  | .guardSelf, .writeTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 122 else 35) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 49 else 42) else (if s.turn then 0 else 0)))
  | .guardSelf, .clearFlag => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 33) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 42) else (if s.turn then 0 else 0)))
  | .guardPeer, .idle => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 72 else 4)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .guardPeer, .readTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 66 else 19) else (if s.turn then 70 else 2)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .guardPeer, .readPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 17) else (if s.turn then 156 else 2)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .guardPeer, .writeFalse => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 15) else (if s.turn then 154 else 2)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .guardPeer, .writeTrue => (if s.flag0 then (if s.flag1 then (if s.turn then 66 else 0) else (if s.turn then 68 else 24)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .guardPeer, .guardSelf => (if s.flag0 then (if s.flag1 then (if s.turn then 66 else 23) else (if s.turn then 152 else 2)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .guardPeer, .guardPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 66 else 21) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .guardPeer, .critical => (if s.flag0 then (if s.flag1 then (if s.turn then 120 else 37) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .guardPeer, .writeTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 118 else 35) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .guardPeer, .clearFlag => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 33) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .critical, .idle => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 1 else 1)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .critical, .readTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 1 else 1) else (if s.turn then 1 else 1)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .critical, .readPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 1) else (if s.turn then 1 else 1)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .critical, .writeFalse => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 1) else (if s.turn then 1 else 1)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .critical, .writeTrue => (if s.flag0 then (if s.flag1 then (if s.turn then 1 else 0) else (if s.turn then 1 else 1)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .critical, .guardSelf => (if s.flag0 then (if s.flag1 then (if s.turn then 1 else 1) else (if s.turn then 1 else 1)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .critical, .guardPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 1 else 1) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .critical, .critical => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .critical, .writeTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .critical, .clearFlag => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .writeTurn, .idle => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 1 else 1)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .writeTurn, .readTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 1 else 1) else (if s.turn then 1 else 1)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .writeTurn, .readPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 1) else (if s.turn then 1 else 1)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .writeTurn, .writeFalse => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 1) else (if s.turn then 1 else 1)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .writeTurn, .writeTrue => (if s.flag0 then (if s.flag1 then (if s.turn then 1 else 0) else (if s.turn then 1 else 1)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .writeTurn, .guardSelf => (if s.flag0 then (if s.flag1 then (if s.turn then 1 else 1) else (if s.turn then 1 else 1)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .writeTurn, .guardPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 1 else 1) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .writeTurn, .critical => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .writeTurn, .writeTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .writeTurn, .clearFlag => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .clearFlag, .idle => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 1 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .clearFlag, .readTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 1 else 0) else (if s.turn then 1 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .clearFlag, .readPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 1 else 0) else (if s.turn then 1 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .clearFlag, .writeFalse => (if s.flag0 then (if s.flag1 then (if s.turn then 1 else 0) else (if s.turn then 1 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .clearFlag, .writeTrue => (if s.flag0 then (if s.flag1 then (if s.turn then 1 else 0) else (if s.turn then 1 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .clearFlag, .guardSelf => (if s.flag0 then (if s.flag1 then (if s.turn then 1 else 0) else (if s.turn then 1 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .clearFlag, .guardPeer => (if s.flag0 then (if s.flag1 then (if s.turn then 1 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .clearFlag, .critical => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .clearFlag, .writeTurn => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
  | .clearFlag, .clearFlag => (if s.flag0 then (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)) else (if s.flag1 then (if s.turn then 0 else 0) else (if s.turn then 0 else 0)))
-- END GENERATED CERTIFICATE

/-- Rename the requester to false, preserving the reviewed transitions. -/
def orient (s : State) (p : Proc) : State :=
  if p then ⟨s.pc1, s.pc0, s.flag1, s.flag0, !s.turn⟩ else s

def rank (s : State) (p : Proc) : Nat := certificate (orient s p) / 2

def blocker (s : State) (p : Proc) : Proc :=
  if certificate (orient s p) % 2 = 0 then p else !p

def Certified (s : State) : Prop := certificate s ≠ 0

set_option maxHeartbeats 4000000 in
 theorem certificate_initial (p : Proc) : Certified (initial p) := by
  unfold Certified
  cases p <;> decide

set_option maxHeartbeats 4000000 in
 theorem certificate_step (s : State) (a : Proc) : Certified s → Certified (next s a) := by
  unfold Certified
  rcases s with ⟨x,y,f,g,t⟩
  cases x <;> cases y <;> cases f <;> cases g <;> cases t <;> cases a <;> decide

/- The finite certificate checks each possible step, not merely sampled runs. -/
set_option maxHeartbeats 8000000 in
 theorem certificate_descent (s : State) (p a : Proc) :
    Certified s → Pending s p → Pending (next s a) p →
    rank (next s a) p ≤ rank s p ∧
    (rank (next s a) p = rank s p →
      blocker (next s a) p = blocker s p ∧ a ≠ blocker s p) := by
  unfold Certified Pending
  rcases s with ⟨x,y,f,g,t⟩
  cases x <;> cases y <;> cases f <;> cases g <;> cases t <;> cases p <;> cases a <;>
    decide

set_option maxHeartbeats 4000000 in
 theorem certificate_active (s : State) (p : Proc) :
    Certified s → Pending s p → s.pc (blocker s p) ≠ .idle := by
  unfold Certified Pending
  rcases s with ⟨x,y,f,g,t⟩
  cases x <;> cases y <;> cases f <;> cases g <;> cases t <;> cases p <;> decide

end Peterson.EssentialDekker.TwoProcess.Progress
