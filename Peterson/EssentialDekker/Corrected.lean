import Cslib.Foundations.Semantics.LTS.Basic

/-! Figure 6 with the owner-selected `≥` correction. Each shared access is
separate, count scans ascend through peers, and expressions short-circuit
left to right. Parameter m represents n=m+2 processes. -/
namespace Peterson.EssentialDekker.Corrected

abbrev Proc (m : Nat) := Fin (m + 2)
abbrev Level (m : Nat) := Fin (m + 1)

inductive PC (m : Nat) where
  | idle | writeTurn (j : Level m) | readTurn (j : Level m)
  | scan (j : Level m) (guard : Bool) (cursor : Level m) (count : Nat)
  | writeFlag (j : Level m) (high : Bool) | guardSelf (j : Level m)
  | critical | exit
  deriving DecidableEq, Repr

structure State (m : Nat) where
  flag : Proc m → Fin (m + 2)
  turn : Level m → Proc m
  pc : Proc m → PC m
  deriving DecidableEq

def peer (p : Proc m) (c : Level m) : Proc m :=
  if h : c.val < p.val then ⟨c.val, by omega⟩ else ⟨c.val + 1, by omega⟩

def State.setPC (s : State m) (p : Proc m) (pc : PC m) : State m :=
  { s with pc := Function.update s.pc p pc }

def passed (j : Level m) : PC m :=
  if h : j.val + 1 < m + 1 then .writeTurn ⟨j.val + 1, h⟩ else .critical

/-- An idle actor's selected step is an optional private request. It is never
required by protocol fairness. A critical actor's step is completion. -/
def next (s : State m) (p : Proc m) : State m :=
  match s.pc p with
  | .idle => s.setPC p (.writeTurn 0)
  | .writeTurn j =>
      ({ s with turn := Function.update s.turn j p }).setPC p (.readTurn j)
  | .readTurn j => s.setPC p
      (if s.turn j ≠ p then .writeFlag j true else .scan j false 0 0)
  | .scan j guard c count =>
      let count' := count + if j.val + 1 ≤ (s.flag (peer p c)).val then 1 else 0
      s.setPC p (if h : c.val + 1 < m + 1 then
        .scan j guard ⟨c.val + 1, h⟩ count'
      else if guard then
        (if count' < m + 2 - (j.val + 1) then passed j else .readTurn j)
      else .writeFlag j (decide (count' < m + 2 - (j.val + 1))))
  | .writeFlag j high =>
      let value : Fin (m + 2) := ⟨if high then j.val + 1 else j.val, by split <;> omega⟩
      ({ s with flag := Function.update s.flag p value }).setPC p (.guardSelf j)
  | .guardSelf j => s.setPC p
      (if (s.flag p).val = j.val + 1 then .scan j true 0 0 else .readTurn j)
  | .critical => s.setPC p .exit
  | .exit => ({ s with flag := Function.update s.flag p 0 }).setPC p .idle

def initial (m : Nat) : State m :=
  { flag := fun _ => 0, turn := fun _ => 0, pc := fun _ => .idle }

def lts (m : Nat) : Cslib.LTS (State m) (Proc m) := ⟨fun s p t => t = next s p⟩

def run (s : State m) (actors : List (Proc m)) : State m := actors.foldl next s

end Peterson.EssentialDekker.Corrected
