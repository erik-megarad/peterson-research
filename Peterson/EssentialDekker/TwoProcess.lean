module

public import Cslib.Foundations.Semantics.LTS.Basic

@[expose] public section

/-! Figure 4 of Peterson's Essential Dekker, page 3. Sequential consistency;
each shared access is a separate transition. Local assignment results live in
the writeTrue/writeFalse control locations. No fairness is assumed. -/
namespace Peterson.EssentialDekker.TwoProcess

/-- false and true name the two actors, not flag values. -/
abbrev Proc := Bool

inductive PC where
  | idle | readTurn | readPeer | writeFalse | writeTrue
  | guardSelf | guardPeer | critical | writeTurn | clearFlag
  deriving DecidableEq, Repr

structure State where
  pc0 : PC
  pc1 : PC
  flag0 : Bool
  flag1 : Bool
  turn : Proc
  deriving DecidableEq, Repr

def State.pc (s : State) (p : Proc) : PC := if p then s.pc1 else s.pc0
def State.flag (s : State) (p : Proc) : Bool := if p then s.flag1 else s.flag0

def State.setPC (s : State) (p : Proc) (pc : PC) : State :=
  if p then { s with pc1 := pc } else { s with pc0 := pc }

def State.setFlag (s : State) (p : Proc) (flag : Bool) : State :=
  if p then { s with flag1 := flag } else { s with flag0 := flag }

/-- Selecting an idle actor makes an optional private request. Selecting a
critical actor completes its critical section; turn and flag writes follow
separately. Actors may be left unselected for any length of time. -/
def next (s : State) (p : Proc) : State :=
  match s.pc p with
  | .idle => s.setPC p .readTurn
  | .readTurn => s.setPC p (if s.turn = p then .writeTrue else .readPeer)
  | .readPeer => s.setPC p (if s.flag (!p) then .writeFalse else .writeTrue)
  | .writeFalse => (s.setFlag p false).setPC p .guardSelf
  | .writeTrue => (s.setFlag p true).setPC p .guardSelf
  | .guardSelf => s.setPC p (if s.flag p then .guardPeer else .readTurn)
  | .guardPeer => s.setPC p (if s.flag (!p) then .readTurn else .critical)
  | .critical => s.setPC p .writeTurn
  | .writeTurn => { s.setPC p .clearFlag with turn := !p }
  | .clearFlag => (s.setFlag p false).setPC p .idle

def initial (turn : Proc) : State := ⟨.idle, .idle, false, false, turn⟩

def lts : Cslib.LTS State Proc := ⟨fun s p t => t = next s p⟩

/-- Every finite interleaving, including arbitrarily many completed requests. -/
inductive Reachable : State → Prop where
  | initial (turn : Proc) : Reachable (initial turn)
  | step {s t : State} (p : Proc) : Reachable s → lts.Tr s p t → Reachable t

def MutualExclusion (s : State) : Prop := ¬ (s.pc0 = .critical ∧ s.pc1 = .critical)

/-- After the own-flag test succeeds, the actor keeps its flag true through
entry and critical occupancy. Only that actor can write its flag. -/
def FlagDiscipline (s : State) : Prop :=
  ((s.pc0 = .guardPeer ∨ s.pc0 = .critical) → s.flag0 = true) ∧
  ((s.pc1 = .guardPeer ∨ s.pc1 = .critical) → s.flag1 = true)

def Invariant (s : State) : Prop := FlagDiscipline s ∧ MutualExclusion s

set_option maxHeartbeats 800000 in
/-- Case analysis checks the compact invariant on all states, including
unreachable states that satisfy it. Each leaf is a kernel-checked proposition. -/
theorem invariant_step (s : State) (p : Proc) : Invariant s → Invariant (next s p) := by
  rcases s with ⟨pc0, pc1, flag0, flag1, turn⟩
  cases p <;> cases pc0 <;> cases pc1 <;>
    simp_all [Invariant, FlagDiscipline, MutualExclusion, next,
      State.pc, State.flag, State.setPC, State.setFlag]
  all_goals cases flag0 <;> cases flag1 <;> cases turn <;> simp_all

theorem invariant_initial (turn : Proc) : Invariant (initial turn) := by
  simp [Invariant, FlagDiscipline, MutualExclusion, initial]

theorem reachable_invariant {s : State} (h : Reachable s) : Invariant s := by
  induction h with
  | initial turn => exact invariant_initial turn
  | step p _ edge ih =>
    change _ = next _ p at edge
    subst_vars
    exact invariant_step _ p ih

/-- Figure 4 repeated mutual exclusion, for either initial turn and every finite
reachable state. There is no fairness or bound on requests, steps, or pauses. -/
theorem repeated_mutual_exclusion {s : State} (h : Reachable s) : MutualExclusion s :=
  (reachable_invariant h).2

end Peterson.EssentialDekker.TwoProcess

#print axioms Peterson.EssentialDekker.TwoProcess.repeated_mutual_exclusion
