import Peterson.EconomicalSolutions.Algorithm1Safety

/-! The reviewed progress boundary, kept separate from certificate construction. -/
namespace EconomicalSolutions.Algorithm1

/-- Exactly the entry protocol, including the delayed entry action. -/
def pendingPC : PC → Bool
  | .read1 | .write1 _ | .read2 | .self2 | .write2 _ | .waitPeer | .waitSelf _ | .enter => true
  | _ => false

def Pending (s : State) (p : Proc) : Prop := pendingPC (s.local p).pc = true

/-- Release is scheduled too; idle and down never owe participation. -/
def protocolPC (pc : PC) : Bool := pendingPC pc || pc == .release

def owedPC (pc : PC) : Bool := protocolPC pc || pc == .cs

def acts (c : Command) (p : Proc) : Bool := c == .run p || c == .fail p

def outcome (s : State) (c : Command) (p : Proc) : Bool :=
  label s c == .entry p || label s c == .fail p

structure Run where
  state : Nat → State
  command : Nat → Command
  initialized : state 0 = initial
  valid : ∀ n, next (state n) (command n) = some (state (n + 1))

def Run.event (r : Run) (n : Nat) : Label := label (r.state n) (r.command n)

/-- An enabled ordinary instruction or own failure must eventually occur.
No favorable-read scheduling is required. -/
def ProtocolScheduling (r : Run) : Prop :=
  ∀ n p, protocolPC ((r.state n).local p).pc = true →
    ∃ m, n ≤ m ∧ acts (r.command m) p = true

/-- The client eventually completes critical code or fails. -/
def CriticalCompletion (r : Run) : Prop :=
  ∀ n p, ((r.state n).local p).pc = .cs →
    ∃ m, n ≤ m ∧ (r.event m = .complete p ∨ r.event m = .fail p)

/-- Service of the original pending request, with no intervening abort or entry. -/
def Served (r : Run) (p : Proc) (start finish : Nat) : Prop :=
  start ≤ finish ∧ r.event finish = .entry p ∧
    ∀ k, start ≤ k → k < finish →
      Pending (r.state k) p ∧ r.event k ≠ .fail p ∧ r.event k ≠ .entry p

end EconomicalSolutions.Algorithm1
