import Peterson.EconomicalSolutions.Algorithm7

/-! Strict level-two publication FIFO is false for the reviewed Algorithm 7.
Commands below are individual interpreter steps, including explicit local controls.
No clock, phase or successful guard is supplied as an execution oracle. -/
namespace EconomicalSolutions.Algorithm7.Counterexample
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def config : Config 2 where
  order p := if p = 0 then [1] else [0]
  nodup := by decide
  complete := by decide

def runs (p : Fin 2) (count : Nat) : List (Command 2) := List.replicate count (.run p)

/-- The seven level-one pairs include P0's required fourth clock-0 tick.
The two maintenance pairs occur only after BOTH complete deletion/addition scans. -/
def commands : List (Command 2) :=
  [.request 0, .request 1] ++ runs 0 4 ++ runs 1 4 ++ runs 0 1 ++ runs 1 1 ++
  runs 0 9 ++ runs 1 11 ++ runs 0 11 ++ runs 1 11 ++ runs 0 11 ++ runs 1 11 ++ runs 0 11 ++
  runs 0 2 ++ runs 1 2 ++ runs 1 2 ++ runs 0 2 ++
  runs 0 4 ++ runs 1 4 ++ runs 1 11 ++ runs 0 11 ++ runs 0 2 ++ runs 1 2 ++
  runs 1 11 ++ runs 0 11 ++ runs 1 11 ++ runs 0 11 ++ runs 1 11 ++ runs 0 11 ++
  runs 0 11 ++ [.complete 0] ++ runs 0 1 ++ runs 1 13 ++ [.complete 1] ++ runs 1 1

def runCommands (cs : List (Command 2)) : Option (State 2) :=
  cs.foldlM (next config) (initial 2)

def replayState (t : Nat) : State 2 := (runCommands (commands.take t)).getD (initial 2)
def command (t : Nat) : Command 2 := commands[t]?.getD .stutter
def replayEvent (t : Nat) : Label 2 := label (replayState t) (command t)

/-- Reproducible certificate text from the actual interpreter. This printer is
untrusted: every emitted state and edge is subsequently checked by the kernel.
The empty lists printed here are specific to this witness; the edge check
rejects any list disagreement. Taking commands as input avoids evaluating the
whole printer during routine module compilation. -/
def localSource (l : Local 2) : String :=
  let short (s : String) := (s.replace "EconomicalSolutions.Algorithm7." "").replace
    "EconomicalSolutions.Algorithm3." "Algorithm3."
  "⟨" ++ short (reprStr l.value) ++ ", " ++ short (reprStr l.pc) ++ ", ∅, " ++
    toString l.count0 ++ ", " ++ toString l.count1 ++ "⟩"

def certificateSource (cs : List (Command 2)) : String :=
  "import Peterson.EconomicalSolutions.Algorithm7Replay\n\n" ++
  "/-! Explicit prestate certificate printed from the actual interpreter.\n" ++
  "Regenerate with `#eval IO.FS.writeFile \"Peterson/EconomicalSolutions/Algorithm7Certificate.lean\" certificateSource commands`\n" ++
  "in namespace EconomicalSolutions.Algorithm7.Counterexample after importing Algorithm7Replay.\n" ++
  "The printer is untrusted; Algorithm7Counterexample checks every edge. -/\n" ++
  "namespace EconomicalSolutions.Algorithm7.Counterexample\n" ++
  "def snapshots : Array (Local 2 × Local 2) := #[\n" ++
  String.intercalate ",\n" ((List.range cs.length).map fun t =>
    "  -- State " ++ toString t ++ "\n  (" ++ localSource (((runCommands (cs.take t)).getD (initial 2)) 0) ++ ", " ++
      localSource (((runCommands (cs.take t)).getD (initial 2)) 1) ++ ")") ++
  "\n]\nend EconomicalSolutions.Algorithm7.Counterexample\n"

end EconomicalSolutions.Algorithm7.Counterexample
