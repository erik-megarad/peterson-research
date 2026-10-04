import ConcurrentReading.Model

namespace ConcurrentReading

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

def start : State Nat 1 := initial 10 (fun _ => 99)
def ri : Fin 1 := ⟨0, by decide⟩
def rsteps (k : Nat) : List (Action Nat 1) := List.replicate k (.reader ri 777)
def wsteps (k : Nat) : List (Action Nat 1) := List.replicate k .writer

def quiescent := [Action.invokeRead ri] ++ rsteps 14

def returned (s : State Nat 1) : Option (Sample Nat 1) :=
  (s.history.reverse.findSome? fun (_, e) => match e with
    | .readReturn _ _ v => some v
    | _ => none)

def result (as : List (Action Nat 1)) : Option (Buffer 1 × Bool × Datum Nat) := do
  let s ← run start as
  let v ← returned s
  pure (v.buffer, v.torn, v.datum)

theorem quiescent_trace : result quiescent = some (.first, false, ⟨10, some 0⟩) := by
  decide

/-- Signal first, let the writer copy and acknowledge, then finish the read. -/
def copyTrace := [Action.invokeRead ri] ++ rsteps 2 ++ [.invokeWrite 20] ++
  wsteps 16 ++ rsteps 13

theorem copy_trace : result copyTrace = some (.copy ri, false, ⟨20, some 1⟩) := by
  decide

/-- Writer passes its copy test before the request; reader sees wflag on the next
pass and chooses the previous completed buff2 while the writer pauses. -/
def secondTrace := [Action.invokeWrite 20] ++ wsteps 8 ++
  [.invokeRead ri] ++ rsteps 2 ++ wsteps 4 ++ [.invokeWrite 30] ++ wsteps 1 ++ rsteps 12

theorem second_trace : result secondTrace = some (.second, false, ⟨20, some 1⟩) := by
  decide

/-- An entire buff1 write occurs inside the first read; overlap persists after end. -/
def interiorTrace := [Action.invokeRead ri] ++ rsteps 5 ++ [.invokeWrite 20] ++
  wsteps 3 ++ rsteps 1

theorem interior_write_corrupts :
    ((run start interiorTrace).bind fun s => (s.readers ri).first).map
      (fun v => (v.torn, v.datum)) = some (true, ⟨777, none⟩) := by decide

/-- Identical write values retain distinct source identities. -/
def equalPayloadTrace := [Action.invokeWrite 10] ++ wsteps 12 ++ quiescent

theorem equal_payload_distinct_origin :
    result equalPayloadTrace = some (.first, false, ⟨10, some 1⟩) := by decide

/-- A completed read can already use a still-pending writer's private copy. -/
def pendingCopyTrace := [Action.invokeRead ri] ++ rsteps 2 ++ [.invokeWrite 20] ++
  wsteps 12 ++ rsteps 13

theorem pending_copy_trace :
    result pendingCopyTrace = some (.copy ri, false, ⟨20, some 1⟩) ∧
    ((run start pendingCopyTrace).map fun s =>
      s.history.any (fun (_, e) => e == .writeReturn 1)) = some false := by decide

/-- A read beginning during a write is also marked, without needing a new begin. -/
def activeWriteTrace := [Action.invokeWrite 20] ++ wsteps 2 ++
  [.invokeRead ri] ++ rsteps 6

theorem active_write_corrupts :
    ((run start activeWriteTrace).bind fun s => (s.readers ri).first).map
      (fun v => (v.torn, v.datum)) = some (true, ⟨777, none⟩) := by decide

end ConcurrentReading
