import Cslib.Foundations.Semantics.LTS.Basic

namespace ConcurrentReading

/-- Payloads are arbitrary; origins are separate ghost write indices. -/
structure Datum (α : Type) where
  value : α
  origin : Option Nat
  deriving DecidableEq, Repr

inductive Buffer (n : Nat) where
  | first | second | copy (i : Fin n)
  deriving DecidableEq, Repr

structure Sample (α : Type) (n : Nat) where
  buffer : Buffer n
  begun : Nat
  ended : Nat
  torn : Bool
  datum : Datum α
  deriving DecidableEq, Repr

structure RawRead (n : Nat) where
  buffer : Buffer n
  begun : Nat
  torn : Bool
  deriving DecidableEq, Repr

structure RawWrite (α : Type) (n : Nat) where
  buffer : Buffer n
  datum : Datum α
  deriving DecidableEq, Repr

/-- PCs are documented in the encoding note; 0 is idle. -/
structure Reader (α : Type) (n : Nat) where
  pc : Nat := 0
  call : Nat := 0
  bit : Bool := false
  flag1 : Bool := false
  switch1 : Bool := false
  flag2 : Bool := false
  switch2 : Bool := false
  test : Bool := false
  first : Option (Sample α n) := none
  second : Option (Sample α n) := none
  chosen : Option (Sample α n) := none

structure Writer (α : Type) where
  pc : Nat := 0
  index : Nat := 0
  value : α
  j : Nat := 0
  bit : Bool := false

inductive Event (α : Type) (n : Nat) where
  | writeInvoke (index : Nat) (value : α)
  | writeReturn (index : Nat)
  | readInvoke (i : Fin n) (call : Nat)
  | readReturn (i : Fin n) (call : Nat) (sample : Sample α n)
  deriving DecidableEq, Repr

structure State (α : Type) (n : Nat) where
  reading : Fin n → Bool
  writing : Fin n → Bool
  wflag : Bool
  switch : Bool
  memory : Buffer n → Datum α
  readers : Fin n → Reader α n
  writer : Writer α
  rawReads : Fin n → Option (RawRead n)
  rawWrite : Option (RawWrite α n)
  clock : Nat
  history : List (Nat × Event α n)

/-- Initial W0 has completed; private buffers have arbitrary uninitialized data. -/
def initial (v : α) (privateData : Fin n → α) : State α n where
  reading := fun _ => false
  writing := fun _ => false
  wflag := false
  switch := true
  memory := fun b => match b with
    | .first | .second => ⟨v, some 0⟩
    | .copy i => ⟨privateData i, none⟩
  readers := fun _ => {}
  writer := { value := v }
  rawReads := fun _ => none
  rawWrite := none
  clock := 2
  history := [(0, .writeInvoke 0 v), (1, .writeReturn 0)]

def putReader (s : State α n) (i : Fin n) (r : Reader α n) : State α n :=
  { s with readers := Function.update s.readers i r }

def emit (s : State α n) (e : Event α n) : State α n :=
  { s with history := s.history ++ [(s.clock, e)] }

/-- A write beginning marks *all* overlapping active reads, permanently. -/
def beginWrite (s : State α n) (b : Buffer n) : State α n :=
  { s with rawWrite := some ⟨b, ⟨s.writer.value, some s.writer.index⟩⟩
           rawReads := fun i => (s.rawReads i).map fun r =>
             { r with torn := r.torn || decide (r.buffer = b) } }

def endWrite (s : State α n) : Option (State α n) := do
  let w ← s.rawWrite
  pure { s with memory := Function.update s.memory w.buffer w.datum, rawWrite := none }

def beginRead (s : State α n) (i : Fin n) (b : Buffer n) : State α n :=
  { s with rawReads := Function.update s.rawReads i (some
      ⟨b, s.clock, s.rawWrite.any (fun w => decide (w.buffer = b))⟩) }

/-- The supplied corrupt payload is unconstrained. It cannot invent provenance. -/
def endRead (s : State α n) (i : Fin n) (corrupt : α) : Option (Sample α n × State α n) := do
  let r ← s.rawReads i
  let d := if r.torn then ⟨corrupt, none⟩ else s.memory r.buffer
  pure (⟨r.buffer, r.begun, s.clock, r.torn, d⟩,
    { s with rawReads := Function.update s.rawReads i none })

/-- One writer primitive; every shared RHS read precedes its separate write. -/
def writerStep (s : State α n) : Option (State α n) := do
  let w := s.writer
  match w.pc with
  | 1 => pure { s with wflag := true, writer := { w with pc := 2 } }
  | 2 => pure { beginWrite s .first with writer := { w with pc := 3 } }
  | 3 => let t ← endWrite s; pure { t with writer := { w with pc := 4 } }
  | 4 => pure { s with writer := { w with pc := 5, bit := s.switch } }
  | 5 => pure { s with switch := !w.bit, writer := { w with pc := 6 } }
  | 6 => pure { s with wflag := false, writer := { w with pc := 7, j := 0 } }
  | 7 =>
    if h : w.j < n then
      pure { s with writer := { w with pc := 8, bit := s.reading ⟨w.j, h⟩ } }
    else pure { s with writer := { w with pc := 13 } }
  | 8 =>
    if h : w.j < n then
      pure { s with writer := { w with
        pc := if w.bit != s.writing ⟨w.j, h⟩ then 9 else 7,
        j := if w.bit != s.writing ⟨w.j, h⟩ then w.j else w.j + 1 } }
    else none
  | 9 =>
    if h : w.j < n then
      pure { beginWrite s (.copy ⟨w.j, h⟩) with writer := { w with pc := 10 } }
    else none
  | 10 => let t ← endWrite s; pure { t with writer := { w with pc := 11 } }
  | 11 =>
    if h : w.j < n then
      pure { s with writer := { w with pc := 12, bit := s.reading ⟨w.j, h⟩ } }
    else none
  | 12 =>
    if h : w.j < n then
      pure { s with writing := Function.update s.writing ⟨w.j, h⟩ w.bit,
                    writer := { w with pc := 7, j := w.j + 1 } }
    else none
  | 13 => pure { beginWrite s .second with writer := { w with pc := 14 } }
  | 14 => let t ← endWrite s; pure { t with writer := { w with pc := 15 } }
  | 15 => pure (emit { s with writer := { w with pc := 0 } } (.writeReturn w.index))
  | _ => none

/-- One reader primitive; the final test reads reading and writing separately. -/
def readerStep (s : State α n) (i : Fin n) (corrupt : α) : Option (State α n) := do
  let r := s.readers i
  match r.pc with
  | 1 => pure (putReader s i { r with pc := 2, bit := s.writing i })
  | 2 => pure (putReader { s with reading := Function.update s.reading i (!r.bit) }
      i { r with pc := 3 })
  | 3 => pure (putReader s i { r with pc := 4, flag1 := s.wflag })
  | 4 => pure (putReader s i { r with pc := 5, switch1 := s.switch })
  | 5 => pure (putReader (beginRead s i .first) i { r with pc := 6 })
  | 6 => let (v, t) ← endRead s i corrupt
         pure (putReader t i { r with pc := 7, first := some v })
  | 7 => pure (putReader s i { r with pc := 8, flag2 := s.wflag })
  | 8 => pure (putReader s i { r with pc := 9, switch2 := s.switch })
  | 9 => pure (putReader (beginRead s i .second) i { r with pc := 10 })
  | 10 => let (v, t) ← endRead s i corrupt
          pure (putReader t i { r with pc := 11, second := some v })
  | 11 => pure (putReader s i { r with pc := 12, test := s.reading i })
  | 12 => pure (putReader s i { r with pc := if r.test == s.writing i then 13 else 15 })
  | 13 => pure (putReader (beginRead s i (.copy i)) i { r with pc := 14 })
  | 14 => let (v, t) ← endRead s i corrupt
          pure (putReader t i { r with pc := 16, chosen := some v })
  | 15 => pure (putReader s i { r with pc := 16, chosen := if (r.switch1 != r.switch2) || r.flag1 || r.flag2 then r.second else r.first })
  | 16 => let v ← r.chosen
          pure (emit (putReader s i { r with pc := 0 }) (.readReturn i r.call v))
  | _ => none

inductive Action (α : Type) (n : Nat) where
  | invokeWrite (value : α) | writer
  | invokeRead (i : Fin n) | reader (i : Fin n) (corrupt : α)
  deriving DecidableEq, Repr

/-- A scheduler chooses one process action; failed/idle actions are not transitions. -/
def step (s : State α n) (a : Action α n) : Option (State α n) := do
  let t ← match a with
    | .invokeWrite v =>
      if s.writer.pc = 0 then
        let k := s.writer.index + 1
        some (emit { s with writer := { pc := 1, index := k, value := v } } (.writeInvoke k v))
      else none
    | .writer => writerStep s
    | .invokeRead i =>
      if (s.readers i).pc = 0 then
        some (emit (putReader s i { pc := 1, call := s.clock }) (.readInvoke i s.clock))
      else none
    | .reader i corrupt => readerStep s i corrupt
  pure { t with clock := s.clock + 1 }

def system (α : Type) (n : Nat) : Cslib.LTS (State α n) (Action α n) :=
  ⟨fun s a t => step s a = some t⟩

def run (s : State α n) : List (Action α n) → Option (State α n)
  | [] => some s
  | a :: as => (step s a).bind (fun t => run t as)

def Reachable (v : α) (privateData : Fin n → α) (s : State α n) : Prop :=
  ∃ as, run (initial v privateData) as = some s

theorem initial_switch (v : α) (privateData : Fin n → α) :
    (initial v privateData).switch = true := rfl

theorem initial_reachable (v : α) (privateData : Fin n → α) : Reachable v privateData (initial v privateData) :=
  ⟨[], rfl⟩

theorem run_sound {s t : State α n} {as : List (Action α n)}
    (h : run s as = some t) : (system α n).MTr s as t := by
  induction as generalizing s with
  | nil => simp only [run, Option.some.injEq] at h; subst t; exact .refl
  | cons a as ih =>
    simp only [run] at h
    cases hs : step s a with
    | none => simp [hs] at h
    | some u =>
      simp only [hs, Option.bind_some] at h
      exact .stepL hs (ih h)

/-- Marking overlap at write begin catches even a write that ends before the read. -/
theorem begin_write_marks {s : State α n} {i : Fin n} {r : RawRead n}
    (h : s.rawReads i = some r) :
    (beginWrite s r.buffer).rawReads i = some { r with torn := true } := by
  simp [beginWrite, h]

end ConcurrentReading
