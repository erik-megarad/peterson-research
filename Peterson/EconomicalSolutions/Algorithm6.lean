module

public import Peterson.EconomicalSolutions.Algorithm2Refinement
public import Peterson.EconomicalSolutions.Algorithm3
public import Mathlib.Data.Finset.Basic

@[expose] public section

/-! Algorithm 6's reviewed product-register implementation. The operational
choices are frozen in economical-solutions-implicit-queue-target.md. Clock
instructions reuse the complete proceedings interpreter, not a ticking oracle.
The product representation makes no state-economy claim. -/
namespace EconomicalSolutions.Algorithm6

abbrev Proc := Algorithm2.Proc
abbrev Command := Algorithm2.Command

structure Config (n : Nat) where
  tournament : Algorithm2.Config n
  order : Proc n → List (Proc n)
  nodup : ∀ p, (order p).Nodup
  complete : ∀ p q, q ∈ order p ↔ q ≠ p

inductive Tag where
  | off | upper (b : Bool) | lower (b : Bool) | cs
  deriving DecidableEq, Repr

/-- One indivisible, single-owner shared register. -/
structure Value where
  tournament : Algorithm2.Value
  clock : Tag
  deriving DecidableEq, Repr

def dead : Value := ⟨Algorithm2.dead, .off⟩

inductive PC (n : Nat) where
  | down | idle | request | acquire
  | upperJoin (clock : Algorithm3.PC)
  | upperTick (count : Nat) (clock : Algorithm3.PC)
  | build (remaining : List (Proc n))
  | off
  | lowerJoin (clock : Algorithm3.PC)
  | complete (candidate : Bool) | enqueue (candidate : Bool)
  | maintain (remaining : List (Proc n))
  | lowerTick (clock : Algorithm3.PC)
  | test | publish | enter | cs | release
  deriving DecidableEq, Repr

structure Local (n : Nat) where
  pc : PC n
  tournamentPC : Algorithm2.PC n
  value : Value
  behind : Finset (Proc n)
  deriving DecidableEq

abbrev State (n : Nat) := Proc n → Local n

def project {n : Nat} (s : State n) : Algorithm2.State n :=
  fun p => ⟨(s p).tournamentPC, (s p).value.tournament⟩

def setLocal {n : Nat} (s : State n) (p : Proc n) (l : Local n) : State n :=
  fun q => if q = p then l else s q

/-- A projected position read is one whole-register sample. Two reads at the
same owner's two positions remain distinct interpreter instructions. -/
def clockValue {n : Nat} (s : State n) (j : Fin (2 * n)) : Option Bool :=
  if h : j.val < n then
    match (s ⟨j.val, h⟩).value.clock with
    | .lower b => some b
    | _ => none
  else
    match (s ⟨j.val - n, by omega⟩).value.clock with
    | .upper b => some b
    | _ => none

def position {n : Nat} (p : Proc n) (upper : Bool) : Fin (2 * n) :=
  ⟨if upper then n + p.val else p.val, by split <;> omega⟩

/-- Only the selected physical owner executes this clock instruction. The
other virtual positions' private controls are never executed independently. -/
def clockInstruction {n : Nat} (s : State n) (p : Proc n) (upper : Bool)
    (pc : Algorithm3.PC) : Option Algorithm3.Local :=
  let i := position p upper
  Algorithm3.ordinary (fun j => ⟨clockValue s j, if j = i then pc else .idle⟩) i

def startJoin {n : Nat} (p : Proc n) (upper : Bool) : Algorithm3.PC :=
  let i := position p upper
  Algorithm3.joinLower i.val (2 * n) i.val

def visible (tag : Tag) : Bool :=
  match tag with
  | .lower _ | .cs => true
  | _ => false

def tournamentInstruction {n : Nat} (cfg : Config n) (s : State n) (p : Proc n) :
    Option (Local n) :=
  (Algorithm2.ordinary cfg.tournament p (project s)).map fun t =>
    { s p with
      pc := if t.pc = .cs then .upperJoin (startJoin p true) else .acquire
      tournamentPC := t.pc
      value := ⟨t.q, (s p).value.clock⟩ }

/-- Clock tags written by the actual clock's cached instruction. The `none`
case is preserved as off; no operation invents a Boolean. -/
def clockTag (upper : Bool) (q : Option Bool) : Tag :=
  match q with
  | none => .off
  | some b => if upper then .upper b else .lower b

def ordinary {n : Nat} (cfg : Config n) (s : State n) (p : Proc n) : Option (Local n) :=
  let l := s p
  match l.pc with
  | .down => none
  | .idle => some { l with pc := .request }
  | .request | .acquire => tournamentInstruction cfg s p
  | .upperJoin pc => (clockInstruction s p true pc).map fun c =>
      { l with pc := if c.pc = .attempt then .upperTick 0 .attempt else .upperJoin c.pc
               value := ⟨l.value.tournament, clockTag true c.q⟩ }
  | .upperTick count pc => (clockInstruction s p true pc).map fun c =>
      let success := match pc with | .tickWrite _ => true | _ => false
      { l with pc := if success && count + 1 = 3 then .build (cfg.order p)
          else .upperTick (if success then count + 1 else count) c.pc
               value := ⟨l.value.tournament, clockTag true c.q⟩
               behind := if success && count + 1 = 3 then ∅ else l.behind }
  | .build [] => some { l with pc := .off }
  | .build (q :: rest) =>
      let sample := (s q).value
      some { l with
        pc := .build rest
        behind := if visible sample.clock then insert q l.behind else l.behind }
  | .off => some { l with
      pc := .lowerJoin (startJoin p false)
      value := ⟨l.value.tournament, .off⟩ }
  | .lowerJoin (.joinWrite b) => some { l with pc := .complete b }
  | .lowerJoin pc => (clockInstruction s p false pc).map fun c =>
      { l with pc := .lowerJoin c.pc }
  | .complete b => some { l with pc := .enqueue b, tournamentPC := .release }
  | .enqueue b => some { l with
      pc := .maintain (cfg.order p)
      tournamentPC := .idle
      value := ⟨Algorithm2.dead, .lower b⟩ }
  | .maintain [] => some { l with pc := .lowerTick .attempt }
  | .maintain (q :: rest) =>
      let sample := (s q).value
      some { l with
        pc := .maintain rest
        behind := if visible sample.clock then l.behind else l.behind.erase q }
  | .lowerTick pc => (clockInstruction s p false pc).map fun c =>
      { l with
        pc := if c.pc = .attempt then .test else .lowerTick c.pc
        value := ⟨l.value.tournament, clockTag false c.q⟩ }
  | .test => some { l with pc := if l.behind = ∅ then .publish else .maintain (cfg.order p) }
  | .publish => some { l with pc := .enter, value := ⟨Algorithm2.dead, .cs⟩ }
  | .enter => some { l with pc := .cs }
  | .cs => some { l with pc := .release }
  | .release => some ⟨.idle, .idle, dead, ∅⟩

def reset (down : Bool) : Local n :=
  ⟨if down then .down else .idle, if down then .down else .idle, dead, ∅⟩

def next {n : Nat} (cfg : Config n) (s : State n) : Command n → Option (State n)
  | .run p => (ordinary cfg s p).map (setLocal s p)
  | .fail p => if (s p).pc = .down then none else some (setLocal s p (reset true))
  | .restart p => if (s p).pc = .down then some (setLocal s p (reset false)) else none
  | .stutter => some s

inductive Label (n : Nat) where
  | request (p : Proc n) | instruction (p : Proc n) | enqueue (p : Proc n)
  | upperJoin (p : Proc n) | upperTick (p : Proc n) | lowerTick (p : Proc n)
  | entry (p : Proc n) | complete (p : Proc n)
  | fail (p : Proc n) | restart (p : Proc n) | stutter
  deriving DecidableEq, Repr

def label {n : Nat} (s : State n) : Command n → Label n
  | .run p => match (s p).pc with
      | .idle => .request p
      | .enqueue _ => .enqueue p
      | .upperJoin (.joinWrite _) => .upperJoin p
      | .upperTick _ (.tickWrite _) => .upperTick p
      | .lowerTick (.tickWrite _) => .lowerTick p
      | .enter => .entry p
      | .cs => .complete p
      | _ => .instruction p
  | .fail p => .fail p
  | .restart p => .restart p
  | .stutter => .stutter

def lts {n : Nat} (cfg : Config n) : Cslib.LTS (State n) (Label n) :=
  ⟨fun s a t => ∃ c, next cfg s c = some t ∧ label s c = a⟩

def initial (n : Nat) : State n := fun _ => reset false

inductive Reachable {n : Nat} (cfg : Config n) : State n → Prop where
  | initial : Reachable cfg (initial n)
  | step {s t : State n} {a : Label n} : Reachable cfg s → (lts cfg).Tr s a t → Reachable cfg t

def MutualExclusion {n : Nat} (s : State n) : Prop :=
  ∀ p q, (s p).pc = .cs → (s q).pc = .cs → p = q

def SafetyTarget : Prop :=
  ∀ n (cfg : Config n) s, Reachable cfg s → MutualExclusion s

end EconomicalSolutions.Algorithm6
