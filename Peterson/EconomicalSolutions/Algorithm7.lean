import Peterson.EconomicalSolutions.Algorithm3
import Mathlib.Data.Finset.Basic

/-! Reviewed Algorithm 7 reconstruction: two reversed proceedings clocks,
one owner-written whole register, and separate list/prefix/eligibility operations.
See economical-solutions-algorithm7-target.md. No positive clock theorem is used. -/
namespace EconomicalSolutions.Algorithm7

abbrev Proc := Fin

structure Config (n : Nat) where
  order : Proc n → List (Proc n)
  nodup : ∀ p, (order p).Nodup
  complete : ∀ p q, q ∈ order p ↔ q ≠ p

inductive Level where
  | one | two | three
  deriving DecidableEq, Repr
inductive Value where
  | dead | cs | live (level : Level) (b0 b1 : Bool)
  deriving DecidableEq, Repr
inductive Phase where
  | one | maintain | three | eligible
  deriving DecidableEq, Repr

inductive PC (n : Nat) where
  | down | idle
  | join (clock first : Bool) (pc : Algorithm3.PC)
  | joinPublish (b0 b1 : Bool)
  | attempt (phase : Phase) (clock : Bool) (pc : Algorithm3.PC)
  | tickWrite (phase : Phase) (clock : Bool) (pending : Value)
  | pairDone (phase : Phase)
  | build (remaining : List (Proc n))
  | prefixRead (level : Level) | prefixWrite (pending : Value)
  | delete (remaining : List (Proc n)) | add (remaining : List (Proc n))
  | eligible (remaining : List (Proc n))
  | publish | enter | cs | release
  deriving DecidableEq, Repr

structure Local (n : Nat) where
  value : Value
  pc : PC n
  behind : Finset (Proc n)
  count0 : Nat
  count1 : Nat
  deriving DecidableEq

abbrev State (n : Nat) := Proc n → Local n

def reset (down : Bool) : Local n := ⟨.dead, if down then .down else .idle, ∅, 0, 0⟩
def initial (n : Nat) : State n := fun _ => reset false

def setLocal {n : Nat} (s : State n) (p : Proc n) (l : Local n) : State n :=
  fun q => if q = p then l else s q

/-- Reversal is its own inverse: this maps physical owners to positions and back. -/
def position {n : Nat} (p : Proc n) (clock : Bool) : Fin n :=
  if clock then ⟨n - 1 - p.val, by omega⟩ else p

def bit (v : Value) (clock : Bool) : Option Bool :=
  match v with
  | .live _ b0 b1 => some (if clock then b1 else b0)
  | _ => none

def replaceBit (v : Value) (clock b : Bool) : Value :=
  match v with
  | .live level b0 b1 => .live level (if clock then b0 else b) (if clock then b else b1)
  | _ => v

def startJoin {n : Nat} (p : Proc n) (clock : Bool) : Algorithm3.PC :=
  let i := position p clock
  Algorithm3.joinLower i.val n i.val

/-- Each proceedings instruction accesses at most one actual whole register.
Only the owner's clock control executes; other controls are irrelevant to reads. -/
def clockInstruction {n : Nat} (s : State n) (p : Proc n) (clock : Bool)
    (pc : Algorithm3.PC) : Option Algorithm3.Local :=
  let i := position p clock
  Algorithm3.ordinary (fun j => ⟨bit (s (position j clock)).value clock,
    if j = i then pc else .idle⟩) i

def afterAttempt (phase : Phase) (clock : Bool) : PC n :=
  if clock then .pairDone phase else .attempt phase true .attempt

def exposed (v : Value) : Bool :=
  match v with | .live .two _ _ | .live .three _ _ | .cs => true | _ => false

def ordinary {n : Nat} (cfg : Config n) (s : State n) (p : Proc n) : Option (Local n) :=
  let l := s p
  match l.pc with
  | .idle | .down | .cs => none
  | .join clock first (.joinWrite b) =>
      -- Cache the candidate locally; do not perform the basic clock's individual join write.
      some { l with
        pc := (if clock then .joinPublish first b else .join true b (startJoin p true)) }
  | .join clock first pc => (clockInstruction s p clock pc).map fun out =>
      { l with
        pc := .join clock first out.pc }
  | .joinPublish b0 b1 => some { l with
        value := .live .one b0 b1
        pc := .attempt .one false .attempt
        count0 := 0
        count1 := 0 }
  | .attempt phase clock .tickRead => do
      let out ← clockInstruction s p clock .tickRead
      match out.pc with
      | .tickWrite b => some { l with
        pc := .tickWrite phase clock (replaceBit l.value clock b) }
      | _ => none
  | .attempt phase clock pc => (clockInstruction s p clock pc).map fun out =>
      { l with
        pc := if out.pc = .attempt then afterAttempt phase clock else .attempt phase clock out.pc }
  | .tickWrite phase clock pending =>
      let count := phase = .one || phase = .three
      some { l with
        value := pending
        pc := afterAttempt phase clock
        count0 := l.count0 + (if count && !clock then 1 else 0)
        count1 := l.count1 + (if count && clock then 1 else 0) }
  | .pairDone .one => some { l with
        pc := if l.count0 ≥ 3 && l.count1 ≥ 3 then .build (cfg.order p) else .attempt .one false .attempt }
  | .pairDone .three => some { l with
        pc := if l.count0 ≥ 3 && l.count1 ≥ 3 then .attempt .eligible false .attempt else .attempt .three false .attempt }
  | .pairDone .maintain => some { l with
        pc := if l.behind = ∅ then .prefixRead .three else .delete (cfg.order p) }
  | .pairDone .eligible => some { l with
        pc := .eligible (cfg.order p) }
  | .build [] => some { l with
        pc := .prefixRead .two }
  | .build (q :: rest) =>
      let sample := (s q).value
      some { l with
        pc := .build rest
        behind := if exposed sample then insert q l.behind else l.behind }
  | .prefixRead level => match l.value with
      | .live _ b0 b1 => some { l with
        pc := .prefixWrite (.live level b0 b1) }
      | _ => none
  | .prefixWrite pending => match pending with
      | .live .two _ _ => some { l with
        value := pending
        pc := .delete (cfg.order p) }
      | .live .three _ _ => some { l with
        value := pending
        pc := .attempt .three false .attempt
        count0 := 0
        count1 := 0 }
      | _ => none
  | .delete [] => some { l with
        pc := .add (cfg.order p) }
  | .delete (q :: rest) =>
      let sample := (s q).value
      some { l with
        pc := .delete rest
        behind := if exposed sample then l.behind else l.behind.erase q }
  | .add [] => some { l with
        pc := .attempt .maintain false .attempt }
  | .add (q :: rest) =>
      let sample := (s q).value
      some { l with
        pc := .add rest
        behind := match sample with | .live .three _ _ => insert q l.behind | _ => l.behind }
  | .eligible [] => some { l with
        pc := .publish }
  | .eligible (q :: rest) =>
      let sample := (s q).value
      let blocked := match sample with
        | .cs => true | .live .three _ _ => q.val < p.val | _ => false
      some { l with
        pc := if blocked then .attempt .eligible false .attempt else .eligible rest }
  | .publish => some { l with
        value := .cs
        pc := .enter }
  | .enter => some { l with
        pc := .cs }
  | .release => some (reset false)

inductive Command (n : Nat) where
  | run (p : Proc n) | request (p : Proc n) | complete (p : Proc n)
  | fail (p : Proc n) | restart (p : Proc n) | stutter
  deriving DecidableEq, Repr
inductive Label (n : Nat) where
  | instruction (p : Proc n) | request (p : Proc n) | join (p : Proc n)
  | tick (p : Proc n) (clock : Bool) | queuePublish (p : Proc n)
  | entry (p : Proc n) | complete (p : Proc n)
  | fail (p : Proc n) | restart (p : Proc n) | stutter
  deriving DecidableEq, Repr

def next {n : Nat} (cfg : Config n) (s : State n) : Command n → Option (State n)
  | .run p => (ordinary cfg s p).map (setLocal s p)
  | .request p => if (s p).pc = .idle then
      some (setLocal s p { reset false with pc := .join false false (startJoin p false) }) else none
  | .complete p => if (s p).pc = .cs then
      some (setLocal s p { s p with pc := .release }) else none
  | .fail p => if (s p).pc = .down then none else some (setLocal s p (reset true))
  | .restart p => if (s p).pc = .down then some (setLocal s p (reset false)) else none
  | .stutter => some s

def label {n : Nat} (s : State n) : Command n → Label n
  | .run p => match (s p).pc with
      | .joinPublish _ _ => .join p
      | .tickWrite _ clock _ => .tick p clock
      | .prefixWrite (.live .two _ _) => .queuePublish p
      | .enter => .entry p
      | _ => .instruction p
  | .request p => .request p
  | .complete p => .complete p
  | .fail p => .fail p
  | .restart p => .restart p
  | .stutter => .stutter

def lts {n : Nat} (cfg : Config n) : Cslib.LTS (State n) (Label n) :=
  ⟨fun s a t => ∃ c, next cfg s c = some t ∧ label s c = a⟩

structure Run {n : Nat} (cfg : Config n) where
  state : Nat → State n
  command : Nat → Command n
  initialized : state 0 = initial n
  valid : ∀ t, next cfg (state t) (command t) = some (state (t + 1))

def Run.event {n : Nat} {cfg : Config n} (r : Run cfg) (t : Nat) : Label n :=
  label (r.state t) (r.command t)

def Protocol (pc : PC n) : Prop := pc ≠ .idle ∧ pc ≠ .down ∧ pc ≠ .cs
instance (pc : PC n) : Decidable (Protocol pc) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def Acts (c : Command n) (p : Proc n) : Prop := c = .run p ∨ c = .fail p
instance (c : Command n) (p : Proc n) : Decidable (Acts c p) := inferInstanceAs (Decidable (_ ∨ _))

def ProtocolScheduling {n : Nat} {cfg : Config n} (r : Run cfg) : Prop :=
  ∀ t p, Protocol (r.state t p).pc → ∃ u, t ≤ u ∧ Acts (r.command u) p

def CriticalCompletion {n : Nat} {cfg : Config n} (r : Run cfg) : Prop :=
  ∀ t p, (r.state t p).pc = .cs →
    ∃ u, t ≤ u ∧ (r.event u = .complete p ∨ r.event u = .fail p)

/-- Earlier level-two publication must be served or aborted before a later
publisher enters. No replacement request can discharge the original: the first
entry/failure following its publication is its outcome. The later entry must
also belong to the original later publication, with no intervening outcome. -/
def PublicationFIFO {n : Nat} {cfg : Config n} (r : Run cfg) : Prop :=
  ∀ (p q : Proc n) (a b e : Nat), p ≠ q → a < b → b ≤ e →
    r.event a = .queuePublish p → r.event b = .queuePublish q → r.event e = .entry q →
    (∀ u, b ≤ u → u < e → r.event u ≠ .entry q ∧ r.event u ≠ .fail q) →
    ∃ u, a ≤ u ∧ u < e ∧ (r.event u = .entry p ∨ r.event u = .fail p)

/-- Even adding both frozen liveness premises cannot rescue the strict target. -/
def UniversalPublicationFIFO : Prop :=
  ∀ n, 0 < n → ∀ (cfg : Config n) (r : Run cfg),
    ProtocolScheduling r → CriticalCompletion r → PublicationFIFO r

end EconomicalSolutions.Algorithm7
