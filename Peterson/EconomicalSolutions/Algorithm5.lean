module

public import Peterson.EconomicalSolutions.Algorithm2Refinement

@[expose] public section

/-! The reviewed explicit queue. Priorities are unrestricted integers in the
interpreter; their range and uniqueness are proof obligations, not guards. -/
namespace EconomicalSolutions.Algorithm5

abbrev Proc := Algorithm2.Proc
abbrev Command := Algorithm2.Command

structure Config (n : Nat) where
  tournament : Algorithm2.Config n
  order : Proc n → List (Proc n)
  nodup : ∀ p, (order p).Nodup
  complete : ∀ p q, q ∈ order p ↔ q ≠ p

inductive PC (n : Nat) where
  | down | idle | request | acquire
  | capacity (remaining : List (Proc n)) (maximum : Int)
  | choose (remaining : List (Proc n)) (maximum : Int)
  | enqueue (candidate : Int)
  | complete | depart | test
  | absent (remaining : List (Proc n)) (priority : Int)
  | prepare (priority : Int)
  | decrement (candidate : Int)
  | enter | cs | release
  deriving DecidableEq, Repr

/-- A process owns one indivisible shared value, including both components. -/
structure Value where
  tournament : Algorithm2.Value
  priority : Int
  deriving DecidableEq, Repr

def dead : Value := ⟨Algorithm2.dead, -1⟩

structure Local (n : Nat) where
  pc : PC n
  tournamentPC : Algorithm2.PC n
  value : Value
  deriving DecidableEq, Repr

abbrev State (n : Nat) := Proc n → Local n

def project {n : Nat} (s : State n) : Algorithm2.State n :=
  fun p => ⟨(s p).tournamentPC, (s p).value.tournament⟩

def setLocal {n : Nat} (s : State n) (p : Proc n) (l : Local n) : State n :=
  fun q => if q = p then l else s q

/-- Reusing the exact tournament instruction projects every compound sample
onto its tournament component. Its owner writes replace the compound value,
preserving the private, owner-only priority component. -/
def tournamentInstruction {n : Nat} (cfg : Config n) (s : State n) (p : Proc n) :
    Option (Local n) :=
  (Algorithm2.ordinary cfg.tournament p (project s)).map fun t =>
    { pc := if t.pc = .cs then .capacity (cfg.order p) (-1) else .acquire
      tournamentPC := t.pc
      value := ⟨t.q, (s p).value.priority⟩ }

/-- Each nonempty scan reads exactly one whole register. Cached comparisons,
maxima and candidate writes are private; the following write remains separate.
Failure in `next` discards every one of these caches. -/
def ordinary {n : Nat} (cfg : Config n) (s : State n) (p : Proc n) : Option (Local n) :=
  let l := s p
  match l.pc with
  | .down => none
  | .idle => some { l with pc := .request }
  | .request | .acquire => tournamentInstruction cfg s p
  | .capacity [] m => some { l with pc :=
      if m < (n : Int) - 1 then .choose (cfg.order p) (-1) else .capacity (cfg.order p) (-1) }
  | .capacity (q :: rest) m =>
      let sample := (s q).value
      some { l with pc := .capacity rest (max m sample.priority) }
  | .choose [] m => some { l with pc := .enqueue (m + 1) }
  | .choose (q :: rest) m =>
      let sample := (s q).value
      some { l with pc := .choose rest (max m sample.priority) }
  | .enqueue v => some { l with pc := .complete, value := ⟨l.value.tournament, v⟩ }
  | .complete => some { l with pc := .depart, tournamentPC := .release }
  | .depart => some { l with pc := .test, tournamentPC := .idle, value := ⟨Algorithm2.dead, l.value.priority⟩ }
  | .test =>
      let sample := l.value
      some { l with pc := if sample.priority = 0 then .enter else .absent (cfg.order p) sample.priority }
  | .absent [] k => some { l with pc := .prepare k }
  | .absent (q :: rest) k =>
      let sample := (s q).value
      some { l with pc := if sample.priority = k - 1 then .absent (cfg.order p) k else .absent rest k }
  | .prepare k =>
      let sample := l.value
      some { l with pc := .decrement (k - 1), value := sample }
  | .decrement v => some { l with pc := .test, value := ⟨Algorithm2.dead, v⟩ }
  | .enter => some { l with pc := .cs }
  | .cs => some { l with pc := .release }
  | .release => some ⟨.idle, .idle, dead⟩

def next {n : Nat} (cfg : Config n) (s : State n) : Command n → Option (State n)
  | .run p => (ordinary cfg s p).map (setLocal s p)
  | .fail p => if (s p).pc = .down then none else some (setLocal s p ⟨.down, .down, dead⟩)
  | .restart p => if (s p).pc = .down then some (setLocal s p ⟨.idle, .idle, dead⟩) else none
  | .stutter => some s

inductive Label (n : Nat) where
  | request (p : Proc n) | instruction (p : Proc n) | enqueue (p : Proc n)
  | entry (p : Proc n) | complete (p : Proc n)
  | fail (p : Proc n) | restart (p : Proc n) | stutter
  deriving DecidableEq, Repr

def label {n : Nat} (s : State n) : Command n → Label n
  | .run p => match (s p).pc with
      | .idle => .request p
      | .enqueue _ => .enqueue p
      | .enter => .entry p
      | .cs => .complete p
      | _ => .instruction p
  | .fail p => .fail p
  | .restart p => .restart p
  | .stutter => .stutter

def lts {n : Nat} (cfg : Config n) : Cslib.LTS (State n) (Label n) :=
  ⟨fun s a t => ∃ c, next cfg s c = some t ∧ label s c = a⟩

def initial (n : Nat) : State n := fun _ => ⟨.idle, .idle, dead⟩

inductive Reachable {n : Nat} (cfg : Config n) : State n → Prop where
  | initial : Reachable cfg (initial n)
  | step {s t : State n} {a : Label n} : Reachable cfg s → (lts cfg).Tr s a t → Reachable cfg t

def MutualExclusion {n : Nat} (s : State n) : Prop :=
  ∀ p q, (s p).pc = .cs → (s q).pc = .cs → p = q

def SafetyTarget : Prop :=
  ∀ n (cfg : Config n) s, Reachable cfg s → MutualExclusion s

end EconomicalSolutions.Algorithm5
