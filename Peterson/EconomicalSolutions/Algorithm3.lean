module

public import Cslib.Foundations.Semantics.LTS.Basic

@[expose] public section

/-! Algorithm 3, complete proceedings listing (printed pp. 93–94).
The collection’s economical-solutions guide explains the selected proceedings version.
This is the basic clock, with complementary upper joining and ALL-upper ticking.
`none` is dead; `some false` / `some true` are F / T. There is no normal leave.
A cursor is the next position to sample. Scan helpers take the number of
positions below that cursor, avoiding natural-subtraction wraparound.
Only private data used by a future instruction are retained in PC payloads. -/
namespace EconomicalSolutions.Algorithm3

inductive PC where
  | down | idle
  | joinLower (j : Nat) | joinUpper (j : Nat) | joinWrite (b : Bool)
  | attempt | tickLower (j : Nat) (observed : Bool)
  | lowerOwn (j : Nat) (sample : Bool)
  | tickUpper (j : Nat) | upperOwn (j : Nat) (sample : Bool)
  | tickRead | tickWrite (b : Bool)
  deriving DecidableEq, Repr

structure Local where
  q : Option Bool
  pc : PC
  deriving DecidableEq, Repr

abbrev State (n : Nat) := Fin n → Local

def initial (n : Nat) : State n := fun _ => ⟨none, .idle⟩

def setLocal {n : Nat} (s : State n) (i : Fin n) (l : Local) : State n :=
  fun p => if p = i then l else s p

/-- `k` lower positions remain, with the next read at k-1. -/
def joinLower (i n k : Nat) : PC :=
  if k > 0 then .joinLower (k - 1)
  else if i + 1 < n then .joinUpper (n - 1) else .joinWrite false

def tickLower (i n k : Nat) (observed : Bool) : PC :=
  if k > 0 then .tickLower (k - 1) observed
  else if observed || !(i + 1 < n) then .tickRead else .tickUpper (n - 1)

def tickUpper (i k : Nat) : PC :=
  if i + 1 < k then .tickUpper (k - 1) else .tickRead

/-- One ordinary instruction. Each peer access, own access and write is separate.
A failed guard returns to attempt. The observed-lower flag belongs to this scan,
not to the current visible population. A pending write uses only its cache. -/
def ordinary {n : Nat} (s : State n) (i : Fin n) : Option Local :=
  let l := s i
  match l.pc with
  | .idle | .down => none
  | .joinLower j => if h : j < n then
      some ⟨l.q, match (s ⟨j, h⟩).q with
        | none => joinLower i.val n j
        | some b => .joinWrite b⟩ else none
  | .joinUpper j => if h : j < n then
      some ⟨l.q, match (s ⟨j, h⟩).q with
        | none => if i.val + 1 < j then .joinUpper (j - 1) else .joinWrite false
        | some b => .joinWrite (!b)⟩ else none
  | .joinWrite b => if l.q = none then some ⟨some b, .attempt⟩ else none
  | pc => do
      let v ← l.q
      let pc' ← match pc with
        | .attempt => some (tickLower i.val n i.val false)
        | .tickLower j observed => if h : j < n then
            some (match (s ⟨j, h⟩).q with
              | none => tickLower i.val n j observed
              | some b => .lowerOwn j b) else none
        | .lowerOwn j sample => some (if sample = v then .attempt
            else tickLower i.val n j true)
        | .tickUpper j => if h : j < n then
            some (match (s ⟨j, h⟩).q with
              | none => tickUpper i.val j
              | some b => .upperOwn j b) else none
        | .upperOwn j sample => some (if sample ≠ v then .attempt else tickUpper i.val j)
        | .tickRead => some (.tickWrite (!v))
        | .tickWrite _ => some .attempt
        | _ => none
      match pc with
      | .tickWrite b => if b ≠ v then some ⟨some b, pc'⟩ else none
      | _ => some ⟨some v, pc'⟩

inductive Command (n : Nat) where
  | run (i : Fin n) | start (i : Fin n) | fail (i : Fin n)
  | restart (i : Fin n) | stutter
  deriving DecidableEq, Repr

inductive Label (n : Nat) where
  | instruction (i : Fin n) | join (i : Fin n) | tick (i : Fin n)
  | start (i : Fin n) | fail (i : Fin n) | restart (i : Fin n) | stutter
  deriving DecidableEq, Repr

/-- Failure erases ALL private work, even between a read and its cached write.
Restart is optional, fresh and inactive; global stutter pays no scheduling debt. -/
def next {n : Nat} (s : State n) : Command n → Option (State n)
  | .run i => (ordinary s i).map (setLocal s i)
  | .start i => if (s i).pc = .idle ∧ (s i).q = none then
      some (setLocal s i ⟨none, joinLower i.val n i.val⟩) else none
  | .fail i => if (s i).pc = .down then none else some (setLocal s i ⟨none, .down⟩)
  | .restart i => if (s i).pc = .down then some (setLocal s i ⟨none, .idle⟩) else none
  | .stutter => some s

/-- Only the successful cached complement write is labelled tick. -/
def label {n : Nat} (s : State n) : Command n → Label n
  | .run i => match (s i).pc with
      | .joinWrite _ => .join i
      | .tickWrite _ => .tick i
      | _ => .instruction i
  | .start i => .start i
  | .fail i => .fail i
  | .restart i => .restart i
  | .stutter => .stutter

def lts (n : Nat) : Cslib.LTS (State n) (Label n) :=
  ⟨fun s a t => ∃ c, next s c = some t ∧ label s c = a⟩

def Active (l : Local) : Prop := l.pc ≠ .idle ∧ l.pc ≠ .down
instance (l : Local) : Decidable (Active l) := inferInstanceAs (Decidable (_ ∧ _))

/-- Joining instructions count, but the optional start itself does not. -/
def Ordinary (a : Label n) (i : Fin n) : Prop :=
  a = .instruction i ∨ a = .join i ∨ a = .tick i
instance (a : Label n) (i : Fin n) : Decidable (Ordinary a i) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def Execution (s : Nat → State n) (a : Nat → Label n) : Prop :=
  s 0 = initial n ∧ ∀ t, (lts n).Tr (s t) (a t) (s (t + 1))

/-- Every active occurrence is owed an instruction or its own abort at or after it.
No successful-guard, transient-observation, or eventual-peer-stability fairness. -/
def InstructionScheduled (s : Nat → State n) (a : Nat → Label n) : Prop :=
  ∀ i t, Active (s t i) → ∃ u, t ≤ u ∧ (Ordinary (a u) i ∨ a u = .fail i)

/-- No failure has yet ended the episode present at t before transition u. -/
def SameEpisodeUntil (a : Nat → Label n) (i : Fin n) (t u : Nat) : Prop :=
  ∀ v, t ≤ v → v < u → a v ≠ .fail i

/-- The frozen positive comparison target, retained unchanged in meaning.
The first own tick or failure belongs to the episode active at t. -/
def NextOutcome (s : Nat → State n) (a : Nat → Label n) : Prop :=
  ∀ i t, Active (s t i) → ∃ u, t ≤ u ∧ SameEpisodeUntil a i t u ∧
    (a u = .tick i ∨ a u = .fail i)

def UniversalNextOutcome (n : Nat) : Prop :=
  ∀ (s : Nat → State n) (a : Nat → Label n), Execution s a → InstructionScheduled s a → NextOutcome s a

def SurvivesFrom (s : Nat → State n) (a : Nat → Label n) (i : Fin n) (t : Nat) : Prop :=
  ∀ u, t ≤ u → Active (s u i) ∧ a u ≠ .fail i

def RepeatedTicks (s : Nat → State n) (a : Nat → Label n) : Prop :=
  ∀ i t, SurvivesFrom s a i t → ∀ v, t ≤ v → ∃ u, v ≤ u ∧ a u = .tick i

def UniversalRepeatedTicks (n : Nat) : Prop :=
  ∀ (s : Nat → State n) (a : Nat → Label n), Execution s a → InstructionScheduled s a → RepeatedTicks s a

end EconomicalSolutions.Algorithm3
