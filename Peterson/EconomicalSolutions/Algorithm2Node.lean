import Peterson.EconomicalSolutions.Algorithm2

/-! A local competition abstraction, not a second semantics for Algorithm 2.
A sample action names its historical observation point. Proving that concrete
scans and changing representatives admit such a trace remains separate. -/
namespace EconomicalSolutions.Algorithm2.Node

/-- Above forgets all higher-level Boolean rewrites: both roles must wait. -/
inductive Value where
  | O | T | F | H
  deriving DecidableEq, Repr

inductive PC where
  | read1 | write1 (v : Value) | read2 | self2 | write2 (v : Value)
  | waitPeer | waitSelf (v : Value) | held
  deriving DecidableEq, Repr

structure Local where
  pc : PC
  q : Value
  deriving DecidableEq, Repr

structure State where
  p0 : Local
  p1 : Local
  deriving DecidableEq, Repr

def matching (p : Bool) (v : Value) : Value :=
  if p then (if v = .T then .F else .T) else v

/-- Used only at a selected observation point inside a scan. The concrete
return can occur later, while this cached private continuation waits. -/
def sampled (p : Bool) (c : Continuation) (v : Value) : PC :=
  match c with
  | .first => .write1 (if v = .T ∨ v = .F then matching p v else .T)
  | .second => if v = .T ∨ v = .F then .write2 (matching p v) else .self2
  | .wait => if v = .H then .waitPeer else if v = .O then .held else .waitSelf v

def ordinary (p : Bool) (l : Local) (peer : Value) : Local :=
  match l.pc with
  | .read1 => { l with pc := sampled p .first peer }
  | .write1 v => ⟨.read2, v⟩
  | .read2 => { l with pc := sampled p .second peer }
  | .self2 => { l with pc := .write2 l.q }
  | .write2 v => ⟨.waitPeer, v⟩
  | .waitPeer => { l with pc := sampled p .wait peer }
  | .waitSelf x => { l with pc := if ((x == l.q) == p) then .held else .waitPeer }
  | .held => ⟨.held, .H⟩

/-- Reset discards the complete local cache. It also permits immediate new
representation; idle/down/lower-tree delay is represented by global stutter. -/
inductive Command where
  | run (p : Bool) | reset (p : Bool) | stutter
  deriving DecidableEq, Repr

def State.local (s : State) (p : Bool) : Local := if p then s.p1 else s.p0

def State.setLocal (s : State) (p : Bool) (l : Local) : State :=
  if p then { s with p1 := l } else { s with p0 := l }

def next (s : State) : Command → State
  | .run p => s.setLocal p (ordinary p (s.local p) (s.local (!p)).q)
  | .reset p => s.setLocal p ⟨.read1, .O⟩
  | .stutter => s

def initial : State := ⟨⟨.read1, .O⟩, ⟨.read1, .O⟩⟩

inductive Reachable : State → Prop where
  | initial : Reachable initial
  | step {s : State} (c : Command) : Reachable s → Reachable (next s c)

def Exclusion (s : State) : Prop := ¬ (s.p0.pc = .held ∧ s.p1.pc = .held)

/-- Lower values are absent at this node; higher values block regardless of
Boolean. This is an observation projection, not a global state refinement. -/
def projectValue (k : Nat) (x : ScanBridge.Value) : Value :=
  if x.level < k then .O else if k < x.level then .H else if x.flag then .T else .F

def projectPC {n : Nat} (k : Nat) : Algorithm2.PC n → PC
  | .write1 _ x => .write1 (projectValue k x)
  | .self2 _ => .self2
  | .write2 _ x => .write2 (projectValue k x)
  | .waitSelf _ x => .waitSelf (projectValue k x)
  | .pass _ => .held
  | .scan .wait _ _ => .waitPeer
  | _ => .read1

/-- The concrete returned-sample continuation agrees exactly with the local
node rule, including both higher-level fallback assignments. -/
theorem resume_projection {n : Nat} (cfg : Config n) (p : Proc n)
    (c : Continuation) (k : Nat) (x : ScanBridge.Value) :
    projectPC k (resume cfg p c k x) = sampled (bit p.val k) c (projectValue k x) := by
  rcases x with ⟨level, flag⟩
  rcases Nat.lt_trichotomy level k with low | same | high
  · have ne : level ≠ k := by omega
    have nh : ¬ k < level := by omega
    cases c <;> simp [resume, projectPC, projectValue, sampled, low, ne, nh]
  · subst level
    cases c <;> cases flag <;> cases h : bit p.val k <;>
      simp [resume, projectPC, projectValue, sampled, matching, Algorithm2.matching, h]
  · have ne : level ≠ k := by omega
    have nl : ¬ level < k := by omega
    cases c <;> simp [resume, projectPC, projectValue, sampled, high, ne, nl, scan]

/-- Equal-level whole-pair comparison preserves precisely the two Booleans.
Reachable wait-self level/cache well-formedness is a separate obligation. -/
theorem waitSelf_projection (p : Bool) (k : Nat) (x y : ScanBridge.Value)
    (hx : x.level = k) (hy : y.level = k) :
    (Bool.xor p (x == y) = false) ↔ ((projectValue k x == projectValue k y) == p) = true := by
  rcases x with ⟨lx, fx⟩
  rcases y with ⟨ly, fy⟩
  dsimp at hx hy
  subst lx; subst ly
  cases p <;> cases fx <;> cases fy <;> simp [projectValue, beq_iff_eq]

/-- Actual pass does not reset or publish. A delayed winner retains its pair
while beginning the next scan or waiting at enter. -/
theorem concrete_pass_retains {n : Nat} (cfg : Config n) (p : Proc n)
    (s : Algorithm2.State n) (k : Nat) (h : (s p).pc = .pass k) :
    Algorithm2.ordinary cfg p s = some ⟨(if k < height n then Algorithm2.scan cfg p .first (k + 1) else .enter), (s p).q⟩ := by
  simp [Algorithm2.ordinary, h]

end EconomicalSolutions.Algorithm2.Node

#print axioms EconomicalSolutions.Algorithm2.Node.resume_projection
#print axioms EconomicalSolutions.Algorithm2.Node.waitSelf_projection
#print axioms EconomicalSolutions.Algorithm2.Node.concrete_pass_retains
