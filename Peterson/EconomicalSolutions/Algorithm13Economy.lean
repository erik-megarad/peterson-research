module

public import Peterson.EconomicalSolutions.Algorithm1
public import Peterson.EconomicalSolutions.Algorithm3
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Exact visible-register alphabets for the frozen Algorithms 1 and 3.
The program counters and cached payloads remain private fields of `Local`. -/

namespace EconomicalSolutions.Algorithm1

/-- A lossless code for Algorithm 1's whole shared register. -/
def valueCode : Value → Fin 3
  | .O => 0
  | .T => 1
  | .F => 2

def valueDecode : Fin 3 → Value
  | 0 => .O
  | 1 => .T
  | _ => .F

def valueEquiv : Value ≃ Fin 3 where
  toFun := valueCode
  invFun := valueDecode
  left_inv := by intro v; cases v <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

noncomputable instance : Fintype Value := Fintype.ofEquiv (Fin 3) valueEquiv.symm

theorem value_card : Fintype.card Value = 3 := by
  rw [Fintype.card_congr valueEquiv]
  simp

def registerCode (s : State) (p : Proc) : Fin 3 := valueCode (s.local p).q

theorem registerCode_decode (s : State) (p : Proc) :
    valueDecode (registerCode s p) = (s.local p).q := valueEquiv.left_inv _

theorem initial_registerCode (p : Proc) : registerCode initial p = 0 := by
  cases p <;> rfl

/-- The ordinary interpreter's peer argument is exactly the peer's visible q. -/
theorem ordinary_peer_read (s : State) (p : Proc) :
    ordinary p (s.local p) (s.local (!p)).q =
      ordinary p (s.local p) (valueDecode (registerCode s (!p))) := by
  rw [registerCode_decode]

/-- At fixed actor, equal actor-local states and equal visible registers
fix the ordinary result. -/
theorem ordinary_visible (s t : State) (p : Proc)
    (hlocal : s.local p = t.local p)
    (hvisible : ∀ q, (s.local q).q = (t.local q).q) :
    ordinary p (s.local p) (s.local (!p)).q =
      ordinary p (t.local p) (t.local (!p)).q := by
  rw [hlocal, hvisible (!p)]

/-- The interpreter's cached first read is the chosen value for its later write. -/
theorem ordinary_read1 (p : Proc) (l : Local) (peer : Value)
    (hpc : l.pc = .read1) :
    ordinary p l peer = some { l with pc := .write1 (matching p peer) } := by
  simp [ordinary, hpc]

theorem ordinary_write1 (p : Proc) (l : Local) (peer : Value) (v : Value)
    (hpc : l.pc = .write1 v) : ordinary p l peer = some ⟨.read2, v⟩ := by
  simp [ordinary, hpc]

theorem ordinary_write2 (p : Proc) (l : Local) (peer : Value) (v : Value)
    (hpc : l.pc = .write2 v) : ordinary p l peer = some ⟨.waitPeer, v⟩ := by
  simp [ordinary, hpc]

/-- Updating one local state leaves every other visible register unchanged. -/
theorem setLocal_other_register (s : State) (p q : Proc) (l : Local)
    (hne : q ≠ p) : registerCode (s.setLocal p l) q = registerCode s q := by
  cases p <;> cases q <;> simp_all [registerCode, State.local, State.setLocal]

/-- Non-actor commands preserve that process's register. -/
theorem next_other_register (s t : State) (c : Command) (p q : Proc)
    (h : next s c = some t)
    (hactor : c = .run p ∨ c = .fail p ∨ c = .restart p)
    (hne : q ≠ p) : registerCode t q = registerCode s q := by
  rcases hactor with rfl | rfl | rfl
  · simp only [next] at h
    cases ho : ordinary p (s.local p) (s.local (!p)).q with
    | none => simp [ho] at h
    | some l =>
        simp only [ho, Option.map_some] at h
        cases h
        exact setLocal_other_register s p q l hne
  · simp only [next] at h
    by_cases hdown : (s.local p).pc = .down
    · simp [hdown] at h
    · simp [hdown] at h
      rw [← h]
      exact setLocal_other_register s p q ⟨.down, .O⟩ hne
  · simp only [next] at h
    by_cases hdown : (s.local p).pc = .down
    · simp [hdown] at h
      rw [← h]
      exact setLocal_other_register s p q ⟨.idle, .O⟩ hne
    · simp [hdown] at h

end EconomicalSolutions.Algorithm1

namespace EconomicalSolutions.Algorithm3

/-- A lossless code for dead and the two Boolean clock-register values. -/
def valueCode : Option Bool → Fin 3
  | none => 0
  | some false => 1
  | some true => 2

def valueDecode : Fin 3 → Option Bool
  | 0 => none
  | 1 => some false
  | _ => some true

def valueEquiv : Option Bool ≃ Fin 3 where
  toFun := valueCode
  invFun := valueDecode
  left_inv := by intro v; cases v with | none => rfl | some b => cases b <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

noncomputable instance : Fintype (Option Bool) := Fintype.ofEquiv (Fin 3) valueEquiv.symm

theorem value_card : Fintype.card (Option Bool) = 3 := by
  rw [Fintype.card_congr valueEquiv]
  simp

def registerCode {n : Nat} (s : State n) (p : Fin n) : Fin 3 := valueCode (s p).q

theorem registerCode_decode {n : Nat} (s : State n) (p : Fin n) :
    valueDecode (registerCode s p) = (s p).q := valueEquiv.left_inv _

theorem initial_registerCode {n : Nat} (p : Fin n) : registerCode (initial n) p = 0 := by
  rfl

/-- Decoding a peer register preserves the exact bit or dead observation. -/
theorem peer_read_registerCode {n : Nat} (s : State n) (q : Fin n) :
    valueDecode (registerCode s q) = (s q).q := registerCode_decode _ _

/-- At fixed actor and actor-local private state, the ordinary interpreter is
fixed by the vector of visible q fields, regardless of peers' private PCs. -/
theorem ordinary_visible {n : Nat} (s t : State n) (i : Fin n)
    (hlocal : s i = t i)
    (hvisible : ∀ q, (s q).q = (t q).q) :
    ordinary s i = ordinary t i := by
  simp only [ordinary, hlocal]
  cases (t i).pc <;> simp [hvisible]

/-- A successful join publication writes exactly its cached bit. -/
theorem ordinary_joinWrite (s : State n) (i : Fin n) (b : Bool)
    (hpc : (s i).pc = .joinWrite b) (hdead : (s i).q = none) :
    ordinary s i = some ⟨some b, .attempt⟩ := by
  simp [ordinary, hpc, hdead]

/-- A successful ticking write publishes its cached complemented bit. -/
theorem ordinary_tickWrite (s : State n) (i : Fin n) (b v : Bool)
    (hpc : (s i).pc = .tickWrite b) (hq : (s i).q = some v) (hchange : b ≠ v) :
    ordinary s i = some ⟨some b, .attempt⟩ := by
  simp [ordinary, hpc, hq, hchange]

/-- Updating one actor's local state leaves every other visible register unchanged. -/
theorem setLocal_other_register {n : Nat} (s : State n) (i q : Fin n) (l : Local)
    (hne : q ≠ i) : registerCode (setLocal s i l) q = registerCode s q := by
  simp [registerCode, setLocal, hne]

/-- A non-actor's visible register is unchanged by a successful command. -/
theorem next_other_register {n : Nat} (s t : State n) (c : Command n)
    (i q : Fin n) (h : next s c = some t)
    (hactor : c = .run i ∨ c = .start i ∨ c = .fail i ∨ c = .restart i)
    (hne : q ≠ i) : registerCode t q = registerCode s q := by
  rcases hactor with rfl | rfl | rfl | rfl
  · simp only [next, Option.map_eq_some_iff] at h
    rcases h with ⟨l, _, rfl⟩
    exact setLocal_other_register s i q l hne
  · simp only [next] at h
    by_cases hstart : (s i).pc = .idle ∧ (s i).q = none
    · simp [hstart] at h
      rw [← h]
      exact setLocal_other_register s i q ⟨none, joinLower i.val n i.val⟩ hne
    · simp [hstart] at h
  · simp only [next] at h
    by_cases hdown : (s i).pc = .down
    · simp [hdown] at h
    · simp [hdown] at h
      rw [← h]
      exact setLocal_other_register s i q ⟨none, .down⟩ hne
  · simp only [next] at h
    by_cases hdown : (s i).pc = .down
    · simp [hdown] at h
      rw [← h]
      exact setLocal_other_register s i q ⟨none, .idle⟩ hne
    · simp [hdown] at h

end EconomicalSolutions.Algorithm3

#print axioms EconomicalSolutions.Algorithm1.valueEquiv
#print axioms EconomicalSolutions.Algorithm1.value_card
#print axioms EconomicalSolutions.Algorithm1.registerCode_decode
#print axioms EconomicalSolutions.Algorithm1.initial_registerCode
#print axioms EconomicalSolutions.Algorithm1.ordinary_peer_read
#print axioms EconomicalSolutions.Algorithm1.ordinary_visible
#print axioms EconomicalSolutions.Algorithm1.ordinary_read1
#print axioms EconomicalSolutions.Algorithm1.ordinary_write1
#print axioms EconomicalSolutions.Algorithm1.ordinary_write2
#print axioms EconomicalSolutions.Algorithm1.next_other_register
#print axioms EconomicalSolutions.Algorithm3.valueEquiv
#print axioms EconomicalSolutions.Algorithm3.value_card
#print axioms EconomicalSolutions.Algorithm3.registerCode_decode
#print axioms EconomicalSolutions.Algorithm3.initial_registerCode
#print axioms EconomicalSolutions.Algorithm3.peer_read_registerCode
#print axioms EconomicalSolutions.Algorithm3.ordinary_visible
#print axioms EconomicalSolutions.Algorithm3.ordinary_joinWrite
#print axioms EconomicalSolutions.Algorithm3.ordinary_tickWrite
#print axioms EconomicalSolutions.Algorithm3.next_other_register
