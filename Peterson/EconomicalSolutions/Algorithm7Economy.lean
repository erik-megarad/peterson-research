import Peterson.EconomicalSolutions.Algorithm7
import Mathlib.Tactic.FinCases

/-! The source counts the possible values of one whole visible register.
The private clock counters, lists, and control positions are not register fields. -/
namespace EconomicalSolutions.Algorithm7

def valueCode : Value → Fin 14
  | .dead => 0
  | .cs => 1
  | .live .one false false => 2
  | .live .one false true => 3
  | .live .one true false => 4
  | .live .one true true => 5
  | .live .two false false => 6
  | .live .two false true => 7
  | .live .two true false => 8
  | .live .two true true => 9
  | .live .three false false => 10
  | .live .three false true => 11
  | .live .three true false => 12
  | .live .three true true => 13

def valueDecode (i : Fin 14) : Value :=
  match i.val with
  | 0 => .dead
  | 1 => .cs
  | 2 => .live .one false false
  | 3 => .live .one false true
  | 4 => .live .one true false
  | 5 => .live .one true true
  | 6 => .live .two false false
  | 7 => .live .two false true
  | 8 => .live .two true false
  | 9 => .live .two true true
  | 10 => .live .three false false
  | 11 => .live .three false true
  | 12 => .live .three true false
  | _ => .live .three true true

/-- A lossless code of every possible whole register value. -/
def valueEquiv : Value ≃ Fin 14 where
  toFun := valueCode
  invFun := valueDecode
  left_inv := by
    intro v
    cases v with
    | dead => rfl
    | cs => rfl
    | live level b0 b1 =>
      cases level <;> cases b0 <;> cases b1 <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> decide

noncomputable instance : Fintype Value := Fintype.ofEquiv (Fin 14) valueEquiv.symm

theorem value_card : Fintype.card Value = 14 := by
  rw [Fintype.card_congr valueEquiv]
  simp

/-- Each process's actual register has the same lossless code, at any population. -/
def registerCode {n : Nat} (s : State n) (p : Proc n) : Fin 14 :=
  valueCode (s p).value

theorem registerCode_decode {n : Nat} (s : State n) (p : Proc n) :
    valueDecode (registerCode s p) = (s p).value :=
  valueEquiv.left_inv _

theorem initial_registerCode {n : Nat} (p : Proc n) :
    registerCode (initial n) p = 0 := rfl

/-- Decoding the register before a clock read gives the same observed bit. -/
theorem bit_registerCode {n : Nat} (s : State n) (q : Proc n) (clock : Bool) :
    bit (valueDecode (registerCode s q)) clock = bit (s q).value clock := by
  rw [registerCode_decode]

/-- The value bound holds at every time of every run, with no fairness premise. -/
theorem run_registerCode {n : Nat} {cfg : Config n} (r : Run cfg)
    (t : Nat) (p : Proc n) :
    valueDecode (registerCode (r.state t) p) = (r.state t p).value :=
  registerCode_decode _ _

/-- A clock read depends on peers' visible register values and the actor's
explicit clock control, not on peers' private counters, lists, or controls. -/
theorem clockInstruction_visible {n : Nat} (s t : State n) (p : Proc n)
    (clock : Bool) (pc : Algorithm3.PC)
    (h : ∀ q, (s q).value = (t q).value) :
    clockInstruction s p clock pc = clockInstruction t p clock pc := by
  unfold clockInstruction
  dsimp
  congr 1
  funext j
  simp only [h (position j clock)]

/-- The next-state interpreter changes only the acting process's register. -/
theorem next_other_register {n : Nat} (cfg : Config n) (s t : State n)
    (c : Command n) (p q : Proc n) (h : next cfg s c = some t)
    (hactor : c = .run p ∨ c = .request p ∨ c = .complete p ∨
      c = .fail p ∨ c = .restart p) (hne : q ≠ p) :
    registerCode t q = registerCode s q := by
  rcases hactor with rfl | rfl | rfl | rfl | rfl
  · simp only [next, Option.map_eq_some_iff] at h
    rcases h with ⟨l, _, rfl⟩
    simp [registerCode, setLocal, hne]
  all_goals
    simp only [next] at h
    split at h <;> simp_all [registerCode]
    rw [← h]
    simp [setLocal, hne]

/-- At fixed configuration and actor, the actor's full local state and the
visible register values determine its ordinary-instruction result. -/
theorem ordinary_visible {n : Nat} (cfg : Config n) (s t : State n)
    (p : Proc n) (hlocal : s p = t p)
    (hvisible : ∀ q, (s q).value = (t q).value) :
    ordinary cfg s p = ordinary cfg t p := by
  have hclock (clock : Bool) (pc : Algorithm3.PC) :
      clockInstruction s p clock pc = clockInstruction t p clock pc :=
    clockInstruction_visible s t p clock pc hvisible
  simp only [ordinary, hlocal]
  cases (t p).pc <;> simp [hvisible, hclock]

end EconomicalSolutions.Algorithm7

#print axioms EconomicalSolutions.Algorithm7.valueEquiv
#print axioms EconomicalSolutions.Algorithm7.value_card
#print axioms EconomicalSolutions.Algorithm7.registerCode_decode
#print axioms EconomicalSolutions.Algorithm7.initial_registerCode
#print axioms EconomicalSolutions.Algorithm7.bit_registerCode
#print axioms EconomicalSolutions.Algorithm7.run_registerCode
#print axioms EconomicalSolutions.Algorithm7.clockInstruction_visible
#print axioms EconomicalSolutions.Algorithm7.next_other_register
#print axioms EconomicalSolutions.Algorithm7.ordinary_visible
