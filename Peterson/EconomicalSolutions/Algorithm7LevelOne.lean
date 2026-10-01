import Peterson.EconomicalSolutions.Algorithm7
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! An affine-counter certificate for original Algorithm 7 level-one starvation.
The explicit states are untrusted data. Every edge is reduced in the Lean kernel.
The surviving clock-1 counters gain two per period; no counter is saturated. -/
namespace EconomicalSolutions.Algorithm7.LevelOneCounterexample
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def config : Config 4 where
  order p := (List.finRange 4).filter (· ≠ p)
  nodup p := (List.nodup_finRange 4).filter _
  complete := by decide

def stemState (k : Fin 68) : State 4 :=
  match k.val with
  | 0 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩]
  | 1 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .join false false (.joinLower 0), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩]
  | 2 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .join false false (.joinUpper 3), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩]
  | 3 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .join false false (.joinUpper 2), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩]
  | 4 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .join false false (.joinWrite false), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩]
  | 5 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .join true false (.joinLower 1), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩]
  | 6 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .join true false (.joinLower 0), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩]
  | 7 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .join true false (.joinUpper 3), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩]
  | 8 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .join true false (.joinWrite false), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩]
  | 9 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .joinPublish false false, ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩]
  | 10 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩]
  | 11 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .join false false (.joinLower 2), ∅, 0, 0⟩]
  | 12 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .join false false (.joinLower 1), ∅, 0, 0⟩]
  | 13 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .join false false (.joinWrite false), ∅, 0, 0⟩]
  | 14 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .join true false (.joinUpper 3), ∅, 0, 0⟩]
  | 15 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .join true false (.joinUpper 2), ∅, 0, 0⟩]
  | 16 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .join true false (.joinWrite true), ∅, 0, 0⟩]
  | 17 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .idle, ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 18 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .join false false (.joinLower 1), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 19 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .join false false (.joinWrite false), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 20 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .join true false (.joinLower 0), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 21 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .join true false (.joinUpper 3), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 22 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .join true false (.joinUpper 2), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 23 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .join true false (.joinWrite true), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 24 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 25 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 26 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.tickLower 0 false), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 27 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.tickUpper 3), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 28 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.tickUpper 2), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 29 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.upperOwn 2 false), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 30 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.tickRead), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 31 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .tickWrite .one false (.live .one true false), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 32 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true false, .attempt .one true (.attempt), ∅, 1, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 33 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true false, .attempt .one true (.tickLower 1 false), ∅, 1, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 34 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true false, .attempt .one true (.lowerOwn 1 true), ∅, 1, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 35 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true false, .attempt .one true (.tickLower 0 true), ∅, 1, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 36 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true false, .attempt .one true (.tickRead), ∅, 1, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 37 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true false, .tickWrite .one true (.live .one true true), ∅, 1, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 38 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .pairDone .one, ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 39 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 40 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.tickLower 1 false), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 41 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.lowerOwn 1 true), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 42 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.tickLower 0 true), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 43 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.tickRead), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 44 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one false true, .tickWrite .one false (.live .one true true), ∅, 0, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 45 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one true true, .attempt .one true (.attempt), ∅, 1, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 46 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one true true, .attempt .one true (.tickLower 0 false), ∅, 1, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 47 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one true true, .attempt .one true (.tickUpper 3), ∅, 1, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 48 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one true true, .attempt .one true (.tickUpper 2), ∅, 1, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 49 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one true true, .attempt .one true (.upperOwn 2 true), ∅, 1, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 50 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one true true, .attempt .one true (.tickRead), ∅, 1, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 51 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one true true, .tickWrite .one true (.live .one true false), ∅, 1, 0⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 52 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one true false, .pairDone .one, ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 53 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 54 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.tickLower 0 false), ∅, 1, 1⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 55 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.tickUpper 3), ∅, 1, 1⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 56 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.tickUpper 2), ∅, 1, 1⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 57 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.upperOwn 2 true), ∅, 1, 1⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 58 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .attempt .one false (.tickRead), ∅, 1, 1⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 59 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one true true, .tickWrite .one false (.live .one false true), ∅, 1, 1⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 60 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one true (.attempt), ∅, 2, 1⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 61 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one true (.tickLower 1 false), ∅, 2, 1⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 62 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one true (.lowerOwn 1 false), ∅, 2, 1⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 63 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one true (.tickLower 0 true), ∅, 2, 1⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 64 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one true (.tickRead), ∅, 2, 1⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 65 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .tickWrite .one true (.live .one false false), ∅, 2, 1⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | 66 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .pairDone .one, ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]
  | _ => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.dead, .joinPublish false true, ∅, 0, 0⟩]

def stemCommand (k : Fin 68) : Command 4 :=
  match k.val with
  | 0 => .request 1
  | 1 => .run 1
  | 2 => .run 1
  | 3 => .run 1
  | 4 => .run 1
  | 5 => .run 1
  | 6 => .run 1
  | 7 => .run 1
  | 8 => .run 1
  | 9 => .run 1
  | 10 => .request 3
  | 11 => .run 3
  | 12 => .run 3
  | 13 => .run 3
  | 14 => .run 3
  | 15 => .run 3
  | 16 => .run 3
  | 17 => .request 2
  | 18 => .run 2
  | 19 => .run 2
  | 20 => .run 2
  | 21 => .run 2
  | 22 => .run 2
  | 23 => .run 2
  | 24 => .run 2
  | 25 => .run 1
  | 26 => .run 1
  | 27 => .run 1
  | 28 => .run 1
  | 29 => .run 1
  | 30 => .run 1
  | 31 => .run 1
  | 32 => .run 1
  | 33 => .run 1
  | 34 => .run 1
  | 35 => .run 1
  | 36 => .run 1
  | 37 => .run 1
  | 38 => .run 1
  | 39 => .run 2
  | 40 => .run 2
  | 41 => .run 2
  | 42 => .run 2
  | 43 => .run 2
  | 44 => .run 2
  | 45 => .run 2
  | 46 => .run 2
  | 47 => .run 2
  | 48 => .run 2
  | 49 => .run 2
  | 50 => .run 2
  | 51 => .run 2
  | 52 => .run 2
  | 53 => .run 1
  | 54 => .run 1
  | 55 => .run 1
  | 56 => .run 1
  | 57 => .run 1
  | 58 => .run 1
  | 59 => .run 1
  | 60 => .run 1
  | 61 => .run 1
  | 62 => .run 1
  | 63 => .run 1
  | 64 => .run 1
  | 65 => .run 1
  | 66 => .run 1
  | _ => .run 3

def cycleBase (k : Fin 168) : State 4 :=
  match k.val with
  | 0 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 1 => ![⟨.dead, .join false false (.joinUpper 3), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 2 => ![⟨.dead, .join false false (.joinWrite true), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 3 => ![⟨.dead, .join true true (.joinLower 2), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 4 => ![⟨.dead, .join true true (.joinWrite false), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 5 => ![⟨.dead, .joinPublish true false, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 6 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 7 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one false (.tickLower 1 false), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 8 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one false (.lowerOwn 1 false), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 9 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one false (.tickLower 0 true), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 10 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one false (.lowerOwn 0 true), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 11 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one true (.attempt), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 12 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one true (.tickLower 0 false), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 13 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one true (.lowerOwn 0 true), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 14 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .attempt .one true (.tickRead), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 15 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true false, .tickWrite .one true (.live .one true true), ∅, 1, 1⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 16 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true true, .pairDone .one, ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 17 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 18 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.tickLower 2 false), ∅, 0, 0⟩]
  | 19 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.lowerOwn 2 true), ∅, 0, 0⟩]
  | 20 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.tickLower 1 true), ∅, 0, 0⟩]
  | 21 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.lowerOwn 1 false), ∅, 0, 0⟩]
  | 22 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one true (.attempt), ∅, 0, 0⟩]
  | 23 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one true (.tickUpper 3), ∅, 0, 0⟩]
  | 24 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one true (.upperOwn 3 false), ∅, 0, 0⟩]
  | 25 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .pairDone .one, ∅, 0, 0⟩]
  | 26 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 27 => ![⟨.dead, .down, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 28 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 29 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.tickLower 0 false), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 30 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.tickUpper 3), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 31 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.upperOwn 3 false), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 32 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.tickUpper 2), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 33 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.upperOwn 2 true), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 34 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one true (.attempt), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 35 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one true (.tickLower 1 false), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 36 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one true (.lowerOwn 1 true), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 37 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one true (.tickLower 0 true), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 38 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one true (.lowerOwn 0 true), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 39 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one true (.tickRead), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 40 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .tickWrite .one true (.live .one false true), ∅, 2, 2⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 41 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .pairDone .one, ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 42 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 43 => ![⟨.dead, .join false false (.joinUpper 3), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 44 => ![⟨.dead, .join false false (.joinWrite true), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 45 => ![⟨.dead, .join true true (.joinLower 2), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 46 => ![⟨.dead, .join true true (.joinWrite true), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 47 => ![⟨.dead, .joinPublish true true, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 48 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 49 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.tickLower 1 false), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 50 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.lowerOwn 1 false), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 51 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.tickLower 0 true), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 52 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.lowerOwn 0 true), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 53 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one true (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 54 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one true (.tickLower 0 false), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 55 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one true (.lowerOwn 0 true), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 56 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .pairDone .one, ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 57 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 0⟩]
  | 58 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.tickLower 2 false), ∅, 0, 0⟩]
  | 59 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.lowerOwn 2 true), ∅, 0, 0⟩]
  | 60 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.tickLower 1 true), ∅, 0, 0⟩]
  | 61 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one false (.lowerOwn 1 false), ∅, 0, 0⟩]
  | 62 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one true (.attempt), ∅, 0, 0⟩]
  | 63 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one true (.tickUpper 3), ∅, 0, 0⟩]
  | 64 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one true (.upperOwn 3 true), ∅, 0, 0⟩]
  | 65 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one true (.tickUpper 2), ∅, 0, 0⟩]
  | 66 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one true (.upperOwn 2 true), ∅, 0, 0⟩]
  | 67 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one true (.tickUpper 1), ∅, 0, 0⟩]
  | 68 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one true (.upperOwn 1 true), ∅, 0, 0⟩]
  | 69 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .attempt .one true (.tickRead), ∅, 0, 0⟩]
  | 70 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false true, .tickWrite .one true (.live .one false false), ∅, 0, 0⟩]
  | 71 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .pairDone .one, ∅, 0, 1⟩]
  | 72 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 73 => ![⟨.dead, .down, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 74 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 75 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.tickLower 0 false), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 76 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.tickUpper 3), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 77 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.upperOwn 3 false), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 78 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.tickUpper 2), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 79 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.upperOwn 2 true), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 80 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one true (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 81 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one true (.tickLower 1 false), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 82 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one true (.lowerOwn 1 true), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 83 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .pairDone .one, ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 84 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 85 => ![⟨.dead, .join false false (.joinUpper 3), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 86 => ![⟨.dead, .join false false (.joinWrite true), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 87 => ![⟨.dead, .join true true (.joinLower 2), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 88 => ![⟨.dead, .join true true (.joinWrite true), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 89 => ![⟨.dead, .joinPublish true true, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 90 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 91 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.tickLower 1 false), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 92 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.lowerOwn 1 false), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 93 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.tickLower 0 true), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 94 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one false (.lowerOwn 0 true), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 95 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one true (.attempt), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 96 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one true (.tickLower 0 false), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 97 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one true (.lowerOwn 0 false), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 98 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .attempt .one true (.tickRead), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 99 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true true, .tickWrite .one true (.live .one true false), ∅, 1, 2⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 100 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true false, .pairDone .one, ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 101 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 102 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.tickLower 2 false), ∅, 0, 1⟩]
  | 103 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.lowerOwn 2 true), ∅, 0, 1⟩]
  | 104 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.tickLower 1 true), ∅, 0, 1⟩]
  | 105 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.lowerOwn 1 false), ∅, 0, 1⟩]
  | 106 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one true (.attempt), ∅, 0, 1⟩]
  | 107 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one true (.tickUpper 3), ∅, 0, 1⟩]
  | 108 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one true (.upperOwn 3 true), ∅, 0, 1⟩]
  | 109 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .pairDone .one, ∅, 0, 1⟩]
  | 110 => ![⟨.live .one true true, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 111 => ![⟨.dead, .down, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 112 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 113 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.tickLower 0 false), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 114 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.tickUpper 3), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 115 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.upperOwn 3 false), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 116 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.tickUpper 2), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 117 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one false (.upperOwn 2 true), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 118 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one true (.attempt), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 119 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one true (.tickLower 1 false), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 120 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one true (.lowerOwn 1 false), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 121 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one true (.tickLower 0 true), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 122 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one true (.lowerOwn 0 false), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 123 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .attempt .one true (.tickRead), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 124 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false true, .tickWrite .one true (.live .one false false), ∅, 2, 3⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 125 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .pairDone .one, ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 126 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 127 => ![⟨.dead, .join false false (.joinUpper 3), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 128 => ![⟨.dead, .join false false (.joinWrite true), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 129 => ![⟨.dead, .join true true (.joinLower 2), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 130 => ![⟨.dead, .join true true (.joinWrite false), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 131 => ![⟨.dead, .joinPublish true false, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 132 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 133 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.tickLower 1 false), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 134 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.lowerOwn 1 false), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 135 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.tickLower 0 true), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 136 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.lowerOwn 0 true), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 137 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one true (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 138 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one true (.tickLower 0 false), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 139 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one true (.lowerOwn 0 false), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 140 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .pairDone .one, ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 141 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 0, 1⟩]
  | 142 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.tickLower 2 false), ∅, 0, 1⟩]
  | 143 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.lowerOwn 2 true), ∅, 0, 1⟩]
  | 144 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.tickLower 1 true), ∅, 0, 1⟩]
  | 145 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one false (.lowerOwn 1 false), ∅, 0, 1⟩]
  | 146 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one true (.attempt), ∅, 0, 1⟩]
  | 147 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one true (.tickUpper 3), ∅, 0, 1⟩]
  | 148 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one true (.upperOwn 3 false), ∅, 0, 1⟩]
  | 149 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one true (.tickUpper 2), ∅, 0, 1⟩]
  | 150 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one true (.upperOwn 2 false), ∅, 0, 1⟩]
  | 151 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one true (.tickUpper 1), ∅, 0, 1⟩]
  | 152 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one true (.upperOwn 1 false), ∅, 0, 1⟩]
  | 153 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .attempt .one true (.tickRead), ∅, 0, 1⟩]
  | 154 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false false, .tickWrite .one true (.live .one false true), ∅, 0, 1⟩]
  | 155 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false true, .pairDone .one, ∅, 0, 2⟩]
  | 156 => ![⟨.live .one true false, .attempt .one false (.attempt), ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 2⟩]
  | 157 => ![⟨.dead, .down, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 2⟩]
  | 158 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 2⟩]
  | 159 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.tickLower 0 false), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 2⟩]
  | 160 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.tickUpper 3), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 2⟩]
  | 161 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.upperOwn 3 false), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 2⟩]
  | 162 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.tickUpper 2), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 2⟩]
  | 163 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one false (.upperOwn 2 true), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 2⟩]
  | 164 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one true (.attempt), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 2⟩]
  | 165 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one true (.tickLower 1 false), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 2⟩]
  | 166 => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .attempt .one true (.lowerOwn 1 false), ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 2⟩]
  | _ => ![⟨.dead, .idle, ∅, 0, 0⟩, ⟨.live .one false false, .pairDone .one, ∅, 2, 4⟩, ⟨.live .one true false, .attempt .one false (.attempt), ∅, 1, 3⟩, ⟨.live .one false true, .attempt .one false (.attempt), ∅, 0, 2⟩]

/-- Only the three surviving clock-1 counters grow; P0's reset counters do not. -/
def cycleState (a : Nat) (k : Fin 168) (p : Fin 4) : Local 4 :=
  let l := cycleBase k p
  { l with count1 := l.count1 + if p = 0 then 0 else a }

def cycleCommand (k : Fin 168) : Command 4 :=
  match k.val with
  | 0 => .request 0
  | 1 => .run 0
  | 2 => .run 0
  | 3 => .run 0
  | 4 => .run 0
  | 5 => .run 0
  | 6 => .run 2
  | 7 => .run 2
  | 8 => .run 2
  | 9 => .run 2
  | 10 => .run 2
  | 11 => .run 2
  | 12 => .run 2
  | 13 => .run 2
  | 14 => .run 2
  | 15 => .run 2
  | 16 => .run 2
  | 17 => .run 3
  | 18 => .run 3
  | 19 => .run 3
  | 20 => .run 3
  | 21 => .run 3
  | 22 => .run 3
  | 23 => .run 3
  | 24 => .run 3
  | 25 => .run 3
  | 26 => .fail 0
  | 27 => .restart 0
  | 28 => .run 1
  | 29 => .run 1
  | 30 => .run 1
  | 31 => .run 1
  | 32 => .run 1
  | 33 => .run 1
  | 34 => .run 1
  | 35 => .run 1
  | 36 => .run 1
  | 37 => .run 1
  | 38 => .run 1
  | 39 => .run 1
  | 40 => .run 1
  | 41 => .run 1
  | 42 => .request 0
  | 43 => .run 0
  | 44 => .run 0
  | 45 => .run 0
  | 46 => .run 0
  | 47 => .run 0
  | 48 => .run 2
  | 49 => .run 2
  | 50 => .run 2
  | 51 => .run 2
  | 52 => .run 2
  | 53 => .run 2
  | 54 => .run 2
  | 55 => .run 2
  | 56 => .run 2
  | 57 => .run 3
  | 58 => .run 3
  | 59 => .run 3
  | 60 => .run 3
  | 61 => .run 3
  | 62 => .run 3
  | 63 => .run 3
  | 64 => .run 3
  | 65 => .run 3
  | 66 => .run 3
  | 67 => .run 3
  | 68 => .run 3
  | 69 => .run 3
  | 70 => .run 3
  | 71 => .run 3
  | 72 => .fail 0
  | 73 => .restart 0
  | 74 => .run 1
  | 75 => .run 1
  | 76 => .run 1
  | 77 => .run 1
  | 78 => .run 1
  | 79 => .run 1
  | 80 => .run 1
  | 81 => .run 1
  | 82 => .run 1
  | 83 => .run 1
  | 84 => .request 0
  | 85 => .run 0
  | 86 => .run 0
  | 87 => .run 0
  | 88 => .run 0
  | 89 => .run 0
  | 90 => .run 2
  | 91 => .run 2
  | 92 => .run 2
  | 93 => .run 2
  | 94 => .run 2
  | 95 => .run 2
  | 96 => .run 2
  | 97 => .run 2
  | 98 => .run 2
  | 99 => .run 2
  | 100 => .run 2
  | 101 => .run 3
  | 102 => .run 3
  | 103 => .run 3
  | 104 => .run 3
  | 105 => .run 3
  | 106 => .run 3
  | 107 => .run 3
  | 108 => .run 3
  | 109 => .run 3
  | 110 => .fail 0
  | 111 => .restart 0
  | 112 => .run 1
  | 113 => .run 1
  | 114 => .run 1
  | 115 => .run 1
  | 116 => .run 1
  | 117 => .run 1
  | 118 => .run 1
  | 119 => .run 1
  | 120 => .run 1
  | 121 => .run 1
  | 122 => .run 1
  | 123 => .run 1
  | 124 => .run 1
  | 125 => .run 1
  | 126 => .request 0
  | 127 => .run 0
  | 128 => .run 0
  | 129 => .run 0
  | 130 => .run 0
  | 131 => .run 0
  | 132 => .run 2
  | 133 => .run 2
  | 134 => .run 2
  | 135 => .run 2
  | 136 => .run 2
  | 137 => .run 2
  | 138 => .run 2
  | 139 => .run 2
  | 140 => .run 2
  | 141 => .run 3
  | 142 => .run 3
  | 143 => .run 3
  | 144 => .run 3
  | 145 => .run 3
  | 146 => .run 3
  | 147 => .run 3
  | 148 => .run 3
  | 149 => .run 3
  | 150 => .run 3
  | 151 => .run 3
  | 152 => .run 3
  | 153 => .run 3
  | 154 => .run 3
  | 155 => .run 3
  | 156 => .fail 0
  | 157 => .restart 0
  | 158 => .run 1
  | 159 => .run 1
  | 160 => .run 1
  | 161 => .run 1
  | 162 => .run 1
  | 163 => .run 1
  | 164 => .run 1
  | 165 => .run 1
  | 166 => .run 1
  | _ => .run 1

def Edge (s : State 4) (c : Command 4) (t : State 4) : Prop :=
  match next config s c with
  | none => False
  | some u => ∀ p, u p = t p
instance (s : State 4) (c : Command 4) (t : State 4) : Decidable (Edge s c t) := by
  unfold Edge
  split <;> infer_instance

theorem edge_next {s t : State 4} {c : Command 4} (h : Edge s c t) :
    next config s c = some t := by
  unfold Edge at h
  split at h
  · contradiction
  · rename_i u he
    exact he.trans (congrArg some (funext h))

theorem stem_initial : stemState 0 = initial 4 := funext (by decide)

theorem stem_step (k : Fin 68) :
    next config (stemState k) (stemCommand k) = some
      (if h : k.val + 1 < 68 then stemState ⟨k.val + 1, h⟩ else cycleState 0 0) := by
  apply edge_next
  have h : ∀ k : Fin 68, Edge (stemState k) (stemCommand k)
      (if h : k.val + 1 < 68 then stemState ⟨k.val + 1, h⟩ else cycleState 0 0) := by decide
  exact h k

theorem cycle_step (a : Nat) (k : Fin 168) :
    next config (cycleState a k) (cycleCommand k) = some
      (if h : k.val + 1 < 168 then cycleState a ⟨k.val + 1, h⟩ else cycleState (a + 2) 0) := by
  apply edge_next
  fin_cases k <;> intro p <;> fin_cases p
  all_goals first | rfl | skip
  all_goals
    change (Local.mk _ _ _ _ _ : Local 4) = Local.mk _ _ _ _ _
    congr 1
  all_goals first
    | (change (0 + a) + 1 = 1 + a; omega)
    | (change (1 + a) + 1 = 2 + a; omega)
    | (change (2 + a) + 1 = 3 + a; omega)
    | (change (3 + a) + 1 = 4 + a; omega)
    | (change 4 + a = 2 + (a + 2); omega)
    | (change 3 + a = 1 + (a + 2); omega)
    | (change 2 + a = 0 + (a + 2); omega)

/-- The natural first-outcome target for an occurrence of the original
level-one exposure. The successful counter test is an actual own instruction;
a later replacement request cannot discharge the original episode. -/
def levelOneControl : PC n → Bool
  | .attempt .one _ _ | .tickWrite .one _ _ | .pairDone .one => true
  | _ => false
def InLevelOne (pc : PC n) : Prop := levelOneControl pc = true
instance (pc : PC n) : Decidable (InLevelOne pc) := inferInstanceAs (Decidable (_ = _))

def CompletesLevelOne {n : Nat} {cfg : Config n} (r : Run cfg) (p : Proc n) (t : Nat) : Prop :=
  r.command t = .run p ∧ (r.state t p).pc = .pairDone .one ∧
    3 ≤ (r.state t p).count0 ∧ 3 ≤ (r.state t p).count1

def LevelOneCompletionOrFailure {n : Nat} {cfg : Config n} (r : Run cfg) : Prop :=
  ∀ p t, InLevelOne (r.state t p).pc → ∃ u, t ≤ u ∧
    (∀ v, t ≤ v → v < u → r.event v ≠ .fail p ∧ ¬ CompletesLevelOne r p v) ∧
    (CompletesLevelOne r p u ∨ r.event u = .fail p)

def state (t : Nat) : State 4 :=
  if h : t < 68 then stemState ⟨t, h⟩ else
    cycleState (2 * ((t - 68) / 168)) ⟨(t - 68) % 168, Nat.mod_lt _ (by decide)⟩
def command (t : Nat) : Command 4 :=
  if h : t < 68 then stemCommand ⟨t, h⟩ else
    cycleCommand ⟨(t - 68) % 168, Nat.mod_lt _ (by decide)⟩

@[simp] theorem state_block (q : Nat) (k : Fin 168) :
    state (68 + (168 * q + k.val)) = cycleState (2 * q) k := by
  simp [state, show ¬68 + (168 * q + k.val) < 68 by omega,
    Nat.not_le_of_lt k.isLt, Nat.add_div, Nat.add_mod, Nat.div_eq_of_lt k.isLt,
    Nat.mod_eq_of_lt k.isLt]
@[simp] theorem command_block (q : Nat) (k : Fin 168) :
    command (68 + (168 * q + k.val)) = cycleCommand k := by
  simp [command, Nat.add_mod, Nat.mod_eq_of_lt k.isLt]

theorem execution_step (t : Nat) :
    next config (state t) (command t) = some (state (t + 1)) := by
  by_cases h : t < 68
  · have ht := stem_step ⟨t, h⟩
    by_cases hn : t + 1 < 68
    · simpa [state, command, h, hn] using ht
    · have he : t = 67 := by omega
      subst t
      simpa [state, command] using ht
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 68 ≤ t)
    have decomp : j = 168 * (j / 168) + j % 168 := by omega
    let q := j / 168
    let k : Fin 168 := ⟨j % 168, Nat.mod_lt _ (by decide)⟩
    have je : j = 168 * q + k.val := decomp
    rw [je, state_block, command_block, cycle_step]
    by_cases hk : k.val + 1 < 168
    · simp only [hk, dite_true]
      have e : 68 + (168 * q + k.val) + 1 = 68 + (168 * q + (k.val + 1)) := by omega
      rw [e, state_block q ⟨k.val + 1, hk⟩]
    · simp only [hk, dite_false]
      have ek : k.val = 167 := by omega
      have e : 68 + (168 * q + k.val) + 1 = 68 + (168 * (q + 1) + (0 : Fin 168).val) := by
        simp only [Fin.val_zero]; omega
      rw [e, state_block]
      congr 2

def witness : Run config where
  state := state
  command := command
  initialized := stem_initial
  valid := execution_step

theorem cycle_pc (a : Nat) (k : Fin 168) (p : Fin 4) :
    (cycleState a k p).pc = (cycleState 0 k p).pc := by
  rfl

theorem cycle_count0 (a : Nat) (k : Fin 168) (p : Fin 4) :
    (cycleState a k p).count0 = (cycleState 0 k p).count0 := by
  rfl

theorem cycle_label (a : Nat) (k : Fin 168) :
    label (cycleState a k) (cycleCommand k) =
      label (cycleState 0 k) (cycleCommand k) := by
  generalize hc : cycleCommand k = c
  cases c <;> simp only [label, cycle_pc]

/-- Every physical process performs a real instruction in every period. -/
theorem ordinary_present : ∀ p : Fin 4, ∃ k : Fin 168, cycleCommand k = .run p := by decide

theorem every_position_runs (p : Fin 4) (t : Nat) :
    ∃ u, t ≤ u ∧ command u = .run p := by
  obtain ⟨k, hk⟩ := ordinary_present p
  exact ⟨68 + (168 * t + k.val), by omega, by simpa using hk⟩

theorem protocol_scheduling : ProtocolScheduling witness := by
  intro t p _
  obtain ⟨u, hu, he⟩ := every_position_runs p t
  exact ⟨u, hu, Or.inl he⟩

/-- These finite facts include all used caches and both real clock controls. -/
theorem cycle_facts : ∀ k : Fin 168, ∀ p : Fin 4,
    (cycleState 0 k p).pc ≠ .cs ∧
    (p ≠ 0 → InLevelOne (cycleState 0 k p).pc ∧
      (cycleState 0 k p).count0 < 3 ∧
      label (cycleState 0 k) (cycleCommand k) ≠ .fail p ∧
      label (cycleState 0 k) (cycleCommand k) ≠ .queuePublish p ∧
      label (cycleState 0 k) (cycleCommand k) ≠ .entry p) := by decide

theorem tail_facts (p : Fin 4) (t : Nat) (ht : 68 ≤ t) :
    (witness.state t p).pc ≠ .cs ∧
    (p ≠ 0 → InLevelOne (witness.state t p).pc ∧
      (witness.state t p).count0 < 3 ∧ witness.event t ≠ .fail p ∧
      witness.event t ≠ .queuePublish p ∧ witness.event t ≠ .entry p) := by
  simpa [witness, state, command, Run.event, show ¬t < 68 by omega,
    cycle_pc, cycle_count0, cycle_label] using
    cycle_facts ⟨(t - 68) % 168, Nat.mod_lt _ (by decide)⟩ p

/-- No process reaches critical code anywhere, so the extra completion premise
also holds, although the doorway counterexample needs only scheduling. -/
theorem critical_completion : CriticalCompletion witness := by
  have stem : ∀ k : Fin 68, ∀ p : Fin 4, (stemState k p).pc ≠ .cs := by decide
  intro t p hc
  by_cases ht : t < 68
  · exact False.elim (stem ⟨t, ht⟩ p (by simpa [witness, state, ht] using hc))
  · exact False.elim ((tail_facts p t (by omega)).1 hc)

theorem level_one_starvation : ProtocolScheduling witness ∧ CriticalCompletion witness ∧
    ∀ p : Fin 4, p ≠ 0 → ∀ t, 68 ≤ t →
      InLevelOne (witness.state t p).pc ∧ (witness.state t p).count0 < 3 ∧
      witness.event t ≠ .fail p ∧ witness.event t ≠ .queuePublish p ∧ witness.event t ≠ .entry p :=
  ⟨protocol_scheduling, critical_completion, fun p hp t ht => (tail_facts p t ht).2 hp⟩

theorem not_level_one_completion_or_failure : ¬ LevelOneCompletionOrFailure witness := by
  intro h
  obtain ⟨u, hu, _, ho⟩ := h 1 68 ((tail_facts 1 68 (by omega)).2 (by decide)).1
  have stuck := (tail_facts 1 u hu).2 (by decide)
  rcases ho with done | failed
  · have := done.2.2.1
    omega
  · exact stuck.2.2.1 failed

/-- Every original survivor also refutes the doorway and entry conclusions,
even with critical completion. No later request replaces any survivor. -/
theorem no_original_outcomes (p : Fin 4) (hp : p ≠ 0) :
    ¬ ∃ u, 68 ≤ u ∧ (witness.event u = .queuePublish p ∨
      witness.event u = .entry p ∨ witness.event u = .fail p) := by
  rintro ⟨u, hu, h⟩
  have facts := (tail_facts p u hu).2 hp
  rcases h with h | h | h
  · exact facts.2.2.2.1 h
  · exact facts.2.2.2.2 h
  · exact facts.2.2.1 h

/-- The three surviving requests are the ones actually started in the finite
setup. No own failure, queue publication or entry occurs even in that setup. -/
theorem original_requests :
    witness.event 0 = .request 1 ∧ witness.event 17 = .request 2 ∧
    witness.event 10 = .request 3 ∧
    ∀ p : Fin 4, p ≠ 0 → ∀ t,
      witness.event t ≠ .fail p ∧ witness.event t ≠ .queuePublish p ∧ witness.event t ≠ .entry p := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  have stem : ∀ k : Fin 68, ∀ p : Fin 4, p ≠ 0 →
      label (stemState k) (stemCommand k) ≠ .fail p ∧
      label (stemState k) (stemCommand k) ≠ .queuePublish p ∧
      label (stemState k) (stemCommand k) ≠ .entry p := by decide
  intro p hp t
  by_cases ht : t < 68
  · simpa [witness, Run.event, state, command, ht] using stem ⟨t, ht⟩ p hp
  · exact ((tail_facts p t (by omega)).2 hp).2.2

#print axioms original_requests

#print axioms stem_step
#print axioms cycle_step
#print axioms execution_step
#print axioms level_one_starvation
#print axioms not_level_one_completion_or_failure
#print axioms no_original_outcomes

end EconomicalSolutions.Algorithm7.LevelOneCounterexample
