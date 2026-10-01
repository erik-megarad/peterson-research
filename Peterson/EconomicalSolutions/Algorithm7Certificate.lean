import Peterson.EconomicalSolutions.Algorithm7Replay

/-! Explicit prestate certificate printed from the actual interpreter.
Regenerate with `#eval IO.FS.writeFile "Peterson/EconomicalSolutions/Algorithm7Certificate.lean" certificateSource commands`
in namespace EconomicalSolutions.Algorithm7.Counterexample after importing Algorithm7Replay.
The printer is untrusted; Algorithm7Counterexample checks every edge. -/
namespace EconomicalSolutions.Algorithm7.Counterexample
def snapshots : Array (Local 2 × Local 2) := #[
  -- State 0
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.dead, PC.idle, ∅, 0, 0⟩),
  -- State 1
  (⟨Value.dead, PC.join false false (Algorithm3.PC.joinUpper 1), ∅, 0, 0⟩, ⟨Value.dead, PC.idle, ∅, 0, 0⟩),
  -- State 2
  (⟨Value.dead, PC.join false false (Algorithm3.PC.joinUpper 1), ∅, 0, 0⟩, ⟨Value.dead, PC.join false false (Algorithm3.PC.joinLower 0), ∅, 0, 0⟩),
  -- State 3
  (⟨Value.dead, PC.join false false (Algorithm3.PC.joinWrite false), ∅, 0, 0⟩, ⟨Value.dead, PC.join false false (Algorithm3.PC.joinLower 0), ∅, 0, 0⟩),
  -- State 4
  (⟨Value.dead, PC.join true false (Algorithm3.PC.joinLower 0), ∅, 0, 0⟩, ⟨Value.dead, PC.join false false (Algorithm3.PC.joinLower 0), ∅, 0, 0⟩),
  -- State 5
  (⟨Value.dead, PC.join true false (Algorithm3.PC.joinWrite false), ∅, 0, 0⟩, ⟨Value.dead, PC.join false false (Algorithm3.PC.joinLower 0), ∅, 0, 0⟩),
  -- State 6
  (⟨Value.dead, PC.joinPublish false false, ∅, 0, 0⟩, ⟨Value.dead, PC.join false false (Algorithm3.PC.joinLower 0), ∅, 0, 0⟩),
  -- State 7
  (⟨Value.dead, PC.joinPublish false false, ∅, 0, 0⟩, ⟨Value.dead, PC.join false false (Algorithm3.PC.joinWrite false), ∅, 0, 0⟩),
  -- State 8
  (⟨Value.dead, PC.joinPublish false false, ∅, 0, 0⟩, ⟨Value.dead, PC.join true false (Algorithm3.PC.joinUpper 1), ∅, 0, 0⟩),
  -- State 9
  (⟨Value.dead, PC.joinPublish false false, ∅, 0, 0⟩, ⟨Value.dead, PC.join true false (Algorithm3.PC.joinWrite false), ∅, 0, 0⟩),
  -- State 10
  (⟨Value.dead, PC.joinPublish false false, ∅, 0, 0⟩, ⟨Value.dead, PC.joinPublish false false, ∅, 0, 0⟩),
  -- State 11
  (⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.dead, PC.joinPublish false false, ∅, 0, 0⟩),
  -- State 12
  (⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩),
  -- State 13
  (⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.tickUpper 1), ∅, 0, 0⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩),
  -- State 14
  (⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.upperOwn 1 false), ∅, 0, 0⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩),
  -- State 15
  (⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.tickRead), ∅, 0, 0⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩),
  -- State 16
  (⟨Value.live (Level.one) false false, PC.tickWrite
  (Phase.one)
  false
  (Value.live (Level.one) true false), ∅, 0, 0⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩),
  -- State 17
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.attempt), ∅, 1, 0⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩),
  -- State 18
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.tickLower 0 false), ∅, 1, 0⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩),
  -- State 19
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.lowerOwn 0 false), ∅, 1, 0⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩),
  -- State 20
  (⟨Value.live (Level.one) true false, PC.pairDone (Phase.one), ∅, 1, 0⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩),
  -- State 21
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 0⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩),
  -- State 22
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 0⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.tickLower 0 false), ∅, 0, 0⟩),
  -- State 23
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 0⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.lowerOwn 0 true), ∅, 0, 0⟩),
  -- State 24
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 0⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.tickRead), ∅, 0, 0⟩),
  -- State 25
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 0⟩, ⟨Value.live (Level.one) false false, PC.tickWrite
  (Phase.one)
  false
  (Value.live (Level.one) true false), ∅, 0, 0⟩),
  -- State 26
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 0⟩, ⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.attempt), ∅, 1, 0⟩),
  -- State 27
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 0⟩, ⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.tickUpper 1), ∅, 1, 0⟩),
  -- State 28
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 0⟩, ⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.upperOwn 1 false), ∅, 1, 0⟩),
  -- State 29
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 0⟩, ⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.tickRead), ∅, 1, 0⟩),
  -- State 30
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 0⟩, ⟨Value.live (Level.one) true false, PC.tickWrite
  (Phase.one)
  true
  (Value.live (Level.one) true true), ∅, 1, 0⟩),
  -- State 31
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 0⟩, ⟨Value.live (Level.one) true true, PC.pairDone (Phase.one), ∅, 1, 1⟩),
  -- State 32
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 0⟩, ⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 33
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.tickUpper 1), ∅, 1, 0⟩, ⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 34
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.upperOwn 1 true), ∅, 1, 0⟩, ⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 35
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.tickRead), ∅, 1, 0⟩, ⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 36
  (⟨Value.live (Level.one) true false, PC.tickWrite
  (Phase.one)
  false
  (Value.live (Level.one) false false), ∅, 1, 0⟩, ⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 37
  (⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.attempt), ∅, 2, 0⟩, ⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 38
  (⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.tickLower 0 false), ∅, 2, 0⟩, ⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 39
  (⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.lowerOwn 0 true), ∅, 2, 0⟩, ⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 40
  (⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.tickRead), ∅, 2, 0⟩, ⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 41
  (⟨Value.live (Level.one) false false, PC.tickWrite
  (Phase.one)
  true
  (Value.live (Level.one) false true), ∅, 2, 0⟩, ⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 42
  (⟨Value.live (Level.one) false true, PC.pairDone (Phase.one), ∅, 2, 1⟩, ⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 43
  (⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 1⟩, ⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 44
  (⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 1⟩, ⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.tickLower 0 false), ∅, 1, 1⟩),
  -- State 45
  (⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 1⟩, ⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.lowerOwn 0 false), ∅, 1, 1⟩),
  -- State 46
  (⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 1⟩, ⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.tickRead), ∅, 1, 1⟩),
  -- State 47
  (⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 1⟩, ⟨Value.live (Level.one) true true, PC.tickWrite
  (Phase.one)
  false
  (Value.live (Level.one) false true), ∅, 1, 1⟩),
  -- State 48
  (⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 1⟩, ⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.attempt), ∅, 2, 1⟩),
  -- State 49
  (⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 1⟩, ⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.tickUpper 1), ∅, 2, 1⟩),
  -- State 50
  (⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 1⟩, ⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.upperOwn 1 true), ∅, 2, 1⟩),
  -- State 51
  (⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 1⟩, ⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.tickRead), ∅, 2, 1⟩),
  -- State 52
  (⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 1⟩, ⟨Value.live (Level.one) false true, PC.tickWrite
  (Phase.one)
  true
  (Value.live (Level.one) false false), ∅, 2, 1⟩),
  -- State 53
  (⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 1⟩, ⟨Value.live (Level.one) false false, PC.pairDone (Phase.one), ∅, 2, 2⟩),
  -- State 54
  (⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 1⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 55
  (⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.tickUpper 1), ∅, 2, 1⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 56
  (⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.upperOwn 1 false), ∅, 2, 1⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 57
  (⟨Value.live (Level.one) false true, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.tickRead), ∅, 2, 1⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 58
  (⟨Value.live (Level.one) false true, PC.tickWrite
  (Phase.one)
  false
  (Value.live (Level.one) true true), ∅, 2, 1⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 59
  (⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.attempt), ∅, 3, 1⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 60
  (⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.tickLower 0 false), ∅, 3, 1⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 61
  (⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.lowerOwn 0 false), ∅, 3, 1⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 62
  (⟨Value.live (Level.one) true true, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.tickRead), ∅, 3, 1⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 63
  (⟨Value.live (Level.one) true true, PC.tickWrite
  (Phase.one)
  true
  (Value.live (Level.one) true false), ∅, 3, 1⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 64
  (⟨Value.live (Level.one) true false, PC.pairDone (Phase.one), ∅, 3, 2⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 65
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 3, 2⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 66
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 3, 2⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.tickLower 0 false), ∅, 2, 2⟩),
  -- State 67
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 3, 2⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.lowerOwn 0 true), ∅, 2, 2⟩),
  -- State 68
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 3, 2⟩, ⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.tickRead), ∅, 2, 2⟩),
  -- State 69
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 3, 2⟩, ⟨Value.live (Level.one) false false, PC.tickWrite
  (Phase.one)
  false
  (Value.live (Level.one) true false), ∅, 2, 2⟩),
  -- State 70
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 3, 2⟩, ⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.attempt), ∅, 3, 2⟩),
  -- State 71
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 3, 2⟩, ⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.tickUpper 1), ∅, 3, 2⟩),
  -- State 72
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 3, 2⟩, ⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.upperOwn 1 false), ∅, 3, 2⟩),
  -- State 73
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 3, 2⟩, ⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.tickRead), ∅, 3, 2⟩),
  -- State 74
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 3, 2⟩, ⟨Value.live (Level.one) true false, PC.tickWrite
  (Phase.one)
  true
  (Value.live (Level.one) true true), ∅, 3, 2⟩),
  -- State 75
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 3, 2⟩, ⟨Value.live (Level.one) true true, PC.pairDone (Phase.one), ∅, 3, 3⟩),
  -- State 76
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.attempt), ∅, 3, 2⟩, ⟨Value.live (Level.one) true true, PC.build [0], ∅, 3, 3⟩),
  -- State 77
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.tickUpper 1), ∅, 3, 2⟩, ⟨Value.live (Level.one) true true, PC.build [0], ∅, 3, 3⟩),
  -- State 78
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.upperOwn 1 true), ∅, 3, 2⟩, ⟨Value.live (Level.one) true true, PC.build [0], ∅, 3, 3⟩),
  -- State 79
  (⟨Value.live (Level.one) true false, PC.attempt
  (Phase.one)
  false
  (Algorithm3.PC.tickRead), ∅, 3, 2⟩, ⟨Value.live (Level.one) true true, PC.build [0], ∅, 3, 3⟩),
  -- State 80
  (⟨Value.live (Level.one) true false, PC.tickWrite
  (Phase.one)
  false
  (Value.live (Level.one) false false), ∅, 3, 2⟩, ⟨Value.live (Level.one) true true, PC.build [0], ∅, 3, 3⟩),
  -- State 81
  (⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.attempt), ∅, 4, 2⟩, ⟨Value.live (Level.one) true true, PC.build [0], ∅, 3, 3⟩),
  -- State 82
  (⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.tickLower 0 false), ∅, 4, 2⟩, ⟨Value.live (Level.one) true true, PC.build [0], ∅, 3, 3⟩),
  -- State 83
  (⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.lowerOwn 0 true), ∅, 4, 2⟩, ⟨Value.live (Level.one) true true, PC.build [0], ∅, 3, 3⟩),
  -- State 84
  (⟨Value.live (Level.one) false false, PC.attempt
  (Phase.one)
  true
  (Algorithm3.PC.tickRead), ∅, 4, 2⟩, ⟨Value.live (Level.one) true true, PC.build [0], ∅, 3, 3⟩),
  -- State 85
  (⟨Value.live (Level.one) false false, PC.tickWrite
  (Phase.one)
  true
  (Value.live (Level.one) false true), ∅, 4, 2⟩, ⟨Value.live (Level.one) true true, PC.build [0], ∅, 3, 3⟩),
  -- State 86
  (⟨Value.live (Level.one) false true, PC.pairDone (Phase.one), ∅, 4, 3⟩, ⟨Value.live (Level.one) true true, PC.build [0], ∅, 3, 3⟩),
  -- State 87
  (⟨Value.live (Level.one) false true, PC.build [1], ∅, 4, 3⟩, ⟨Value.live (Level.one) true true, PC.build [0], ∅, 3, 3⟩),
  -- State 88
  (⟨Value.live (Level.one) false true, PC.build [], ∅, 4, 3⟩, ⟨Value.live (Level.one) true true, PC.build [0], ∅, 3, 3⟩),
  -- State 89
  (⟨Value.live (Level.one) false true, PC.prefixRead (Level.two), ∅, 4, 3⟩, ⟨Value.live (Level.one) true true, PC.build [0], ∅, 3, 3⟩),
  -- State 90
  (⟨Value.live (Level.one) false true, PC.prefixRead (Level.two), ∅, 4, 3⟩, ⟨Value.live (Level.one) true true, PC.build [], ∅, 3, 3⟩),
  -- State 91
  (⟨Value.live (Level.one) false true, PC.prefixRead (Level.two), ∅, 4, 3⟩, ⟨Value.live (Level.one) true true, PC.prefixRead (Level.two), ∅, 3, 3⟩),
  -- State 92
  (⟨Value.live (Level.one) false true, PC.prefixRead (Level.two), ∅, 4, 3⟩, ⟨Value.live (Level.one) true true, PC.prefixWrite
  (Value.live (Level.two) true true), ∅, 3, 3⟩),
  -- State 93
  (⟨Value.live (Level.one) false true, PC.prefixRead (Level.two), ∅, 4, 3⟩, ⟨Value.live (Level.two) true true, PC.delete [0], ∅, 3, 3⟩),
  -- State 94
  (⟨Value.live (Level.one) false true, PC.prefixWrite
  (Value.live (Level.two) false true), ∅, 4, 3⟩, ⟨Value.live (Level.two) true true, PC.delete [0], ∅, 3, 3⟩),
  -- State 95
  (⟨Value.live (Level.two) false true, PC.delete [1], ∅, 4, 3⟩, ⟨Value.live (Level.two) true true, PC.delete [0], ∅, 3, 3⟩),
  -- State 96
  (⟨Value.live (Level.two) false true, PC.delete [], ∅, 4, 3⟩, ⟨Value.live (Level.two) true true, PC.delete [0], ∅, 3, 3⟩),
  -- State 97
  (⟨Value.live (Level.two) false true, PC.add [1], ∅, 4, 3⟩, ⟨Value.live (Level.two) true true, PC.delete [0], ∅, 3, 3⟩),
  -- State 98
  (⟨Value.live (Level.two) false true, PC.add [], ∅, 4, 3⟩, ⟨Value.live (Level.two) true true, PC.delete [0], ∅, 3, 3⟩),
  -- State 99
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) true true, PC.delete [0], ∅, 3, 3⟩),
  -- State 100
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) true true, PC.delete [], ∅, 3, 3⟩),
  -- State 101
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) true true, PC.add [0], ∅, 3, 3⟩),
  -- State 102
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) true true, PC.add [], ∅, 3, 3⟩),
  -- State 103
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) true true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 104
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) true true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.tickLower 0 false), ∅, 3, 3⟩),
  -- State 105
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) true true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.lowerOwn 0 false), ∅, 3, 3⟩),
  -- State 106
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) true true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.tickRead), ∅, 3, 3⟩),
  -- State 107
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) true true, PC.tickWrite
  (Phase.maintain)
  false
  (Value.live (Level.two) false true), ∅, 3, 3⟩),
  -- State 108
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  true
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 109
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  true
  (Algorithm3.PC.tickUpper 1), ∅, 3, 3⟩),
  -- State 110
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  true
  (Algorithm3.PC.upperOwn 1 true), ∅, 3, 3⟩),
  -- State 111
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  true
  (Algorithm3.PC.tickRead), ∅, 3, 3⟩),
  -- State 112
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) false true, PC.tickWrite
  (Phase.maintain)
  true
  (Value.live (Level.two) false false), ∅, 3, 3⟩),
  -- State 113
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) false false, PC.pairDone (Phase.maintain), ∅, 3, 3⟩),
  -- State 114
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) false false, PC.prefixRead (Level.three), ∅, 3, 3⟩),
  -- State 115
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.tickUpper 1), ∅, 4, 3⟩, ⟨Value.live (Level.two) false false, PC.prefixRead (Level.three), ∅, 3, 3⟩),
  -- State 116
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.upperOwn 1 false), ∅, 4, 3⟩, ⟨Value.live (Level.two) false false, PC.prefixRead (Level.three), ∅, 3, 3⟩),
  -- State 117
  (⟨Value.live (Level.two) false true, PC.attempt
  (Phase.maintain)
  false
  (Algorithm3.PC.tickRead), ∅, 4, 3⟩, ⟨Value.live (Level.two) false false, PC.prefixRead (Level.three), ∅, 3, 3⟩),
  -- State 118
  (⟨Value.live (Level.two) false true, PC.tickWrite
  (Phase.maintain)
  false
  (Value.live (Level.two) true true), ∅, 4, 3⟩, ⟨Value.live (Level.two) false false, PC.prefixRead (Level.three), ∅, 3, 3⟩),
  -- State 119
  (⟨Value.live (Level.two) true true, PC.attempt
  (Phase.maintain)
  true
  (Algorithm3.PC.attempt), ∅, 4, 3⟩, ⟨Value.live (Level.two) false false, PC.prefixRead (Level.three), ∅, 3, 3⟩),
  -- State 120
  (⟨Value.live (Level.two) true true, PC.attempt
  (Phase.maintain)
  true
  (Algorithm3.PC.tickLower 0 false), ∅, 4, 3⟩, ⟨Value.live (Level.two) false false, PC.prefixRead (Level.three), ∅, 3, 3⟩),
  -- State 121
  (⟨Value.live (Level.two) true true, PC.attempt
  (Phase.maintain)
  true
  (Algorithm3.PC.lowerOwn 0 false), ∅, 4, 3⟩, ⟨Value.live (Level.two) false false, PC.prefixRead (Level.three), ∅, 3, 3⟩),
  -- State 122
  (⟨Value.live (Level.two) true true, PC.attempt
  (Phase.maintain)
  true
  (Algorithm3.PC.tickRead), ∅, 4, 3⟩, ⟨Value.live (Level.two) false false, PC.prefixRead (Level.three), ∅, 3, 3⟩),
  -- State 123
  (⟨Value.live (Level.two) true true, PC.tickWrite
  (Phase.maintain)
  true
  (Value.live (Level.two) true false), ∅, 4, 3⟩, ⟨Value.live (Level.two) false false, PC.prefixRead (Level.three), ∅, 3, 3⟩),
  -- State 124
  (⟨Value.live (Level.two) true false, PC.pairDone (Phase.maintain), ∅, 4, 3⟩, ⟨Value.live (Level.two) false false, PC.prefixRead (Level.three), ∅, 3, 3⟩),
  -- State 125
  (⟨Value.live (Level.two) true false, PC.prefixRead (Level.three), ∅, 4, 3⟩, ⟨Value.live (Level.two) false false, PC.prefixRead (Level.three), ∅, 3, 3⟩),
  -- State 126
  (⟨Value.live (Level.two) true false, PC.prefixWrite
  (Value.live (Level.three) true false), ∅, 4, 3⟩, ⟨Value.live (Level.two) false false, PC.prefixRead (Level.three), ∅, 3, 3⟩),
  -- State 127
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.live (Level.two) false false, PC.prefixRead (Level.three), ∅, 3, 3⟩),
  -- State 128
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.live (Level.two) false false, PC.prefixWrite
  (Value.live (Level.three) false false), ∅, 3, 3⟩),
  -- State 129
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩),
  -- State 130
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.tickLower 0 false), ∅, 0, 0⟩),
  -- State 131
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.lowerOwn 0 true), ∅, 0, 0⟩),
  -- State 132
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.tickRead), ∅, 0, 0⟩),
  -- State 133
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.live (Level.three) false false, PC.tickWrite
  (Phase.three)
  false
  (Value.live (Level.three) true false), ∅, 0, 0⟩),
  -- State 134
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.attempt), ∅, 1, 0⟩),
  -- State 135
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.tickUpper 1), ∅, 1, 0⟩),
  -- State 136
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.upperOwn 1 false), ∅, 1, 0⟩),
  -- State 137
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.tickRead), ∅, 1, 0⟩),
  -- State 138
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.live (Level.three) true false, PC.tickWrite
  (Phase.three)
  true
  (Value.live (Level.three) true true), ∅, 1, 0⟩),
  -- State 139
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.live (Level.three) true true, PC.pairDone (Phase.three), ∅, 1, 1⟩),
  -- State 140
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 0, 0⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 141
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.tickUpper 1), ∅, 0, 0⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 142
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.upperOwn 1 true), ∅, 0, 0⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 143
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.tickRead), ∅, 0, 0⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 144
  (⟨Value.live (Level.three) true false, PC.tickWrite
  (Phase.three)
  false
  (Value.live (Level.three) false false), ∅, 0, 0⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 145
  (⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.attempt), ∅, 1, 0⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 146
  (⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.tickLower 0 false), ∅, 1, 0⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 147
  (⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.lowerOwn 0 true), ∅, 1, 0⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 148
  (⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.tickRead), ∅, 1, 0⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 149
  (⟨Value.live (Level.three) false false, PC.tickWrite
  (Phase.three)
  true
  (Value.live (Level.three) false true), ∅, 1, 0⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 150
  (⟨Value.live (Level.three) false true, PC.pairDone (Phase.three), ∅, 1, 1⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 151
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩),
  -- State 152
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.tickLower 0 false), ∅, 1, 1⟩),
  -- State 153
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.lowerOwn 0 false), ∅, 1, 1⟩),
  -- State 154
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.tickRead), ∅, 1, 1⟩),
  -- State 155
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩, ⟨Value.live (Level.three) true true, PC.tickWrite
  (Phase.three)
  false
  (Value.live (Level.three) false true), ∅, 1, 1⟩),
  -- State 156
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩, ⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.attempt), ∅, 2, 1⟩),
  -- State 157
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩, ⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.tickUpper 1), ∅, 2, 1⟩),
  -- State 158
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩, ⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.upperOwn 1 true), ∅, 2, 1⟩),
  -- State 159
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩, ⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.tickRead), ∅, 2, 1⟩),
  -- State 160
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩, ⟨Value.live (Level.three) false true, PC.tickWrite
  (Phase.three)
  true
  (Value.live (Level.three) false false), ∅, 2, 1⟩),
  -- State 161
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩, ⟨Value.live (Level.three) false false, PC.pairDone (Phase.three), ∅, 2, 2⟩),
  -- State 162
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 1, 1⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 163
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.tickUpper 1), ∅, 1, 1⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 164
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.upperOwn 1 false), ∅, 1, 1⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 165
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.tickRead), ∅, 1, 1⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 166
  (⟨Value.live (Level.three) false true, PC.tickWrite
  (Phase.three)
  false
  (Value.live (Level.three) true true), ∅, 1, 1⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 167
  (⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.attempt), ∅, 2, 1⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 168
  (⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.tickLower 0 false), ∅, 2, 1⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 169
  (⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.lowerOwn 0 false), ∅, 2, 1⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 170
  (⟨Value.live (Level.three) true true, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.tickRead), ∅, 2, 1⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 171
  (⟨Value.live (Level.three) true true, PC.tickWrite
  (Phase.three)
  true
  (Value.live (Level.three) true false), ∅, 2, 1⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 172
  (⟨Value.live (Level.three) true false, PC.pairDone (Phase.three), ∅, 2, 2⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 173
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩),
  -- State 174
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.tickLower 0 false), ∅, 2, 2⟩),
  -- State 175
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.lowerOwn 0 true), ∅, 2, 2⟩),
  -- State 176
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩, ⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.tickRead), ∅, 2, 2⟩),
  -- State 177
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩, ⟨Value.live (Level.three) false false, PC.tickWrite
  (Phase.three)
  false
  (Value.live (Level.three) true false), ∅, 2, 2⟩),
  -- State 178
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩, ⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.attempt), ∅, 3, 2⟩),
  -- State 179
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩, ⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.tickUpper 1), ∅, 3, 2⟩),
  -- State 180
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩, ⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.upperOwn 1 false), ∅, 3, 2⟩),
  -- State 181
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩, ⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.tickRead), ∅, 3, 2⟩),
  -- State 182
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩, ⟨Value.live (Level.three) true false, PC.tickWrite
  (Phase.three)
  true
  (Value.live (Level.three) true true), ∅, 3, 2⟩),
  -- State 183
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩, ⟨Value.live (Level.three) true true, PC.pairDone (Phase.three), ∅, 3, 3⟩),
  -- State 184
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.attempt), ∅, 2, 2⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 185
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.tickUpper 1), ∅, 2, 2⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 186
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.upperOwn 1 true), ∅, 2, 2⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 187
  (⟨Value.live (Level.three) true false, PC.attempt
  (Phase.three)
  false
  (Algorithm3.PC.tickRead), ∅, 2, 2⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 188
  (⟨Value.live (Level.three) true false, PC.tickWrite
  (Phase.three)
  false
  (Value.live (Level.three) false false), ∅, 2, 2⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 189
  (⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.attempt), ∅, 3, 2⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 190
  (⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.tickLower 0 false), ∅, 3, 2⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 191
  (⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.lowerOwn 0 true), ∅, 3, 2⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 192
  (⟨Value.live (Level.three) false false, PC.attempt
  (Phase.three)
  true
  (Algorithm3.PC.tickRead), ∅, 3, 2⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 193
  (⟨Value.live (Level.three) false false, PC.tickWrite
  (Phase.three)
  true
  (Value.live (Level.three) false true), ∅, 3, 2⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 194
  (⟨Value.live (Level.three) false true, PC.pairDone (Phase.three), ∅, 3, 3⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 195
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 196
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.tickUpper 1), ∅, 3, 3⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 197
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.upperOwn 1 true), ∅, 3, 3⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 198
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.eligible)
  true
  (Algorithm3.PC.attempt), ∅, 3, 3⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 199
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.eligible)
  true
  (Algorithm3.PC.tickLower 0 false), ∅, 3, 3⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 200
  (⟨Value.live (Level.three) false true, PC.attempt
  (Phase.eligible)
  true
  (Algorithm3.PC.lowerOwn 0 true), ∅, 3, 3⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 201
  (⟨Value.live (Level.three) false true, PC.pairDone (Phase.eligible), ∅, 3, 3⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 202
  (⟨Value.live (Level.three) false true, PC.eligible [1], ∅, 3, 3⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 203
  (⟨Value.live (Level.three) false true, PC.eligible [], ∅, 3, 3⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 204
  (⟨Value.live (Level.three) false true, PC.publish, ∅, 3, 3⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 205
  (⟨Value.cs, PC.enter, ∅, 3, 3⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 206
  (⟨Value.cs, PC.cs, ∅, 3, 3⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 207
  (⟨Value.cs, PC.release, ∅, 3, 3⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 208
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 209
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.tickLower 0 false), ∅, 3, 3⟩),
  -- State 210
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.live (Level.three) true true, PC.attempt
  (Phase.eligible)
  false
  (Algorithm3.PC.tickRead), ∅, 3, 3⟩),
  -- State 211
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.live (Level.three) true true, PC.tickWrite
  (Phase.eligible)
  false
  (Value.live (Level.three) false true), ∅, 3, 3⟩),
  -- State 212
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.live (Level.three) false true, PC.attempt
  (Phase.eligible)
  true
  (Algorithm3.PC.attempt), ∅, 3, 3⟩),
  -- State 213
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.live (Level.three) false true, PC.attempt
  (Phase.eligible)
  true
  (Algorithm3.PC.tickUpper 1), ∅, 3, 3⟩),
  -- State 214
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.live (Level.three) false true, PC.attempt
  (Phase.eligible)
  true
  (Algorithm3.PC.tickRead), ∅, 3, 3⟩),
  -- State 215
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.live (Level.three) false true, PC.tickWrite
  (Phase.eligible)
  true
  (Value.live (Level.three) false false), ∅, 3, 3⟩),
  -- State 216
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.live (Level.three) false false, PC.pairDone (Phase.eligible), ∅, 3, 3⟩),
  -- State 217
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.live (Level.three) false false, PC.eligible [0], ∅, 3, 3⟩),
  -- State 218
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.live (Level.three) false false, PC.eligible [], ∅, 3, 3⟩),
  -- State 219
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.live (Level.three) false false, PC.publish, ∅, 3, 3⟩),
  -- State 220
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.cs, PC.enter, ∅, 3, 3⟩),
  -- State 221
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.cs, PC.cs, ∅, 3, 3⟩),
  -- State 222
  (⟨Value.dead, PC.idle, ∅, 0, 0⟩, ⟨Value.cs, PC.release, ∅, 3, 3⟩)
]
end EconomicalSolutions.Algorithm7.Counterexample
