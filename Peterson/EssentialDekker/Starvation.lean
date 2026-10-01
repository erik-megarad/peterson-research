import Peterson.EssentialDekker.Corrected
import Mathlib.Data.Fin.VecNotation

/-! Concrete states are a generated certificate, checked against `next` below.
No correctness claim relies on the generating Python program. -/
namespace Peterson.EssentialDekker.Corrected.Starvation
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

-- BEGIN GENERATED CERTIFICATE
def stemState (i : Fin 96) : State 1 :=
  match i.val with
  | 0 => { flag := ![0, 0, 0], turn := ![0, 0], pc := ![.idle, .idle, .idle] }
  | 1 => { flag := ![0, 0, 0], turn := ![0, 0], pc := ![.writeTurn 0, .idle, .idle] }
  | 2 => { flag := ![0, 0, 0], turn := ![0, 0], pc := ![.readTurn 0, .idle, .idle] }
  | 3 => { flag := ![0, 0, 0], turn := ![0, 0], pc := ![.scan 0 false 0 0, .idle, .idle] }
  | 4 => { flag := ![0, 0, 0], turn := ![0, 0], pc := ![.scan 0 false 1 0, .idle, .idle] }
  | 5 => { flag := ![0, 0, 0], turn := ![0, 0], pc := ![.writeFlag 0 true, .idle, .idle] }
  | 6 => { flag := ![1, 0, 0], turn := ![0, 0], pc := ![.guardSelf 0, .idle, .idle] }
  | 7 => { flag := ![1, 0, 0], turn := ![0, 0], pc := ![.guardSelf 0, .writeTurn 0, .idle] }
  | 8 => { flag := ![1, 0, 0], turn := ![1, 0], pc := ![.guardSelf 0, .readTurn 0, .idle] }
  | 9 => { flag := ![1, 0, 0], turn := ![1, 0], pc := ![.guardSelf 0, .scan 0 false 0 0, .idle] }
  | 10 => { flag := ![1, 0, 0], turn := ![1, 0], pc := ![.guardSelf 0, .scan 0 false 1 1, .idle] }
  | 11 => { flag := ![1, 0, 0], turn := ![1, 0], pc := ![.guardSelf 0, .writeFlag 0 true, .idle] }
  | 12 => { flag := ![1, 1, 0], turn := ![1, 0], pc := ![.guardSelf 0, .guardSelf 0, .idle] }
  | 13 => { flag := ![1, 1, 0], turn := ![1, 0], pc := ![.guardSelf 0, .scan 0 true 0 0, .idle] }
  | 14 => { flag := ![1, 1, 0], turn := ![1, 0], pc := ![.guardSelf 0, .scan 0 true 1 1, .idle] }
  | 15 => { flag := ![1, 1, 0], turn := ![1, 0], pc := ![.guardSelf 0, .writeTurn 1, .idle] }
  | 16 => { flag := ![1, 1, 0], turn := ![1, 1], pc := ![.guardSelf 0, .readTurn 1, .idle] }
  | 17 => { flag := ![1, 1, 0], turn := ![1, 1], pc := ![.guardSelf 0, .scan 1 false 0 0, .idle] }
  | 18 => { flag := ![1, 1, 0], turn := ![1, 1], pc := ![.guardSelf 0, .scan 1 false 1 0, .idle] }
  | 19 => { flag := ![1, 1, 0], turn := ![1, 1], pc := ![.guardSelf 0, .writeFlag 1 true, .idle] }
  | 20 => { flag := ![1, 2, 0], turn := ![1, 1], pc := ![.guardSelf 0, .guardSelf 1, .idle] }
  | 21 => { flag := ![1, 2, 0], turn := ![1, 1], pc := ![.guardSelf 0, .scan 1 true 0 0, .idle] }
  | 22 => { flag := ![1, 2, 0], turn := ![1, 1], pc := ![.guardSelf 0, .scan 1 true 1 0, .idle] }
  | 23 => { flag := ![1, 2, 0], turn := ![1, 1], pc := ![.guardSelf 0, .critical, .idle] }
  | 24 => { flag := ![1, 2, 0], turn := ![1, 1], pc := ![.guardSelf 0, .critical, .writeTurn 0] }
  | 25 => { flag := ![1, 2, 0], turn := ![2, 1], pc := ![.guardSelf 0, .critical, .readTurn 0] }
  | 26 => { flag := ![1, 2, 0], turn := ![2, 1], pc := ![.guardSelf 0, .exit, .readTurn 0] }
  | 27 => { flag := ![1, 0, 0], turn := ![2, 1], pc := ![.guardSelf 0, .idle, .readTurn 0] }
  | 28 => { flag := ![1, 0, 0], turn := ![2, 1], pc := ![.guardSelf 0, .writeTurn 0, .readTurn 0] }
  | 29 => { flag := ![1, 0, 0], turn := ![1, 1], pc := ![.guardSelf 0, .readTurn 0, .readTurn 0] }
  | 30 => { flag := ![1, 0, 0], turn := ![1, 1], pc := ![.guardSelf 0, .scan 0 false 0 0, .readTurn 0] }
  | 31 => { flag := ![1, 0, 0], turn := ![1, 1], pc := ![.guardSelf 0, .scan 0 false 1 1, .readTurn 0] }
  | 32 => { flag := ![1, 0, 0], turn := ![1, 1], pc := ![.guardSelf 0, .writeFlag 0 true, .readTurn 0] }
  | 33 => { flag := ![1, 1, 0], turn := ![1, 1], pc := ![.guardSelf 0, .guardSelf 0, .readTurn 0] }
  | 34 => { flag := ![1, 1, 0], turn := ![1, 1], pc := ![.guardSelf 0, .guardSelf 0, .writeFlag 0 true] }
  | 35 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.guardSelf 0, .guardSelf 0, .guardSelf 0] }
  | 36 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.scan 0 true 0 0, .guardSelf 0, .guardSelf 0] }
  | 37 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.scan 0 true 1 1, .guardSelf 0, .guardSelf 0] }
  | 38 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .guardSelf 0, .guardSelf 0] }
  | 39 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.writeFlag 0 true, .guardSelf 0, .guardSelf 0] }
  | 40 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.guardSelf 0, .guardSelf 0, .guardSelf 0] }
  | 41 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.scan 0 true 0 0, .guardSelf 0, .guardSelf 0] }
  | 42 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.scan 0 true 1 1, .guardSelf 0, .guardSelf 0] }
  | 43 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .guardSelf 0, .guardSelf 0] }
  | 44 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .scan 0 true 0 0, .guardSelf 0] }
  | 45 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .scan 0 true 1 1, .guardSelf 0] }
  | 46 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .readTurn 0, .guardSelf 0] }
  | 47 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .scan 0 false 0 0, .guardSelf 0] }
  | 48 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .scan 0 false 1 1, .guardSelf 0] }
  | 49 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .writeFlag 0 false, .guardSelf 0] }
  | 50 => { flag := ![1, 0, 1], turn := ![1, 1], pc := ![.readTurn 0, .guardSelf 0, .guardSelf 0] }
  | 51 => { flag := ![1, 0, 1], turn := ![1, 1], pc := ![.readTurn 0, .readTurn 0, .guardSelf 0] }
  | 52 => { flag := ![1, 0, 1], turn := ![1, 1], pc := ![.readTurn 0, .readTurn 0, .scan 0 true 0 0] }
  | 53 => { flag := ![1, 0, 1], turn := ![1, 1], pc := ![.readTurn 0, .readTurn 0, .scan 0 true 1 1] }
  | 54 => { flag := ![1, 0, 1], turn := ![1, 1], pc := ![.readTurn 0, .readTurn 0, .writeTurn 1] }
  | 55 => { flag := ![1, 0, 1], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .readTurn 1] }
  | 56 => { flag := ![1, 0, 1], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .scan 1 false 0 0] }
  | 57 => { flag := ![1, 0, 1], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .scan 1 false 1 0] }
  | 58 => { flag := ![1, 0, 1], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .writeFlag 1 true] }
  | 59 => { flag := ![1, 0, 2], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .guardSelf 1] }
  | 60 => { flag := ![1, 0, 2], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .scan 1 true 0 0] }
  | 61 => { flag := ![1, 0, 2], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .scan 1 true 1 0] }
  | 62 => { flag := ![1, 0, 2], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .critical] }
  | 63 => { flag := ![1, 0, 2], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .exit] }
  | 64 => { flag := ![1, 0, 0], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .idle] }
  | 65 => { flag := ![1, 0, 0], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .writeTurn 0] }
  | 66 => { flag := ![1, 0, 0], turn := ![2, 2], pc := ![.readTurn 0, .readTurn 0, .readTurn 0] }
  | 67 => { flag := ![1, 0, 0], turn := ![2, 2], pc := ![.readTurn 0, .readTurn 0, .scan 0 false 0 0] }
  | 68 => { flag := ![1, 0, 0], turn := ![2, 2], pc := ![.readTurn 0, .readTurn 0, .scan 0 false 1 1] }
  | 69 => { flag := ![1, 0, 0], turn := ![2, 2], pc := ![.readTurn 0, .readTurn 0, .writeFlag 0 true] }
  | 70 => { flag := ![1, 0, 1], turn := ![2, 2], pc := ![.readTurn 0, .readTurn 0, .guardSelf 0] }
  | 71 => { flag := ![1, 0, 1], turn := ![2, 2], pc := ![.readTurn 0, .writeFlag 0 true, .guardSelf 0] }
  | 72 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .guardSelf 0] }
  | 73 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.writeFlag 0 true, .guardSelf 0, .guardSelf 0] }
  | 74 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.guardSelf 0, .guardSelf 0, .guardSelf 0] }
  | 75 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.scan 0 true 0 0, .guardSelf 0, .guardSelf 0] }
  | 76 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.scan 0 true 1 1, .guardSelf 0, .guardSelf 0] }
  | 77 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .guardSelf 0] }
  | 78 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .scan 0 true 0 0] }
  | 79 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .scan 0 true 1 1] }
  | 80 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .readTurn 0] }
  | 81 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .scan 0 false 0 0] }
  | 82 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .scan 0 false 1 1] }
  | 83 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .writeFlag 0 false] }
  | 84 => { flag := ![1, 1, 0], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .guardSelf 0] }
  | 85 => { flag := ![1, 1, 0], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .readTurn 0] }
  | 86 => { flag := ![1, 1, 0], turn := ![2, 2], pc := ![.readTurn 0, .scan 0 true 0 0, .readTurn 0] }
  | 87 => { flag := ![1, 1, 0], turn := ![2, 2], pc := ![.readTurn 0, .scan 0 true 1 1, .readTurn 0] }
  | 88 => { flag := ![1, 1, 0], turn := ![2, 2], pc := ![.readTurn 0, .writeTurn 1, .readTurn 0] }
  | 89 => { flag := ![1, 1, 0], turn := ![2, 1], pc := ![.readTurn 0, .readTurn 1, .readTurn 0] }
  | 90 => { flag := ![1, 1, 0], turn := ![2, 1], pc := ![.readTurn 0, .scan 1 false 0 0, .readTurn 0] }
  | 91 => { flag := ![1, 1, 0], turn := ![2, 1], pc := ![.readTurn 0, .scan 1 false 1 0, .readTurn 0] }
  | 92 => { flag := ![1, 1, 0], turn := ![2, 1], pc := ![.readTurn 0, .writeFlag 1 true, .readTurn 0] }
  | 93 => { flag := ![1, 2, 0], turn := ![2, 1], pc := ![.readTurn 0, .guardSelf 1, .readTurn 0] }
  | 94 => { flag := ![1, 2, 0], turn := ![2, 1], pc := ![.readTurn 0, .scan 1 true 0 0, .readTurn 0] }
  | _ => { flag := ![1, 2, 0], turn := ![2, 1], pc := ![.readTurn 0, .scan 1 true 1 0, .readTurn 0] }

def phase (i : Fin 68) : State 1 :=
  match i.val with
  | 0 => { flag := ![1, 2, 0], turn := ![2, 1], pc := ![.readTurn 0, .critical, .readTurn 0] }
  | 1 => { flag := ![1, 2, 0], turn := ![2, 1], pc := ![.readTurn 0, .exit, .readTurn 0] }
  | 2 => { flag := ![1, 0, 0], turn := ![2, 1], pc := ![.readTurn 0, .idle, .readTurn 0] }
  | 3 => { flag := ![1, 0, 0], turn := ![2, 1], pc := ![.readTurn 0, .writeTurn 0, .readTurn 0] }
  | 4 => { flag := ![1, 0, 0], turn := ![1, 1], pc := ![.readTurn 0, .readTurn 0, .readTurn 0] }
  | 5 => { flag := ![1, 0, 0], turn := ![1, 1], pc := ![.readTurn 0, .scan 0 false 0 0, .readTurn 0] }
  | 6 => { flag := ![1, 0, 0], turn := ![1, 1], pc := ![.readTurn 0, .scan 0 false 1 1, .readTurn 0] }
  | 7 => { flag := ![1, 0, 0], turn := ![1, 1], pc := ![.readTurn 0, .writeFlag 0 true, .readTurn 0] }
  | 8 => { flag := ![1, 1, 0], turn := ![1, 1], pc := ![.readTurn 0, .guardSelf 0, .readTurn 0] }
  | 9 => { flag := ![1, 1, 0], turn := ![1, 1], pc := ![.readTurn 0, .guardSelf 0, .writeFlag 0 true] }
  | 10 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .guardSelf 0, .guardSelf 0] }
  | 11 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.writeFlag 0 true, .guardSelf 0, .guardSelf 0] }
  | 12 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.guardSelf 0, .guardSelf 0, .guardSelf 0] }
  | 13 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.scan 0 true 0 0, .guardSelf 0, .guardSelf 0] }
  | 14 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.scan 0 true 1 1, .guardSelf 0, .guardSelf 0] }
  | 15 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .guardSelf 0, .guardSelf 0] }
  | 16 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .scan 0 true 0 0, .guardSelf 0] }
  | 17 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .scan 0 true 1 1, .guardSelf 0] }
  | 18 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .readTurn 0, .guardSelf 0] }
  | 19 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .scan 0 false 0 0, .guardSelf 0] }
  | 20 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .scan 0 false 1 1, .guardSelf 0] }
  | 21 => { flag := ![1, 1, 1], turn := ![1, 1], pc := ![.readTurn 0, .writeFlag 0 false, .guardSelf 0] }
  | 22 => { flag := ![1, 0, 1], turn := ![1, 1], pc := ![.readTurn 0, .guardSelf 0, .guardSelf 0] }
  | 23 => { flag := ![1, 0, 1], turn := ![1, 1], pc := ![.readTurn 0, .readTurn 0, .guardSelf 0] }
  | 24 => { flag := ![1, 0, 1], turn := ![1, 1], pc := ![.readTurn 0, .readTurn 0, .scan 0 true 0 0] }
  | 25 => { flag := ![1, 0, 1], turn := ![1, 1], pc := ![.readTurn 0, .readTurn 0, .scan 0 true 1 1] }
  | 26 => { flag := ![1, 0, 1], turn := ![1, 1], pc := ![.readTurn 0, .readTurn 0, .writeTurn 1] }
  | 27 => { flag := ![1, 0, 1], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .readTurn 1] }
  | 28 => { flag := ![1, 0, 1], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .scan 1 false 0 0] }
  | 29 => { flag := ![1, 0, 1], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .scan 1 false 1 0] }
  | 30 => { flag := ![1, 0, 1], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .writeFlag 1 true] }
  | 31 => { flag := ![1, 0, 2], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .guardSelf 1] }
  | 32 => { flag := ![1, 0, 2], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .scan 1 true 0 0] }
  | 33 => { flag := ![1, 0, 2], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .scan 1 true 1 0] }
  | 34 => { flag := ![1, 0, 2], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .critical] }
  | 35 => { flag := ![1, 0, 2], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .exit] }
  | 36 => { flag := ![1, 0, 0], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .idle] }
  | 37 => { flag := ![1, 0, 0], turn := ![1, 2], pc := ![.readTurn 0, .readTurn 0, .writeTurn 0] }
  | 38 => { flag := ![1, 0, 0], turn := ![2, 2], pc := ![.readTurn 0, .readTurn 0, .readTurn 0] }
  | 39 => { flag := ![1, 0, 0], turn := ![2, 2], pc := ![.readTurn 0, .readTurn 0, .scan 0 false 0 0] }
  | 40 => { flag := ![1, 0, 0], turn := ![2, 2], pc := ![.readTurn 0, .readTurn 0, .scan 0 false 1 1] }
  | 41 => { flag := ![1, 0, 0], turn := ![2, 2], pc := ![.readTurn 0, .readTurn 0, .writeFlag 0 true] }
  | 42 => { flag := ![1, 0, 1], turn := ![2, 2], pc := ![.readTurn 0, .readTurn 0, .guardSelf 0] }
  | 43 => { flag := ![1, 0, 1], turn := ![2, 2], pc := ![.readTurn 0, .writeFlag 0 true, .guardSelf 0] }
  | 44 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .guardSelf 0] }
  | 45 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.writeFlag 0 true, .guardSelf 0, .guardSelf 0] }
  | 46 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.guardSelf 0, .guardSelf 0, .guardSelf 0] }
  | 47 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.scan 0 true 0 0, .guardSelf 0, .guardSelf 0] }
  | 48 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.scan 0 true 1 1, .guardSelf 0, .guardSelf 0] }
  | 49 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .guardSelf 0] }
  | 50 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .scan 0 true 0 0] }
  | 51 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .scan 0 true 1 1] }
  | 52 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .readTurn 0] }
  | 53 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .scan 0 false 0 0] }
  | 54 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .scan 0 false 1 1] }
  | 55 => { flag := ![1, 1, 1], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .writeFlag 0 false] }
  | 56 => { flag := ![1, 1, 0], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .guardSelf 0] }
  | 57 => { flag := ![1, 1, 0], turn := ![2, 2], pc := ![.readTurn 0, .guardSelf 0, .readTurn 0] }
  | 58 => { flag := ![1, 1, 0], turn := ![2, 2], pc := ![.readTurn 0, .scan 0 true 0 0, .readTurn 0] }
  | 59 => { flag := ![1, 1, 0], turn := ![2, 2], pc := ![.readTurn 0, .scan 0 true 1 1, .readTurn 0] }
  | 60 => { flag := ![1, 1, 0], turn := ![2, 2], pc := ![.readTurn 0, .writeTurn 1, .readTurn 0] }
  | 61 => { flag := ![1, 1, 0], turn := ![2, 1], pc := ![.readTurn 0, .readTurn 1, .readTurn 0] }
  | 62 => { flag := ![1, 1, 0], turn := ![2, 1], pc := ![.readTurn 0, .scan 1 false 0 0, .readTurn 0] }
  | 63 => { flag := ![1, 1, 0], turn := ![2, 1], pc := ![.readTurn 0, .scan 1 false 1 0, .readTurn 0] }
  | 64 => { flag := ![1, 1, 0], turn := ![2, 1], pc := ![.readTurn 0, .writeFlag 1 true, .readTurn 0] }
  | 65 => { flag := ![1, 2, 0], turn := ![2, 1], pc := ![.readTurn 0, .guardSelf 1, .readTurn 0] }
  | 66 => { flag := ![1, 2, 0], turn := ![2, 1], pc := ![.readTurn 0, .scan 1 true 0 0, .readTurn 0] }
  | _ => { flag := ![1, 2, 0], turn := ![2, 1], pc := ![.readTurn 0, .scan 1 true 1 0, .readTurn 0] }

def stemActors : List (Proc 1) := [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def cycle : List (Proc 1) := [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
-- END GENERATED CERTIFICATE

def actor (i : Fin 68) : Proc 1 := cycle[i.val]'(by simpa only [show cycle.length = 68 from by decide] using i.isLt)
def stemActor (i : Fin 96) : Proc 1 := stemActors[i.val]'(by simpa only [show stemActors.length = 96 from by decide] using i.isLt)

def Same (s t : State 1) : Prop :=
  (∀ p, s.flag p = t.flag p) ∧ (∀ j, s.turn j = t.turn j) ∧ (∀ p, s.pc p = t.pc p)
instance (s t : State 1) : Decidable (Same s t) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
theorem same_eq {s t : State 1} (h : Same s t) : s = t := by
  have hf := funext h.1
  have ht := funext h.2.1
  have hp := funext h.2.2
  cases s; cases t
  cases hf; cases ht; cases hp
  rfl

theorem stem_initial : stemState 0 = initial 1 := same_eq (by decide)

theorem stem_step (i : Fin 96) :
    next (stemState i) (stemActor i) =
      if h : i.val + 1 < 96 then stemState ⟨i.val + 1, h⟩ else phase 0 := by
  apply same_eq
  have h : ∀ i : Fin 96, Same (next (stemState i) (stemActor i))
      (if h : i.val + 1 < 96 then stemState ⟨i.val + 1, h⟩ else phase 0) := by decide
  exact h i

theorem phase_step (i : Fin 68) :
    next (phase i) (actor i) = phase ⟨(i.val + 1) % 68, Nat.mod_lt _ (by decide)⟩ := by
  apply same_eq
  have h : ∀ i : Fin 68, Same (next (phase i) (actor i))
      (phase ⟨(i.val + 1) % 68, Nat.mod_lt _ (by decide)⟩) := by decide
  exact h i

theorem phase_pending (i : Fin 68) :
    (phase i).pc 0 ≠ .idle ∧ (phase i).pc 0 ≠ .critical ∧ (phase i).pc 0 ≠ .exit := by
  revert i
  decide

theorem actors_present : ∀ p : Proc 1, ∃ i : Fin 68, actor i = p := by decide

/-- Infinite execution: the finite stem followed by the cycle forever. -/
def state (t : Nat) : State 1 :=
  if h : t < 96 then stemState ⟨t, h⟩ else phase ⟨(t - 96) % 68, Nat.mod_lt _ (by decide)⟩
def event (t : Nat) : Proc 1 :=
  if h : t < 96 then stemActor ⟨t, h⟩ else actor ⟨(t - 96) % 68, Nat.mod_lt _ (by decide)⟩

@[simp] theorem state_after (k : Nat) : state (96 + k) = phase ⟨k % 68, Nat.mod_lt _ (by decide)⟩ := by
  simp [state]
@[simp] theorem event_after (k : Nat) : event (96 + k) = actor ⟨k % 68, Nat.mod_lt _ (by decide)⟩ := by
  simp [event]

theorem execution_initial : state 0 = initial 1 := stem_initial

theorem execution_step (t : Nat) : state (t + 1) = next (state t) (event t) := by
  by_cases h : t < 96
  · have ht := stem_step ⟨t, h⟩
    by_cases hn : t + 1 < 96
    · simpa [state, event, h, hn] using ht.symm
    · have he : t = 95 := by omega
      subst t
      simpa [state, event] using ht.symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 96 ≤ t)
    rw [Nat.add_assoc, state_after, state_after, event_after, phase_step]
    congr 1
    apply Fin.ext
    simp [Nat.add_mod]

/-- Stronger than needed: each actor is selected arbitrarily far in the future. -/
theorem every_actor_runs (p : Proc 1) (t : Nat) : ∃ u, t ≤ u ∧ event u = p := by
  obtain ⟨i, hi⟩ := actors_present p
  refine ⟨96 + (68 * t + i.val), by omega, ?_⟩
  rw [event_after]
  convert hi using 1
  congr 1
  apply Fin.ext
  simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

/-- The first actor never enters, including the stem before the periodic tail. -/
theorem stem_no_entry (i : Fin 96) : (stemState i).pc 0 ≠ .critical := by
  revert i
  decide

theorem never_enters (t : Nat) : (state t).pc 0 ≠ .critical := by
  by_cases h : t < 96
  · simpa [state, h] using stem_no_entry ⟨t, h⟩ 
  · simpa [state, h] using (phase_pending ⟨(t - 96) % 68, Nat.mod_lt _ (by decide)⟩).2.1

theorem completion_certificate : ∀ i : Fin 164, ∀ p : Proc 1,
    (state i.val).pc p = .critical → ∃ d : Fin 68,
      (state (i.val + d.val)).pc p = .critical ∧ event (i.val + d.val) = p := by decide

theorem state_offset (k d : Nat) : state (96 + k % 68 + d) = state (96 + k + d) := by
  simp only [Nat.add_assoc, state_after]
  congr 1
  apply Fin.ext
  simp [Nat.add_mod]
theorem event_offset (k d : Nat) : event (96 + k % 68 + d) = event (96 + k + d) := by
  simp only [Nat.add_assoc, event_after]
  congr 1
  apply Fin.ext
  simp [Nat.add_mod]

/-- Every critical occupant is selected for its completion action later. -/
theorem critical_completes (p : Proc 1) (t : Nat) (h : (state t).pc p = .critical) :
    ∃ u, t ≤ u ∧ (state u).pc p = .critical ∧ event u = p := by
  by_cases ht : t < 164
  · obtain ⟨d, hd⟩ := completion_certificate ⟨t, ht⟩ p h
    exact ⟨t + d.val, by omega, hd⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 96 ≤ t)
    have hk : 96 + k % 68 < 164 := by have := Nat.mod_lt k (by decide : 0 < 68); omega
    have he := state_offset k 0
    simp only [Nat.add_zero] at he
    obtain ⟨d, hd⟩ := completion_certificate ⟨96 + k % 68, hk⟩ p (by simpa [he] using h)
    exact ⟨96 + k + d.val, by omega, by simpa only [state_offset, event_offset] using hd⟩

/-- The starving request occurs at event zero, from the initialized idle state. -/
theorem request_zero : (state 0).pc 0 = .idle ∧ event 0 = 0 ∧
    (state 1).pc 0 = .writeTurn 0 := by decide

def WeakProtocolFair (s : Nat → State 1) (a : Nat → Proc 1) : Prop :=
  ∀ p t, (∀ u, t ≤ u → (s u).pc p ≠ .idle ∧ (s u).pc p ≠ .critical) →
    ∃ u, t ≤ u ∧ a u = p

theorem protocol_fair : WeakProtocolFair state event := by
  intro p t _
  exact every_actor_runs p t

/-- Counterexample to the proposed progress assertion for this reviewed model.
The witness starts at the prescribed initial state; every selected action is
an actual step; it satisfies protocol fairness and critical completion; actor
zero requests at zero and never reaches its critical section. -/
theorem corrected_progress_counterexample :
    state 0 = initial 1 ∧
    (∀ t, state (t + 1) = next (state t) (event t)) ∧
    WeakProtocolFair state event ∧
    (∀ p t, (state t).pc p = .critical →
      ∃ u, t ≤ u ∧ (state u).pc p = .critical ∧ event u = p) ∧
    ((state 0).pc 0 = .idle ∧ event 0 = 0 ∧ (state 1).pc 0 = .writeTurn 0) ∧
    (∀ t, (state t).pc 0 ≠ .critical) :=
  ⟨execution_initial, execution_step, protocol_fair, critical_completes, request_zero, never_enters⟩

#print axioms corrected_progress_counterexample

end Peterson.EssentialDekker.Corrected.Starvation
