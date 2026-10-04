import Cslib.Foundations.Semantics.LTS.Basic

/-! Figure 1 as typed primitive requests and local continuations.
`Sample` fields other than `value` are ghost history; no guard inspects them. -/
namespace MultiReaderAtomic

abbrev Token := Fin 3
inductive Process (n : Nat) where
  | writer
  | reader (j : Fin n)
  deriving DecidableEq
inductive Register (n : Nat) where
  | buff1 | buff2 | level
  | wc (j : Fin n) | rc (j : Fin n) | fc (j : Fin n)
  deriving DecidableEq

abbrev Value (α : Type) : Register n → Type
  | .buff1 | .buff2 => α
  | .level | .wc _ | .rc _ | .fc _ => Token

def initialValue (v₀ : α) : (r : Register n) → Value α r
  | .buff1 | .buff2 => v₀
  | .level | .wc _ => 0
  | .rc _ | .fc _ => 1

def registerOwner : Register n → Process n
  | .rc j | .fc j => .reader j
  | _ => .writer

structure Sample (α : Type) where
  value : α
  witness : Option Nat
  source : Nat
  deriving DecidableEq

inductive Program (n : Nat) (α : Type) where
  | done (result : Option (Sample α))
  | read (r : Register n) (next : Sample (Value α r) → Program n α)
  | write (r : Register n) (value : Value α r) (next : Program n α)
  | order (next : Bool → Program n α)
  | token (a b : Token) (next : Token → Program n α)

/-- A pair of operands permits either sequential evaluation order. -/
def pair (a b : Register n)
    (next : Sample (Value α a) → Sample (Value α b) → Program n α) : Program n α :=
  .order fun leftFirst => if leftFirst then
    .read a fun x => .read b fun y => next x y
  else .read b fun y => .read a fun x => next x y

def writerTail (v : α) : Program n α :=
  .write .level 1 (.write .buff1 v (.write .level 2
    (.write .buff2 v (.write .level 0 (.done none)))))

def writerLoop (v : α) : List (Fin n) → Program n α
  | [] => writerTail v
  | j :: js => pair (.rc j) (.fc j) fun a b =>
      .token a.value b.value fun t => .write (.wc j) t (writerLoop v js)

def writerProgram (v : α) : Program n α := writerLoop v (List.finRange n)

/-- Return-value selection precedes, but does not bypass, forwarding. -/
def readerFinish (j : Fin n) (saved : Sample α) (forwarded : Bool)
    (level rc wc : Token) : Program n α :=
  if rc ≠ wc ∨ (level = 1 ∧ forwarded = false) then
    .read .buff2 fun v => .done (some v)
  else if level ≠ 0 then
    .read (.rc j) fun t => .write (.fc j) t.value (.done (some saved))
  else .done (some saved)

def readerScan (j : Fin n) (saved : Sample α) (forwarded : Bool) :
    List (Fin n) → Program n α
  | [] => .read .level fun level => pair (.rc j) (.wc j) fun rc wc =>
      readerFinish j saved forwarded level.value rc.value wc.value
  | i :: rest => pair (.fc i) (.wc i) fun fc wc =>
      readerScan j saved (forwarded || decide (fc.value = wc.value)) rest

def readerProgram (j : Fin n) : Program n α :=
  .read (.wc j) fun token => .write (.rc j) token.value
    (.read .buff1 fun saved => readerScan j saved false (List.finRange n))

end MultiReaderAtomic
