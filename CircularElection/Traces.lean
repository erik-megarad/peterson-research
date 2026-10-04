module

public import CircularElection.Model

@[expose] public section
namespace CircularElection
variable {n : Nat} {Id : Type} [LinearOrder Id]

/-- Decidable first-announcement boundary for finite trace certificates. -/
def runBefore (owner : Fin n → Id) (s : State n Id) : List (Action n) → Option (State n Id)
  | [] => some s
  | a :: as => if ∃ p, (s.process p).pc = .elected then none
      else (execute owner s a).bind (fun t => runBefore owner t as)

theorem runBefore_sound (owner : Fin n → Id) {as : List (Action n)} {s t : State n Id}
    (h : runBefore owner s as = some t) : BeforeFirst owner s as t := by
  induction as generalizing s with
  | nil =>
    simp only [runBefore, Option.some.injEq] at h
    subst t
    exact .nil s
  | cons a as ih =>
    simp only [runBefore] at h
    split at h
    · contradiction
    · rename_i hn
      cases he : execute owner s a with
      | none => simp [he] at h
      | some u =>
        simp only [he, Option.bind_some] at h
        exact .cons hn he (ih h)

theorem beforeFirst_trace (owner : Fin n → Id) {as : List (Action n)} {s t : State n Id}
    (h : BeforeFirst owner s as t) : (lts owner).MTr s as t := by
  induction h with
  | nil => exact .refl
  | cons _ h _ ih => exact .stepL h ih

/-- Numeric owners 0 and 1 give a concrete ordered, injective two-process instance. -/
def owners₂ : Fin 2 → Nat := Fin.val

def oneSchedule : List (Action 1) := [.send 0, .deliver 0, .receive 0]

/-- Each owner sends and receives once; the smaller owner forwards 1, then
owner 1 performs its mandatory second send before receiving the returned 1. -/
def fourSchedule : List (Action 2) :=
  [.send 0, .send 1, .deliver 0, .deliver 1, .receive 0, .receive 1,
   .send 0, .send 1, .deliver 0, .receive 1]

/-- The smaller owner receives the other second message, adopts 1 using >=,
and makes the fifth send before owner 1 performs its announcing receive. -/
def fiveSchedule : List (Action 2) :=
  [.send 0, .send 1, .deliver 0, .deliver 1, .receive 0, .receive 1,
   .send 0, .send 1, .deliver 1, .receive 0, .compare 0, .send 0,
   .deliver 0, .receive 1]

private theorem certificate (owner : Fin n → Nat) (as : List (Action n))
    (p : Fin n) (cost : Nat)
    (h : (runBefore owner (initial owner) as).map
      (fun s => (s.sends, (s.process p).pc)) = some (cost, PC.elected)) :
    ∃ s, BeforeFirst owner (initial owner) as s ∧
      s.sends = cost ∧ (s.process p).pc = .elected := by
  obtain ⟨s, hs, ho⟩ := Option.map_eq_some_iff.mp h
  exact ⟨s, runBefore_sound owner hs, (Prod.mk.inj ho).1, (Prod.mk.inj ho).2⟩

/-- One send, self-loop delivery, then first-receive announcement. -/
theorem one_process_trace :
    ∃ s, BeforeFirst (fun _ : Fin 1 => 7) (initial (fun _ : Fin 1 => 7)) oneSchedule s ∧
      s.sends = 1 ∧ (s.process 0).pc = .elected := by
  apply certificate
  decide

theorem two_process_four_send_trace :
    ∃ s, BeforeFirst owners₂ (initial owners₂) fourSchedule s ∧
      s.sends = 4 ∧ (s.process 1).pc = .elected := by
  apply certificate
  decide

theorem two_process_five_send_trace :
    ∃ s, BeforeFirst owners₂ (initial owners₂) fiveSchedule s ∧
      s.sends = 5 ∧ (s.process 1).pc = .elected := by
  apply certificate
  decide

/-- The fifth-send schedule actually migrates the maximum candidate to owner 0. -/
theorem five_trace_carrier :
    (runBefore owners₂ (initial owners₂) fiveSchedule).map
      (fun s => ((s.process 0).tid, (s.process 0).pc)) = some (1, PC.firstReceive) := by
  decide

end CircularElection
