import Peterson.EconomicalSolutions.Algorithm5Economy
import Peterson.EconomicalSolutions.Algorithm5Sanity

/-! A concrete obstruction to the proposed priority-only erasure. All steps
use the frozen Algorithm 5 interpreter; the erasure is only an observation. -/
namespace EconomicalSolutions.Algorithm5

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private def cfg : Config 2 := ascendingConfig 2 (by decide)

/-- Keep the tournament value before enqueue, but keep only the priority once
queued. On reachable registers, these are exactly the proposed A5 codes. -/
def erase5 (v : Value) : Algorithm2.Value ⊕ Int :=
  if v.priority = -1 then .inl v.tournament else .inr v.priority

private def commands : List (Command 2) :=
  List.replicate 19 (.run 0) ++ List.replicate 2 (.run 1) ++ [.run 0]

private def state (k : Nat) : State 2 :=
  (twoRun (commands.take k)).getD (initial 2)

private def command (k : Nat) : Command 2 := commands[k]?.getD .stutter

/-- Pointwise equality allows finite checking of genuine `next` edges without
postulating decidable equality of state functions. -/
private def Edge (s : State 2) (c : Command 2) (t : State 2) : Prop :=
  match next cfg s c with
  | none => False
  | some u => ∀ p, u p = t p

private instance (s : State 2) (c : Command 2) (t : State 2) : Decidable (Edge s c t) := by
  unfold Edge
  split <;> infer_instance

private theorem edge_next {s t : State 2} {c : Command 2} (h : Edge s c t) :
    next cfg s c = some t := by
  unfold Edge at h
  split at h
  · contradiction
  · rename_i u eq
    exact eq.trans (congrArg some (funext h))

/-- Nineteen process-0 runs, two process-1 runs, then process 0 departs. -/
theorem erasure_trace_edges : commands.length = 22 ∧
    ∀ k : Fin 22, Edge (state k) (command k) (state (k + 1)) := by decide

private theorem state_zero : state 0 = initial 2 := by
  funext p
  fin_cases p <;> decide

theorem erasure_reachable (k : Nat) (hk : k ≤ 22) : Reachable cfg (state k) := by
  induction k with
  | zero => rw [state_zero]; exact .initial
  | succ j ih =>
      have hj : j < 22 := by omega
      exact .step (ih (by omega))
        ⟨command j, edge_next (erasure_trace_edges.2 ⟨j, hj⟩), rfl⟩

private def beforeDeparture : State 2 := state 21
private def afterDeparture : State 2 := state 22

theorem erasure_departure_edge :
    next cfg beforeDeparture (.run 0) = some afterDeparture := by
  simpa [beforeDeparture, afterDeparture, command, commands] using
    edge_next (erasure_trace_edges.2 ⟨21, by decide⟩)

/-- The next tournament scan observes the retained root flag before the
departure, and dead after it. The actor has not taken a step in between. -/
theorem erasure_observation :
    (beforeDeparture 0).pc = .depart ∧
    (beforeDeparture 0).value = ⟨⟨1, true⟩, 0⟩ ∧
    (afterDeparture 0).value = ⟨Algorithm2.dead, 0⟩ ∧
    (beforeDeparture 1).tournamentPC = .scan .first 1 [⟨0, by decide⟩] ∧
    beforeDeparture 1 = afterDeparture 1 ∧
    (∀ q, erase5 (beforeDeparture q).value = erase5 (afterDeparture q).value) ∧
    (ordinary cfg beforeDeparture 1).map Local.tournamentPC =
      some (.write1 1 ⟨1, false⟩) ∧
    (ordinary cfg afterDeparture 1).map Local.tournamentPC =
      some (.scan .first 1 []) ∧
    ordinary cfg beforeDeparture 1 ≠ ordinary cfg afterDeparture 1 := by decide +kernel

theorem erasure_witness :
    ∃ s t : State 2, Reachable cfg s ∧ Reachable cfg t ∧
      s 1 = t 1 ∧
      (∀ q, erase5 (s q).value = erase5 (t q).value) ∧
      ordinary cfg s 1 ≠ ordinary cfg t 1 := by
  refine ⟨beforeDeparture, afterDeparture,
    erasure_reachable 21 (by decide), erasure_reachable 22 (by decide), ?_⟩
  exact ⟨erasure_observation.2.2.2.2.1,
    erasure_observation.2.2.2.2.2.1,
    erasure_observation.2.2.2.2.2.2.2.2⟩

/-- No function of the actor's complete local state and these erased owner
messages can return the unchanged ordinary instruction on all reachable states. -/
theorem erasure_does_not_factor :
    ¬ ∃ f : Local 2 → (Proc 2 → Algorithm2.Value ⊕ Int) → Option (Local 2),
      ∀ u, Reachable cfg u →
        ordinary cfg u 1 = f (u 1) (fun q => erase5 (u q).value) := by
  rintro ⟨f, hf⟩
  have hs := hf beforeDeparture (erasure_reachable 21 (by omega))
  have ht := hf afterDeparture (erasure_reachable 22 (by omega))
  obtain ⟨_, _, _, _, hlocal, hcodes, _, _, hdiff⟩ := erasure_observation
  have codes : (fun q => erase5 (beforeDeparture q).value) =
      (fun q => erase5 (afterDeparture q).value) := funext hcodes
  apply hdiff
  rw [hs, ht, hlocal, codes]

end EconomicalSolutions.Algorithm5

#print axioms EconomicalSolutions.Algorithm5.erasure_trace_edges
#print axioms EconomicalSolutions.Algorithm5.erasure_reachable
#print axioms EconomicalSolutions.Algorithm5.erasure_departure_edge
#print axioms EconomicalSolutions.Algorithm5.erasure_observation
#print axioms EconomicalSolutions.Algorithm5.erasure_witness
#print axioms EconomicalSolutions.Algorithm5.erasure_does_not_factor
