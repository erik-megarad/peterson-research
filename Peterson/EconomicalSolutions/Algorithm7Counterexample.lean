import Peterson.EconomicalSolutions.Algorithm7Certificate

/-! A finite strict-publication-FIFO reversal with an admissible infinite tail.
Every explicit certificate edge is checked against the real interpreter by
kernel reduction. Native evaluation is not a proof step. -/
namespace EconomicalSolutions.Algorithm7.Counterexample
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def state (t : Nat) : State 2 :=
  if t < 223 then
    let row := snapshots[t]?.getD (reset false, reset false)
    fun p => if p = 0 then row.1 else row.2
  else initial 2

def event (t : Nat) : Label 2 := label (state t) (command t)

/-- Pointwise equality makes the finite check decidable without assuming an
equality oracle for functions. An invalid command makes this proposition false. -/
def Edge (s : State 2) (c : Command 2) (t : State 2) : Prop :=
  match next config s c with
  | none => False
  | some u => ∀ p, u p = t p
instance (s : State 2) (c : Command 2) (t : State 2) : Decidable (Edge s c t) := by
  unfold Edge
  split <;> infer_instance

theorem edge_next {s t : State 2} {c : Command 2} (h : Edge s c t) :
    next config s c = some t := by
  unfold Edge at h
  split at h
  · contradiction
  · rename_i u eq
    exact eq.trans (congrArg some (funext h))

theorem finite_edges : ∀ t : Fin 223,
    Edge (state t) (command t) (state (t + 1)) := by decide

theorem commands_length : commands.length = 223 := by decide

theorem tail_state {t : Nat} (h : 223 ≤ t) : state t = initial 2 := by
  simp [state, show ¬ t < 223 by omega]

theorem tail_command {t : Nat} (h : 223 ≤ t) : command t = .stutter := by
  have past : commands.length ≤ t := by rw [commands_length]; exact h
  simp [command, List.getElem?_eq_none past]

theorem execution_step (t : Nat) : next config (state t) (command t) = some (state (t + 1)) := by
  by_cases before : t < 223
  · exact edge_next (finite_edges ⟨t, before⟩)
  · rw [tail_command (by omega), tail_state (by omega), tail_state (by omega)]
    rfl

def witness : Run config where
  state := state
  command := command
  initialized := funext (by decide)
  valid := execution_step

/-- The run uses exactly the same relation as the CSLib LTS. -/
theorem execution_lts (t : Nat) : (lts config).Tr (state t) (event t) (state (t + 1)) :=
  ⟨command t, execution_step t, rfl⟩

/-- The final release instruction of each process discharges every earlier
protocol occurrence in this particular finite schedule. Idle tail owes none. -/
theorem protocol_scheduling : ProtocolScheduling witness := by
  have finite : ∀ t : Fin 223, ∀ p : Fin 2, Protocol (state t p).pc →
      t.val ≤ (if p = 0 then 207 else 222) ∧
      Acts (command (if p = 0 then 207 else 222)) p := by decide
  intro t p owed
  by_cases before : t < 223
  · exact ⟨if p = 0 then 207 else 222, finite ⟨t, before⟩ p owed⟩
  · have inactive : ¬ Protocol (initial 2 p).pc := by simp [initial, reset, Protocol]
    exfalso
    apply inactive
    simpa only [witness, tail_state (by omega : 223 ≤ t)] using owed

theorem critical_completion : CriticalCompletion witness := by
  have finite : ∀ t : Fin 223, ∀ p : Fin 2, (state t p).pc = .cs →
      event t = .complete p := by decide
  intro t p occupied
  by_cases before : t < 223
  · exact ⟨t, le_refl _, Or.inl (finite ⟨t, before⟩ p occupied)⟩
  · have idle : (witness.state t p).pc = .idle := by
      simp [witness, tail_state (by omega : 223 ≤ t), initial, reset]
    rw [idle] at occupied
    contradiction

/-- Kernel-checked event indices and retained original earlier request. -/
theorem publication_reversal :
    event 1 = .request 1 ∧ event 92 = .queuePublish 1 ∧
    event 94 = .queuePublish 0 ∧ event 205 = .entry 0 ∧
    (state 206 0).pc = .cs ∧
    (state 206 1).pc = .attempt .eligible false .attempt ∧
    (state 206 1).value = .live .three true true ∧
    (∀ t : Fin 206, event t ≠ .entry 1 ∧ event t ≠ .fail 1) ∧
    (∀ t : Fin 205, 1 < t.val → event t ≠ .request 1) := by decide

/-- Counts include the fourth clock-0 tick; each level-three count was reset.
The certificate contains all intermediate whole registers and local caches. -/
theorem exposure_counts :
    ((state 87 0).count0, (state 87 0).count1) = (4, 3) ∧
    ((state 87 1).count0, (state 87 1).count1) = (3, 3) ∧
    (∀ p : Fin 2, ((state 195 p).count0, (state 195 p).count1) = (3, 3)) ∧
    (∀ t : Fin 206, ∀ p : Fin 2, (state t p).behind = ∅) := by decide

theorem no_failures (t : Nat) (p : Fin 2) : event t ≠ .fail p := by
  have finite : ∀ t : Fin 223, ∀ p : Fin 2, event t ≠ .fail p := by decide
  by_cases before : t < 223
  · exact finite ⟨t, before⟩ p
  · simp [event, tail_command (by omega : 223 ≤ t), label]

theorem not_publication_fifo : ¬ PublicationFIFO witness := by
  intro fifo
  have laterOriginal : ∀ t : Fin 205, 94 ≤ t.val →
      event t ≠ .entry 0 ∧ event t ≠ .fail 0 := by decide
  obtain ⟨u, _lo, hi, outcome⟩ := fifo 1 0 92 94 205 (by decide) (by decide) (by decide)
    publication_reversal.2.1 publication_reversal.2.2.1 publication_reversal.2.2.2.1
    (fun t lo hi => laterOriginal ⟨t, hi⟩ lo)
  have neither := publication_reversal.2.2.2.2.2.2.2.1 ⟨u, by omega⟩
  exact outcome.elim neither.1 neither.2

/-- One actual initialized failure-free execution satisfies both frozen
liveness premises and violates the exact strict publication-order comparison. -/
theorem admissible_counterexample :
    ProtocolScheduling witness ∧ CriticalCompletion witness ∧
    (∀ t p, witness.event t ≠ .fail p) ∧ ¬ PublicationFIFO witness :=
  ⟨protocol_scheduling, critical_completion, no_failures, not_publication_fifo⟩

theorem not_universal_publication_fifo : ¬ UniversalPublicationFIFO := by
  intro fifo
  exact not_publication_fifo (fifo 2 (by decide) config witness protocol_scheduling critical_completion)

#print axioms finite_edges
#print axioms execution_lts
#print axioms publication_reversal
#print axioms exposure_counts
#print axioms admissible_counterexample
#print axioms not_universal_publication_fifo

end EconomicalSolutions.Algorithm7.Counterexample
