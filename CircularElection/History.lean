module
public import CircularElection.Traces

/-! Exact finite FIFO histories, derived from the actual asynchronous protocol.
These are proof witnesses only. They do not impose phase completion or safety. -/
@[expose] public section
namespace CircularElection
variable {n : Nat} {Id : Type} [LinearOrder Id]

/-- A process's local transcript starts in its real initial local state. Sends
and receives record values; comparisons retain the actual published test. The
singleton receive input strips away only the unused FIFO tail. -/
inductive LocalHistory (owner : Id) (p : Fin n) : Local Id → List Id → List Id → Prop
  | initial : LocalHistory owner p ⟨.firstSend, owner, none, none⟩ [] []
  | send {l l' out input v} : LocalHistory owner p l out input →
      localStep owner (.send p) l [] = some (l', [], some v) →
      LocalHistory owner p l' (out ++ [v]) input
  | receive {l l' out input v} : LocalHistory owner p l out input →
      localStep owner (.receive p) l [v] = some (l', [], none) →
      LocalHistory owner p l' out (input ++ [v])
  | compare {l l' out input} : LocalHistory owner p l out input →
      localStep owner (.compare p) l [] = some (l', [], none) →
      LocalHistory owner p l' out input

/-- Complete emitted/consumed streams, including occurrences no longer in queues. -/
structure History (n : Nat) (Id : Type) where
  output : Fin n → List Id
  input : Fin n → List Id

def initialHistory : History n Id := ⟨fun _ => [], fun _ => []⟩

/-- Exact list equality supplies ordering and values, not only occurrence counts.
Delivered/receive observations are linked to the model's unchanged counters. -/
def HasHistory (owner : Fin n → Id) (s : State n Id) (h : History n Id) : Prop :=
  (∀ p, LocalHistory (owner p) p (s.process p) (h.output p) (h.input p)) ∧
  (∀ p, h.output p = h.input (next p) ++ s.inbox (next p) ++ s.edge p) ∧
  (∀ p, (h.output p).length = s.sent p) ∧
  (∀ p, (h.input (next p)).length + (s.inbox (next p)).length = s.delivered p)

private theorem history_next_injective : Function.Injective (next (n := n)) := by
  intro p q h
  have hp := p.isLt
  have hq := q.isLt
  have he := congrArg Fin.val h
  change (p.val + 1) % n = (q.val + 1) % n at he
  by_cases hpw : p.val + 1 < n <;> by_cases hqw : q.val + 1 < n
  all_goals
    try have : p.val + 1 = n := by omega
    try have : q.val + 1 = n := by omega
    simp_all [Nat.mod_eq_of_lt]
  all_goals apply Fin.ext; omega

private theorem send_strip (owner : Id) (p : Fin n) (l : Local Id)
    (q : List Id) (r : Local Id × List Id × Option Id)
    (hs : localStep owner (.send p) l q = some r) :
    ∃ l' v, r = (l', q, some v) ∧
      localStep owner (.send p) l [] = some (l', [], some v) := by
  rcases l with ⟨pc, tid, ntid, nntid⟩
  cases pc <;> simp only [localStep] at hs <;> try contradiction
  all_goals try split at hs
  all_goals try contradiction
  all_goals cases hs; exact ⟨_, _, rfl, by simp [localStep]⟩

private theorem receive_strip (owner : Id) (p : Fin n) (l : Local Id)
    (q : List Id) (r : Local Id × List Id × Option Id)
    (hs : localStep owner (.receive p) l q = some r) :
    ∃ l' v rest, q = v :: rest ∧ r = (l', rest, none) ∧
      localStep owner (.receive p) l [v] = some (l', [], none) := by
  rcases l with ⟨pc, tid, ntid, nntid⟩
  cases pc <;> cases q <;> simp only [localStep] at hs <;> try contradiction
  all_goals split at hs
  all_goals cases hs; exact ⟨_, _, _, rfl, rfl, by simp_all [localStep]⟩

private theorem compare_strip (owner : Id) (p : Fin n) (l : Local Id)
    (q : List Id) (r : Local Id × List Id × Option Id)
    (hs : localStep owner (.compare p) l q = some r) :
    ∃ l', r = (l', q, none) ∧
      localStep owner (.compare p) l [] = some (l', [], none) := by
  rcases l with ⟨pc, tid, ntid, nntid⟩
  cases pc <;> simp only [localStep] at hs <;> try contradiction
  split at hs <;> try contradiction
  split at hs <;> cases hs
  all_goals exact ⟨_, rfl, by simp only [localStep]; simp_all only [ite_true, ite_false]⟩

private theorem history_initial (owner : Fin n → Id) :
    HasHistory owner (initial owner) initialHistory := by
  refine ⟨fun p => .initial, ?_, ?_, ?_⟩ <;>
    simp [initialHistory, initial]

/-- Every successful actual transition extends exact history witnesses. -/
theorem step_history (owner : Fin n → Id) {s t : State n Id} {a : Action n}
    {h : History n Id} (hh : HasHistory owner s h) (ht : (lts owner).Tr s a t) :
    ∃ h', HasHistory owner t h' := by
  change execute owner s a = some t at ht
  rcases hh with ⟨hl, hq, hc, hd⟩
  cases a with
  | idle =>
    simp only [execute, Option.some.injEq] at ht
    subst t
    exact ⟨h, hl, hq, hc, hd⟩
  | deliver p =>
    cases he : s.edge p with
    | nil => simp [execute, he] at ht
    | cons v rest =>
      simp only [execute, he, Option.some.injEq] at ht
      subst t
      refine ⟨h, hl, ?_, hc, ?_⟩
      · intro i
        have hi := hq i
        by_cases hip : i = p
        · subst i; simpa [he, List.append_assoc] using hi
        · have hn : next i ≠ next p := fun h => hip (history_next_injective h)
          simpa [Function.update_of_ne hip, Function.update_of_ne hn] using hi
      · intro i
        have hi := hd i
        by_cases hip : i = p
        · subst i; simp; omega
        · have hn : next i ≠ next p := fun h => hip (history_next_injective h)
          simpa [Function.update_of_ne hip, Function.update_of_ne hn] using hi
  | send p =>
    simp only [execute, Option.map_eq_some_iff] at ht
    obtain ⟨r, hr, rfl⟩ := ht
    obtain ⟨l', v, rfl, hs⟩ := send_strip _ _ _ _ _ hr
    let h' : History n Id :=
      {h with output := Function.update h.output p (h.output p ++ [v])}
    refine ⟨h', ?_, ?_, ?_, ?_⟩
    · intro i
      by_cases hip : i = p
      · subst i; simpa [h', commitLocal] using LocalHistory.send (hl p) hs
      · simpa [h', commitLocal, Function.update_of_ne hip] using hl i
    · intro i
      have hi := hq i
      by_cases hip : i = p <;> simp_all [h', commitLocal, List.append_assoc]
    · intro i
      by_cases hip : i = p
      · subst i
        simpa [h', commitLocal] using hc p
      · simpa [h', commitLocal, Function.update_of_ne hip] using hc i
    · intro i; simpa [h', commitLocal] using hd i
  | receive p =>
    simp only [execute, Option.map_eq_some_iff] at ht
    obtain ⟨r, hr, rfl⟩ := ht
    obtain ⟨l', v, rest, he, rfl, hs⟩ := receive_strip _ _ _ _ _ hr
    let h' : History n Id :=
      {h with input := Function.update h.input p (h.input p ++ [v])}
    refine ⟨h', ?_, ?_, ?_, ?_⟩
    · intro i
      by_cases hip : i = p
      · subst i; simpa [h', commitLocal] using LocalHistory.receive (hl p) hs
      · simpa [h', commitLocal, Function.update_of_ne hip] using hl i
    · intro i
      have hi := hq i
      by_cases hin : next i = p <;> simp_all [h', commitLocal, List.append_assoc]
    · intro i; simpa [h', commitLocal] using hc i
    · intro i
      have hi := hd i
      by_cases hin : next i = p <;> simp_all [h', commitLocal]
      omega
  | compare p =>
    simp only [execute, Option.map_eq_some_iff] at ht
    obtain ⟨r, hr, rfl⟩ := ht
    obtain ⟨l', rfl, hs⟩ := compare_strip _ _ _ _ _ hr
    refine ⟨h, ?_, ?_, ?_, ?_⟩
    · intro i
      by_cases hip : i = p
      · subst i; simpa [commitLocal] using LocalHistory.compare (hl p) hs
      · simpa [commitLocal, Function.update_of_ne hip] using hl i
    · simpa [commitLocal] using hq
    · simpa [commitLocal] using hc
    · simpa [commitLocal] using hd

/-- Arbitrary initialized finite LTS traces have exact ordered value histories.
No fairness, injectivity, positive-size or phase-alignment premise is required. -/
theorem reachable_history (owner : Fin n → Id) {s : State n Id}
    (hr : Reachable owner s) : ∃ h, HasHistory owner s h := by
  obtain ⟨as, hr⟩ := hr
  apply Cslib.LTS.mtrInv_of_trInv (p := fun s => ∃ h, HasHistory owner s h)
    (fun _ _ _ ht ⟨h, hh⟩ => step_history owner hh ht) _ _ _ hr
  exact ⟨initialHistory, history_initial owner⟩

/-- The same history evidence covers the announcing receive at the final state. -/
theorem beforeFirst_history (owner : Fin n → Id) {as : List (Action n)} {s : State n Id}
    (hr : BeforeFirst owner (initial owner) as s) : ∃ h, HasHistory owner s h :=
  reachable_history owner ⟨as, beforeFirst_trace owner hr⟩

/-- The k-th consumed value is exactly the k-th emitted value on the incoming
edge. This is an occurrence statement, even when several values are equal. -/
theorem history_fifo_occurrence (owner : Fin n → Id) {s : State n Id} {h : History n Id}
    (hh : HasHistory owner s h) (p : Fin n) (k : Nat)
    (hk : k < (h.input (next p)).length) :
    (h.output p)[k]? = (h.input (next p))[k]? := by
  rw [hh.2.1 p, List.append_assoc]
  exact List.getElem?_append_left hk

/-- Announcement stops the announcing process's remaining local instructions.
One may not complete its current phase inside the accepted actual protocol. -/
theorem elected_local_disabled (owner : Fin n → Id) (s : State n Id) (p : Fin n)
    (hp : (s.process p).pc = .elected) (a : Action n) (ha : actProcess a = some p) :
    execute owner s a = none := by
  cases a <;> simp_all [actProcess, execute, localStep]

/-- A real terminal partial phase: the one-process run announces after its first
send, and cannot supply a second send to a proposed actual phase completion. -/
theorem one_process_partial_phase :
    ∃ s, BeforeFirst (fun _ : Fin 1 => 7) (initial (fun _ : Fin 1 => 7)) oneSchedule s ∧
      s.sent 0 = 1 ∧ (s.process 0).pc = .elected ∧
      execute (fun _ : Fin 1 => 7) s (.send 0) = none := by
  have hc : (runBefore (fun _ : Fin 1 => 7) (initial (fun _ : Fin 1 => 7))
      oneSchedule).map (fun s => (s.sent 0, (s.process 0).pc)) =
      some (1, PC.elected) := by decide
  obtain ⟨s, hs, hv⟩ := Option.map_eq_some_iff.mp hc
  have hpair := Prod.mk.inj hv
  exact ⟨s, runBefore_sound _ hs, hpair.1, hpair.2,
    elected_local_disabled _ s 0 hpair.2 (.send 0) rfl⟩

end CircularElection
