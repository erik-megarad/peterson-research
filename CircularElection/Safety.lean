module
public import CircularElection.Plan

/-! Actual FIFO occurrence refinement and general election safety. -/
@[expose] public section
namespace CircularElection
variable {n : Nat} {Id : Type} [LinearOrder Id]

private theorem actual_next_injective : Function.Injective (next (n := n)) := by
  intro p q h
  apply (finRotate n).injective
  simpa only [rotate_is_actual_next] using h

private theorem fifo_local_count_step (owner : Id) (p : Fin n) (a : Action n)
    (l : Local Id) (q : List Id) (r : Local Id × List Id × Option Id)
    (sent received : Nat) (ha : actProcess a = some p)
    (hc : LocalCount sent received l.pc) (hs : localStep owner a l q = some r) :
    LocalCount (sent + r.2.2.toList.length)
      (received + (match a with | .receive _ => 1 | _ => 0)) r.1.pc ∧
    r.2.1.length + (match a with | .receive _ => 1 | _ => 0) = q.length := by
  rcases l with ⟨pc, tid, ntid, nntid⟩
  cases a <;> cases pc <;> simp only [localStep] at hs <;> try contradiction
  all_goals try (split at hs)
  all_goals try (split at hs)
  all_goals try (split at hs)
  all_goals cases hs
  all_goals simp_all [LocalCount]
  all_goals omega

omit [LinearOrder Id] in
private theorem fifo_commit_counted (s : State n Id) (rc : Fin n → Nat) (p : Fin n)
    (r : Local Id × List Id × Option Id) (d : Nat) (hs : Counted s rc)
    (hc : LocalCount (s.sent p + r.2.2.toList.length) (rc p + d) r.1.pc)
    (hq : r.2.1.length + d = (s.inbox p).length) :
    Counted (commitLocal s p r) (Function.update rc p (rc p + d)) := by
  rcases r with ⟨l, q, out⟩
  cases out <;> constructor
  all_goals
    intro i
    have hp := hs.1 i
    have hi := hs.2 i
    by_cases he : i = p <;> by_cases hn : next i = p <;>
      simp_all [commitLocal]
    all_goals omega

private theorem fifo_counted_step (owner : Fin n → Id) {s t : State n Id}
    {a : Action n} {rc : Fin n → Nat} (hc : Counted s rc)
    (h : (lts owner).Tr s a t) : Counted t (receivedAfter rc a) := by
  change execute owner s a = some t at h
  cases a with
  | idle =>
    simp only [execute, Option.some.injEq] at h
    exact h ▸ hc
  | deliver p =>
    cases he : s.edge p with
    | nil => simp [execute, he] at h
    | cons v rest =>
      simp only [execute, he, Option.some.injEq] at h
      subst t
      refine ⟨hc.1, ?_⟩
      intro i
      have hi := hc.2 i
      by_cases hip : i = p
      · subst i
        simp [receivedAfter, he] at hi ⊢
        omega
      · have hn : next i ≠ next p := fun h => hip (actual_next_injective h)
        simpa [receivedAfter, Function.update_of_ne hip, Function.update_of_ne hn] using hi
  | send p | receive p | compare p =>
    simp only [execute, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    have hl := fifo_local_count_step (owner p) p _ (s.process p) (s.inbox p) r
      (s.sent p) (rc p) rfl (hc.1 p) hr
    all_goals
      simpa [receivedAfter] using fifo_commit_counted s rc p r _ hc hl.1 hl.2

private theorem fifo_send_strip (owner : Id) (p : Fin n) (l : Local Id)
    (q : List Id) (r : Local Id × List Id × Option Id)
    (hs : localStep owner (.send p) l q = some r) :
    ∃ l' v, r = (l', q, some v) ∧
      localStep owner (.send p) l [] = some (l', [], some v) := by
  rcases l with ⟨pc, tid, ntid, nntid⟩
  cases pc <;> simp only [localStep] at hs <;> try contradiction
  all_goals try split at hs
  all_goals try contradiction
  all_goals cases hs; exact ⟨_, _, rfl, by simp [localStep]⟩

private theorem fifo_receive_strip (owner : Id) (p : Fin n) (l : Local Id)
    (q : List Id) (r : Local Id × List Id × Option Id)
    (hs : localStep owner (.receive p) l q = some r) :
    ∃ l' v rest, q = v :: rest ∧ r = (l', rest, none) ∧
      localStep owner (.receive p) l [v] = some (l', [], none) := by
  rcases l with ⟨pc, tid, ntid, nntid⟩
  cases pc <;> cases q <;> simp only [localStep] at hs <;> try contradiction
  all_goals split at hs
  all_goals cases hs; exact ⟨_, _, _, rfl, rfl, by simp_all [localStep]⟩

private theorem fifo_compare_strip (owner : Id) (p : Fin n) (l : Local Id)
    (q : List Id) (r : Local Id × List Id × Option Id)
    (hs : localStep owner (.compare p) l q = some r) :
    ∃ l', r = (l', q, none) ∧
      localStep owner (.compare p) l [] = some (l', [], none) := by
  rcases l with ⟨pc, tid, ntid, nntid⟩
  cases pc <;> simp only [localStep] at hs <;> try contradiction
  split at hs <;> try contradiction
  split at hs <;> cases hs
  all_goals exact ⟨_, rfl, by simp only [localStep]; simp_all only [ite_true, ite_false]⟩


/-- Each value in a FIFO tail agrees with its absolute input occurrence. -/
def QueueMatches (stream : Nat → Id) : Nat → List Id → Prop
  | _, [] => True
  | k, v :: rest => stream k = v ∧ QueueMatches stream (k + 1) rest

omit [LinearOrder Id] in
private theorem queueMatches_append (stream : Nat → Id) (k : Nat) (xs ys : List Id) :
    QueueMatches stream k (xs ++ ys) ↔
      QueueMatches stream k xs ∧ QueueMatches stream (k + xs.length) ys := by
  induction xs generalizing k with
  | nil => simp [QueueMatches]
  | cons v rest ih => simp [QueueMatches, ih, Nat.add_comm, Nat.add_left_comm, and_assoc]

variable (owner : Fin n → Id) (hn : 0 < n) (hi : Function.Injective owner)

structure Planned (s : State n Id) (received : Fin n → Nat) : Prop where
  counts : Counted s received
  locals : ∀ p, LocalPlan owner hn hi p (s.sent p) (received p) (s.process p)
  queues : ∀ p, QueueMatches (inputAt owner hn hi (next p)) (received (next p))
    (s.inbox (next p) ++ s.edge p)

private theorem planned_head {s : State n Id} {rc : Fin n → Nat}
    (hp : Planned owner hn hi s rc) (p : Fin n) (v : Id) (rest : List Id)
    (hq : s.inbox p = v :: rest) : inputAt owner hn hi p (rc p) = v := by
  let previous := (finRotate n).symm p
  have he : next previous = p := by
    rw [← rotate_is_actual_next]
    exact (finRotate n).apply_symm_apply p
  have hh := hp.queues previous
  rw [he, hq] at hh
  exact hh.1

private theorem planned_initial : Planned owner hn hi (initial owner) (fun _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Counted, LocalCount, initial]
  · intro p
    refine ⟨0, rfl, rfl, ?_, rfl⟩
    exact ⟨p, rfl⟩
  · intro p
    trivial

/-- Every actual instruction preserves local and FIFO occurrence refinement. -/
theorem step_planned {s t : State n Id} {a : Action n} {rc : Fin n → Nat}
    (hp : Planned owner hn hi s rc) (ht : (lts owner).Tr s a t) :
    Planned owner hn hi t (receivedAfter rc a) := by
  have hcount := fifo_counted_step owner hp.counts ht
  change execute owner s a = some t at ht
  cases a with
  | idle =>
    simp only [execute, Option.some.injEq] at ht
    subst t
    exact hp
  | deliver p =>
    cases he : s.edge p with
    | nil => simp [execute, he] at ht
    | cons v rest =>
      simp only [execute, he, Option.some.injEq] at ht
      subst t
      refine ⟨hcount, hp.locals, ?_⟩
      intro i
      have hh := hp.queues i
      by_cases hip : i = p
      · subst i
        simpa [receivedAfter, he, List.append_assoc] using hh
      · have hn' : next i ≠ next p := fun h => hip (actual_next_injective h)
        simpa [receivedAfter, Function.update_of_ne hip, Function.update_of_ne hn'] using hh
  | send p =>
    simp only [execute, Option.map_eq_some_iff] at ht
    obtain ⟨r, hr, rfl⟩ := ht
    obtain ⟨l', v, rfl, _⟩ := fifo_send_strip _ _ _ _ _ hr
    have hl := local_plan_step owner hn hi p (.send p) (s.process p) (s.inbox p)
      (l', s.inbox p, some v) (s.sent p) (rc p) (hp.locals p)
      (planned_head owner hn hi hp p) hr
    refine ⟨hcount, ?_, ?_⟩
    · intro i
      by_cases hip : i = p
      · subst i
        simpa [commitLocal, receivedAfter] using hl.1
      · simpa [commitLocal, receivedAfter, Function.update_of_ne hip] using hp.locals i
    · intro i
      by_cases hip : i = p
      · subst i
        have hemit := hl.2.1 v rfl
        have hc := hp.counts.2 p
        have hlen : rc (next p) + (s.inbox (next p) ++ s.edge p).length = s.sent p := by
          simp only [List.length_append]
          omega
        have hm : QueueMatches (inputAt owner hn hi (next p)) (rc (next p))
            ((s.inbox (next p) ++ s.edge p) ++ [v]) := by
          rw [queueMatches_append]
          refine ⟨hp.queues p, ?_⟩
          change inputAt owner hn hi (next p)
            (rc (next p) + (s.inbox (next p) ++ s.edge p).length) = v ∧ True
          rw [hlen]
          exact ⟨hemit, trivial⟩
        simpa [commitLocal, receivedAfter, List.append_assoc] using hm
      · simpa [commitLocal, receivedAfter, Function.update_of_ne hip] using hp.queues i
  | receive p =>
    simp only [execute, Option.map_eq_some_iff] at ht
    obtain ⟨r, hr, rfl⟩ := ht
    obtain ⟨l', v, rest, he, rfl, _⟩ := fifo_receive_strip _ _ _ _ _ hr
    have hl := local_plan_step owner hn hi p (.receive p) (s.process p) (s.inbox p)
      (l', rest, none) (s.sent p) (rc p) (hp.locals p)
      (planned_head owner hn hi hp p) hr
    refine ⟨hcount, ?_, ?_⟩
    · intro i
      by_cases hip : i = p
      · subst i
        simpa [commitLocal, receivedAfter] using hl.1
      · simpa [commitLocal, receivedAfter, Function.update_of_ne hip] using hp.locals i
    · intro i
      have hh := hp.queues i
      by_cases hin : next i = p
      · rw [hin, he] at hh
        have htail := hh.2
        simpa [commitLocal, receivedAfter, hin] using htail
      · simpa [commitLocal, receivedAfter, Function.update_of_ne hin] using hh
  | compare p =>
    simp only [execute, Option.map_eq_some_iff] at ht
    obtain ⟨r, hr, rfl⟩ := ht
    obtain ⟨l', rfl, _⟩ := fifo_compare_strip _ _ _ _ _ hr
    have hl := local_plan_step owner hn hi p (.compare p) (s.process p) (s.inbox p)
      (l', s.inbox p, none) (s.sent p) (rc p) (hp.locals p)
      (planned_head owner hn hi hp p) hr
    refine ⟨hcount, ?_, ?_⟩
    · intro i
      by_cases hip : i = p
      · subst i
        simpa [commitLocal, receivedAfter] using hl.1
      · simpa [commitLocal, receivedAfter, Function.update_of_ne hip] using hp.locals i
    · intro i
      simpa [commitLocal, receivedAfter] using hp.queues i

/-- General initialized finite executions refine the occurrence plan, including
announcing states and partial rounds. There is no scheduling/fairness premise. -/
theorem reachable_planned {s : State n Id} (hr : Reachable owner s) :
    ∃ rc, Planned owner hn hi s rc := by
  obtain ⟨as, htrace⟩ := hr
  apply Cslib.LTS.mtrInv_of_trInv (p := fun s => ∃ rc, Planned owner hn hi s rc)
    (fun _ _ _ ht ⟨rc, hp⟩ => ⟨receivedAfter rc _, step_planned owner hn hi hp ht⟩)
    _ _ _ htrace
  exact ⟨fun _ => 0, planned_initial owner hn hi⟩

include hn hi in
/-- Every reachable announcement belongs to the original maximum owner. -/
theorem reachable_announcer_maximum {s : State n Id} (hr : Reachable owner s)
    (p : Fin n) (he : (s.process p).pc = .elected) : IsMaximum owner p := by
  obtain ⟨rc, hp⟩ := reachable_planned owner hn hi hr
  simpa only [LocalPlan, he] using hp.locals p

include hn hi in
/-- The unchanged R2c target, for all positive rings and injective owners on
exactly the accepted asynchronous reliable FIFO transition system. -/
theorem election_safety : ElectionSafety owner := by
  intro as s h p he
  exact reachable_announcer_maximum owner hn hi
    ⟨as, beforeFirst_trace owner h⟩ p he

end CircularElection
