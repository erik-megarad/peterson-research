module
public import CircularElection.Safety
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Progress support for the accepted asynchronous protocol. -/
@[expose] public section
open scoped BigOperators
namespace CircularElection
variable {n : Nat} {Id : Type} [LinearOrder Id]

namespace Frontier
variable {owner : Fin n → Id}

/-- A nonsingleton frontier loses at least one carrier. -/
theorem advance_size_lt (f : Frontier owner) (hi : Function.Injective owner)
    (hm : 1 < f.size) : (f.advance hi).size < f.size := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp f.survivors_positive
  have hs : RoundSurvives f.candidate (finRotate f.size).symm p := by
    simpa [survivors] using hp
  have hd : f.candidate ((finRotate f.size).symm p) ≠
      f.candidate ((finRotate f.size).symm ((finRotate f.size).symm p)) := by
    intro he
    exact rotate_previous_ne hm _ ((f.candidate_injective hi he).symm)
  have hn := round_no_adjacent f.candidate (finRotate f.size).symm p hd hs
  have hnot : (finRotate f.size).symm p ∉ f.survivors := by
    simpa [survivors] using hn
  have hproper : f.survivors ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro he
    exact hnot (he ▸ Finset.mem_univ _)
  simpa [advance] using Finset.card_lt_card hproper
end Frontier

variable (owner : Fin n → Id) (hn : 0 < n) (hi : Function.Injective owner)

/-- Ideal recurrence reaches a singleton; actual progress is a separate obligation. -/
theorem frontier_eventually_singleton : ∃ r, (frontierAt owner hn hi r).size = 1 := by
  have aux : ∀ m r, (frontierAt owner hn hi r).size = m →
      ∃ s, (frontierAt owner hn hi s).size = 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro r hr
      by_cases hm : m = 1
      · exact ⟨r, hr.trans hm⟩
      · have hp := (frontierAt owner hn hi r).positive
        have hlt := (frontierAt owner hn hi r).advance_size_lt hi (by omega)
        exact ih _ (by simpa only [frontierAt, ← hr] using hlt) (r + 1) rfl
  exact aux _ 0 rfl

/-- Some original maximum has a finite prospective returning occurrence. -/
theorem planned_return_exists : ∃ p k, inputAt owner hn hi p k = owner p := by
  obtain ⟨r, hr⟩ := frontier_eventually_singleton owner hn hi
  let f := frontierAt owner hn hi r
  let c : Fin f.size := ⟨0, f.positive⟩
  refine ⟨f.origin c, 2 * r, ?_⟩
  rw [inputAt_even]
  change f.candidate ((finRotate f.size).symm (f.block (f.origin c))) = owner (f.origin c)
  have he : (finRotate f.size).symm (f.block (f.origin c)) = c := by
    apply Fin.ext
    have hh := ((finRotate f.size).symm (f.block (f.origin c))).isLt
    have hc := c.isLt
    change f.size = 1 at hr
    omega
  rw [he]
  rfl

/-- A control rank pays for the comparison instruction, which changes no counters. -/
def controlRank : PC → Nat
  | .firstSend | .relayReceive => 1
  | _ => 0

/-- Nonannouncing controls differ by at most one send/receive occurrence. -/
theorem local_count_bounds {s r : Nat} {pc : PC} (hc : LocalCount s r pc)
    (he : pc ≠ .elected) : s ≤ r + 1 ∧ r ≤ s + 1 := by
  cases pc <;> simp_all [LocalCount] <;> omega

omit hn hi in
/-- Every local instruction strictly advances counters plus its control rank. -/
theorem local_measure_increases (p : Fin n) (a : Action n) (l : Local Id)
    (q : List Id) (z : Local Id × List Id × Option Id)
    (hs : localStep (owner p) a l q = some z) :
    controlRank l.pc <
      2 * (z.2.2.toList.length + (match a with | .receive _ => 1 | _ => 0)) +
      controlRank z.1.pc := by
  rcases l with ⟨pc, tid, ntid, nntid⟩
  cases a <;> cases pc <;> simp only [localStep] at hs <;> try contradiction
  all_goals try (split at hs)
  all_goals try (split at hs)
  all_goals try (split at hs)
  all_goals cases hs
  all_goals simp [controlRank]

/-- The only local controls which can block have an empty receive inbox. -/
theorem planned_disabled {s : State n Id} {rc : Fin n → Nat}
    (hp : Planned owner hn hi s rc) (p : Fin n)
    (hne : (s.process p).pc ≠ .elected)
    (hd : ¬ LocalEnabled owner s p) :
    (s.inbox p = []) ∧
    ((s.process p).pc = .firstReceive ∨ (s.process p).pc = .secondReceive ∨
      (s.process p).pc = .relayReceive) := by
  have hl := hp.locals p
  have disabled (a : Action n) (ha : actProcess a = some p) :
      localStep (owner p) a (s.process p) (s.inbox p) = none := by
    cases hx : localStep (owner p) a (s.process p) (s.inbox p) with
    | none => rfl
    | some z =>
      exfalso
      apply hd
      refine ⟨a, commitLocal s p z, ha, ?_⟩
      cases a <;> simp_all [actProcess, lts, execute]
  cases hc : (s.process p).pc with
  | firstSend => simpa [localStep, hc] using disabled (.send p) rfl
  | secondSend =>
    simp only [LocalPlan, hc] at hl
    obtain ⟨r, _, _, _, _, hv⟩ := hl
    simpa [localStep, hc, hv] using disabled (.send p) rfl
  | relaySend => simpa [localStep, hc] using disabled (.send p) rfl
  | compare =>
    simp only [LocalPlan, hc] at hl
    obtain ⟨r, _, _, _, _, hv, hw⟩ := hl
    have hh := disabled (.compare p) rfl
    simp only [localStep, hc, hv, hw] at hh
    split at hh <;> contradiction
  | elected => exact (hne hc).elim
  | firstReceive | secondReceive | relayReceive =>
    have hh := disabled (.receive p) rfl
    cases hq : s.inbox p with
    | nil => simp
    | cons v rest => simp [localStep, hc, hq] at hh

namespace Execution
variable {owner : Fin n → Id}

def received (e : Execution owner) : Nat → Fin n → Nat
  | 0 => fun _ => 0
  | t + 1 => receivedAfter (e.received t) (e.action t)

end Execution

/-- Prefix induction keeps the actual receive ordinal at each time. -/
theorem execution_planned (e : Execution owner) (t : Nat) :
    Planned owner hn hi (e.state t) (e.received t) := by
  induction t with
  | zero =>
    rw [e.starts]
    refine ⟨?_, ?_, ?_⟩
    · simp [Execution.received, Counted, LocalCount, initial]
    · intro p
      refine ⟨0, rfl, rfl, ?_, rfl⟩
      exact ⟨p, rfl⟩
    · intro p
      trivial
  | succ t ih => exact step_planned owner hn hi ih (e.steps t)

/-- A returning FIFO head necessarily announces in all three receiving controls. -/
theorem receive_return_announces (s t : State n Id) (p : Fin n)
    (rc : Fin n → Nat) (hp : Planned owner hn hi s rc)
    (hv : inputAt owner hn hi p (rc p) = owner p)
    (ht : (lts owner).Tr s (.receive p) t) : Announced t := by
  change execute owner s (.receive p) = some t at ht
  simp only [execute, Option.map_eq_some_iff] at ht
  obtain ⟨z, hz, rfl⟩ := ht
  let prev := (finRotate n).symm p
  have he : next prev = p := by
    rw [← rotate_is_actual_next]
    exact (finRotate n).apply_symm_apply p
  have hq := hp.queues prev
  rw [he] at hq
  cases hpc : (s.process p).pc <;> cases hbox : s.inbox p <;>
    simp only [localStep, hpc, hbox] at hz <;> try contradiction
  all_goals
    rename_i v rest
    rw [hbox] at hq
    have hh : v = owner p := hq.1.symm.trans hv
    simp only [hh, ite_true, Option.some.injEq] at hz
    subst z
    exact ⟨p, by simp [commitLocal]⟩

/-- Without announcement, a returning occurrence cannot have been consumed. -/
theorem received_bound_of_return (e : Execution owner)
    (hno : ∀ t, ¬ Announced (e.state t)) (p : Fin n) (k : Nat)
    (hv : inputAt owner hn hi p k = owner p) : ∀ t, e.received t p ≤ k := by
  intro t
  induction t with
  | zero => simp [Execution.received]
  | succ t ih =>
    change receivedAfter (e.received t) (e.action t) p ≤ k
    cases ha : e.action t with
    | idle | deliver q | send q | compare q => simpa [receivedAfter] using ih
    | receive q =>
      by_cases hqp : p = q
      · subst q
        simp only [receivedAfter, Function.update_self]
        by_contra hb
        have he : e.received t p = k := by omega
        apply hno (t + 1)
        apply receive_return_announces owner hn hi _ _ p (e.received t)
          (execution_planned owner hn hi e t) (by simpa [he] using hv)
        simpa [ha] using e.steps t
      · simpa [receivedAfter, Function.update_of_ne hqp] using ih

/-- A bound on one sender spreads around the actual ring using FIFO counts. -/
theorem planned_sent_bound {s : State n Id} {rc : Fin n → Nat}
    (hp : Planned owner hn hi s rc) (hno : ¬ Announced s)
    (p : Fin n) (b : Nat) (hb : s.sent p ≤ b) : ∀ q, s.sent q ≤ b + n := by
  have hstep (q : Fin n) : s.sent (next q) ≤ s.sent q + 1 := by
    have hl := local_count_bounds (hp.counts.1 (next q)) (fun he => hno ⟨next q, he⟩)
    have hq := hp.counts.2 q
    omega
  have hit (k : Nat) : s.sent ((finRotate n)^[k] p) ≤ b + k := by
    induction k with
    | zero => simpa using hb
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have hh := hstep ((finRotate n)^[k] p)
      rw [← rotate_is_actual_next] at hh
      omega
  intro q
  let : NeZero n := ⟨by omega⟩
  let k : Fin n := q - p
  have he : (finRotate n)^[k.val] p = q := by
    rw [← finCycle_eq_finRotate_iterate, finCycle_apply]
    simp [k]
  have hh := hit k.val
  rw [he] at hh
  have hk := k.isLt
  omega

include hn hi in
/-- No announcement bounds all real sends; it does not assume fairness. -/
theorem nonannouncing_sends_bounded (e : Execution owner)
    (hno : ∀ t, ¬ Announced (e.state t)) :
    ∃ b, ∀ t p, (e.state t).sent p ≤ b := by
  obtain ⟨p, k, hv⟩ := planned_return_exists owner hn hi
  have hr := received_bound_of_return owner hn hi e hno p k hv
  refine ⟨k + 1 + n, ?_⟩
  intro t q
  have hp := execution_planned owner hn hi e t
  have hc := local_count_bounds (hp.counts.1 p) (fun he => hno t ⟨p, he⟩)
  exact planned_sent_bound owner hn hi hp (hno t) p (k + 1) (by have := hr t; omega) q

/-- Potential for actual actions: sends, receives, delivered inboxes and local control. -/
def progressMeasure (s : State n Id) (rc : Fin n → Nat) : Nat :=
  ∑ p, (3 * (s.sent p + rc p) + controlRank (s.process p).pc + (s.inbox p).length)

omit hn hi in
theorem local_inbox_count (p : Fin n) (a : Action n) (l : Local Id)
    (q : List Id) (z : Local Id × List Id × Option Id)
    (hs : localStep (owner p) a l q = some z) :
    z.2.1.length + (match a with | .receive _ => 1 | _ => 0) = q.length := by
  rcases l with ⟨pc, tid, ntid, nntid⟩
  cases a <;> cases pc <;> simp only [localStep] at hs <;> try contradiction
  all_goals try (split at hs)
  all_goals try (split at hs)
  all_goals try (split at hs)
  all_goals cases hs
  all_goals simp_all

omit hn hi [LinearOrder Id] in
theorem local_measure_commit (s : State n Id) (rc : Fin n → Nat) (p : Fin n)
    (z : Local Id × List Id × Option Id) (d : Nat)
    (hq : z.2.1.length + d = (s.inbox p).length)
    (hi : controlRank (s.process p).pc < 2 * (z.2.2.toList.length + d) + controlRank z.1.pc) :
    progressMeasure s rc <
      progressMeasure (commitLocal s p z) (Function.update rc p (rc p + d)) := by
  unfold progressMeasure
  have hs : ∀ i : Fin n,
      3 * (s.sent i + rc i) + controlRank (s.process i).pc + (s.inbox i).length ≤
      3 * ((commitLocal s p z).sent i + Function.update rc p (rc p + d) i) +
        controlRank ((commitLocal s p z).process i).pc + ((commitLocal s p z).inbox i).length := by
    intro i
    rcases z with ⟨l, q, out⟩
    cases out <;> by_cases he : i = p <;> simp_all [commitLocal]
    all_goals omega
  apply Finset.sum_lt_sum (fun i _ => hs i)
  refine ⟨p, Finset.mem_univ p, ?_⟩
  rcases z with ⟨l, q, out⟩
  cases out <;> simp_all [commitLocal]
  all_goals omega

omit hn hi in
/-- Every actual nonidle action increases the potential, including delivery. -/
theorem step_measure_increases {s t : State n Id} {rc : Fin n → Nat} {a : Action n}
    (ht : (lts owner).Tr s a t) (ha : a ≠ .idle) :
    progressMeasure s rc < progressMeasure t (receivedAfter rc a) := by
  change execute owner s a = some t at ht
  cases a with
  | idle => exact (ha rfl).elim
  | deliver p =>
    cases he : s.edge p with
    | nil => simp [execute, he] at ht
    | cons v rest =>
      simp only [execute, he, Option.some.injEq] at ht
      subst t
      unfold progressMeasure
      apply Finset.sum_lt_sum
      · intro i _
        by_cases hi : i = next p <;> simp [receivedAfter, Function.update, hi]
      · refine ⟨next p, Finset.mem_univ _, ?_⟩
        simp [receivedAfter]
  | send p | receive p | compare p =>
    simp only [execute, Option.map_eq_some_iff] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    have hm := local_measure_increases owner p _ _ _ _ hz
    have hq := local_inbox_count owner p _ _ _ _ hz
    have hh := local_measure_commit s rc p z _ hq hm
    all_goals simpa [receivedAfter] using hh

include hn hi in
/-- The potential is uniformly bounded throughout a nonannouncing execution. -/
theorem nonannouncing_measure_bounded (e : Execution owner)
    (hno : ∀ t, ¬ Announced (e.state t)) :
    ∃ b, ∀ t, progressMeasure (e.state t) (e.received t) ≤ b := by
  obtain ⟨b, hb⟩ := nonannouncing_sends_bounded owner hn hi e hno
  refine ⟨n * (3 * (b + (b + 1)) + 1 + b), ?_⟩
  intro t
  unfold progressMeasure
  calc
    _ ≤ ∑ _p : Fin n, (3 * (b + (b + 1)) + 1 + b) := by
      apply Finset.sum_le_sum
      intro p _
      have hp := execution_planned owner hn hi e t
      have hc := local_count_bounds (hp.counts.1 p) (fun he => hno t ⟨p, he⟩)
      have hsent := hb t p
      let prev := (finRotate n).symm p
      have he : next prev = p := by
        rw [← rotate_is_actual_next]
        exact (finRotate n).apply_symm_apply p
      have hq := hp.counts.2 prev
      rw [he] at hq
      have hs := hb t prev
      have hk : controlRank ((e.state t).process p).pc ≤ 1 := by
        cases ((e.state t).process p).pc <;> simp [controlRank]
      omega
    _ = _ := by simp

omit hn hi in
/-- Sent occurrences split exactly into delivered and still on the edge. -/
theorem execution_delivery_count (e : Execution owner) (t : Nat) (p : Fin n) :
    (e.state t).delivered p + ((e.state t).edge p).length = (e.state t).sent p := by
  induction t with
  | zero => simp [e.starts, initial]
  | succ t ih =>
    have ht := e.steps t
    change execute owner (e.state t) (e.action t) = some (e.state (t + 1)) at ht
    cases ha : e.action t with
    | idle =>
      simp only [ha, execute, Option.some.injEq] at ht
      exact ht ▸ ih
    | deliver q =>
      cases he : (e.state t).edge q with
      | nil => simp [execute, ha, he] at ht
      | cons v rest =>
        simp only [execute, ha, he, Option.some.injEq] at ht
        rw [← ht]
        by_cases hqp : p = q <;> simp_all
        omega
    | send q | receive q | compare q =>
      simp only [execute, ha, Option.map_eq_some_iff] at ht
      obtain ⟨z, _, hz⟩ := ht
      rw [← hz]
      clear hz
      rcases z with ⟨l, box, out⟩
      cases out <;> by_cases hpq : p = q <;> simp_all [commitLocal]
      all_goals omega

/-- A bounded natural-valued function attains a global maximum. -/
theorem bounded_nat_max (f : Nat → Nat) (b : Nat) (hb : ∀ t, f t ≤ b) :
    ∃ t, ∀ u, f u ≤ f t := by
  classical
  let P := fun k => ∃ t, f t = k
  have hex : P (Nat.findGreatest P b) := Nat.findGreatest_spec (hb 0) ⟨0, rfl⟩
  obtain ⟨t, ht⟩ := hex
  refine ⟨t, ?_⟩
  intro u
  rw [ht]
  by_contra hh
  exact Nat.findGreatest_is_greatest (P := P) (by omega) (hb u) ⟨u, rfl⟩

include hn hi in
/-- A permanently nonannouncing run must eventually use only idle actions. -/
theorem nonannouncing_stabilizes (e : Execution owner)
    (hno : ∀ t, ¬ Announced (e.state t)) :
    ∃ t, ∀ u, t ≤ u → e.state u = e.state t ∧ e.action u = .idle := by
  obtain ⟨b, hb⟩ := nonannouncing_measure_bounded owner hn hi e hno
  obtain ⟨t, ht⟩ := bounded_nat_max (fun t => progressMeasure (e.state t) (e.received t)) b hb
  have stay : ∀ u, t ≤ u → e.state u = e.state t ∧ e.received u = e.received t := by
    intro u hu
    induction u, hu using Nat.le_induction with
    | base => exact ⟨rfl, rfl⟩
    | succ u hu ih =>
      have ha : e.action u = .idle := by
        by_contra ha
        have hh := step_measure_increases owner (rc := e.received u) (e.steps u) ha
        change progressMeasure (e.state u) (e.received u) <
          progressMeasure (e.state (u + 1)) (e.received (u + 1)) at hh
        rw [ih.1, ih.2] at hh
        exact (not_lt_of_ge (ht (u + 1))) hh
      have hs := e.steps u
      change execute owner (e.state u) (e.action u) = some (e.state (u + 1)) at hs
      simp only [ha, execute, Option.some.injEq] at hs
      exact ⟨hs.symm.trans ih.1, by simpa [Execution.received, ha, receivedAfter] using ih.2⟩
  refine ⟨t, fun u hu => ⟨(stay u hu).1, ?_⟩⟩
  by_contra ha
  have hh := step_measure_increases owner (rc := e.received u) (e.steps u) ha
  change progressMeasure (e.state u) (e.received u) <
    progressMeasure (e.state (u + 1)) (e.received (u + 1)) at hh
  rw [(stay u hu).1, (stay u hu).2] at hh
  exact (not_lt_of_ge (ht (u + 1))) hh

/-- An initialized plan cannot be both locally blocked and empty on every edge.
The argument includes receivers in partially completed rounds. -/
theorem planned_not_deadlocked {s : State n Id} {rc : Fin n → Nat}
    (hp : Planned owner hn hi s rc) (hno : ¬ Announced s)
    (hedge : ∀ p, s.edge p = []) : ∃ p, LocalEnabled owner s p := by
  classical
  by_contra hh
  have hd : ∀ p, ¬ LocalEnabled owner s p := by simpa using hh
  have hr (p : Fin n) := planned_disabled owner hn hi hp p (fun he => hno ⟨p, he⟩) (hd p)
  have hle (p : Fin n) : rc p ≤ s.sent p := by
    have hc := hp.counts.1 p
    rcases (hr p).2 with he | he | he <;> simp only [LocalCount, he] at hc <;> omega
  have hfifo (p : Fin n) : s.sent p = rc (next p) := by
    simpa [hedge p, (hr (next p)).1] using hp.counts.2 p
  have hsum : ∑ p, s.sent p = ∑ p, rc p := by
    simp only [hfifo, ← rotate_is_actual_next]
    exact Equiv.sum_comp (finRotate n) rc
  have heq (p : Fin n) : rc p = s.sent p := by
    exact (Finset.sum_eq_sum_iff_of_le (fun q _ => hle q)).mp hsum.symm p (Finset.mem_univ p)
  have hrelay (p : Fin n) : (s.process p).pc = .relayReceive := by
    have hc := hp.counts.1 p
    have he := heq p
    rcases (hr p).2 with h | h | h
    · simp only [LocalCount, h] at hc
      omega
    · simp only [LocalCount, h] at hc
      omega
    · exact h
  let r := ∑ p : Fin n, rc p / 2
  have hbound (p : Fin n) : rc p / 2 ≤ r :=
    Finset.single_le_sum (f := fun p : Fin n => rc p / 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
  let f := frontierAt owner hn hi r
  let c : Fin f.size := ⟨0, f.positive⟩
  have ha : f.Active (f.physical c) := ⟨c, rfl⟩
  have hlocal := hp.locals (f.physical c)
  simp only [LocalPlan, hrelay] at hlocal
  exact hlocal.2 (frontier_active_decreases owner hn hi _ (hbound _) ha)

include hn hi in
/-- General conditional progress on the actual asynchronous FIFO LTS, under
exactly the accepted occurrence delivery and weak local fairness assumptions. -/
theorem eventual_election : EventualElection owner := by
  intro e hdelivery hlocal
  by_contra hh
  have hno : ∀ t, ¬ Announced (e.state t) := by simpa using hh
  obtain ⟨t, hstay⟩ := nonannouncing_stabilizes owner hn hi e hno
  have hedge (p : Fin n) : (e.state t).edge p = [] := by
    by_contra he
    have hc := execution_delivery_count owner e t p
    have hlen : 0 < ((e.state t).edge p).length := List.length_pos_iff.mpr he
    have hsent : (e.state t).delivered p < (e.state t).sent p := by omega
    obtain ⟨u, hu, hd⟩ := hdelivery p t ((e.state t).delivered p) hsent
    rw [(hstay u hu).1] at hd
    exact (Nat.lt_irrefl _) hd
  obtain ⟨p, hp⟩ := planned_not_deadlocked owner hn hi
    (execution_planned owner hn hi e t) (hno t) hedge
  obtain ⟨u, hu, ha⟩ := hlocal p t (fun u hu => by simpa [(hstay u hu).1] using hp)
  rw [(hstay u hu).2] at ha
  contradiction

/-- The unchanged correctness target combines independently checked safety and
conditional eventual election, for every positive ring and injective ownership. -/
theorem correct_election : CorrectElection := by
  intro n hn Id _ owner hi
  exact ⟨election_safety owner hn hi, eventual_election owner hn hi⟩

end CircularElection
