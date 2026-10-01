import Peterson.EconomicalSolutions.Algorithm1ProgressCertificate
import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-! Theorem 3-1: per-request progress despite unrestricted peer failures.
The finite certificate supplies local rank obligations; this proof quantifies
all infinite initialized executions and uses only the reviewed fairness. -/
namespace EconomicalSolutions.Algorithm1

theorem Run.omega_execution (r : Run) : lts.OmegaExecution r.state r.event := by
  intro n
  exact ⟨r.command n, r.valid n, rfl⟩

theorem Run.invariant (r : Run) (n : Nat) : Invariant (r.state n) := by
  induction n with
  | zero => rw [r.initialized]; exact invariant_initial
  | succ n ih => exact invariant_next ih (r.valid n)

/-- A pending passage cannot be replaced by a new request. -/
theorem pending_not_request (s : State) (c : Command) (p : Proc)
    (hp : Pending s p) : label s c ≠ .request p := by
  cases c with
  | run q =>
    by_cases hqp : q = p
    · subst q
      cases hpc : (s.local p).pc <;> simp_all [label, Pending, pendingPC]
    · cases hpc : (s.local q).pc <;> simp [label, hpc, hqp]
  | fail q => simp [label]
  | restart q => simp [label]
  | stutter => simp [label]

theorem every_progress_state_checked (p : Proc) (s : State) :
    checkProgressState p s = true := by
  have hp : p ∈ [false, true] := by cases p <;> decide
  have a := List.all_eq_true.mp progress_certificate_checked p hp
  have b := List.all_eq_true.mp a s.p0 (allLocals_complete s.p0)
  exact List.all_eq_true.mp b s.p1 (allLocals_complete s.p1)

theorem progress_obligations {p : Proc} {s : State}
    (hi : Invariant s) (hp : Pending s p) :
    owedPC (s.local (progressActor p s)).pc = true ∧
    ∀ c t, next s c = some t → outcome s c p = false →
      Pending t p ∧ progressRank p t ≤ progressRank p s ∧
      (progressRank p t = progressRank p s → progressActor p t = progressActor p s) ∧
      (acts c (progressActor p s) = true → progressRank p t < progressRank p s) := by
  have h := every_progress_state_checked p s
  have hi' : invariantB s = true := hi
  have hp' : pendingPC (s.local p).pc = true := hp
  simp only [checkProgressState, hi', hp', Bool.true_and, Bool.not_true, Bool.false_or,
    Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  intro c t he ho
  have hc := List.all_eq_true.mp h.2 c (allCommands_complete c)
  simp only [he, ho, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, beq_iff_eq] at hc
  exact ⟨hc.1.1.1, hc.1.1.2, fun hEq => hc.1.2.resolve_left (not_not_intro hEq),
    fun ha => hc.2.resolve_left (by simp [ha])⟩

/-- Completion/failure labels can only be produced by the indicated actor. -/
theorem completion_acts (s : State) (c : Command) (p : Proc)
    (h : label s c = .complete p ∨ label s c = .fail p) : acts c p = true := by
  cases c with
  | run q =>
    cases hpc : (s.local q).pc <;> simp_all [label, acts]
  | fail q => simp_all [label, acts]
  | restart q => simp_all [label]
  | stutter => simp_all [label]

theorem owed_eventually_acts (r : Run) (hf : ProtocolScheduling r)
    (hc : CriticalCompletion r) {n : Nat} {p : Proc}
    (h : owedPC ((r.state n).local p).pc = true) :
    ∃ m, n ≤ m ∧ acts (r.command m) p = true := by
  simp only [owedPC, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with hp | hp
  · exact hf n p hp
  · obtain ⟨m, hm, he⟩ := hc n p hp
    exact ⟨m, hm, completion_acts _ _ _ he⟩

/-- Natural ranks cannot decrease forever, even with unbounded delays. -/
theorem progress_rank_stabilizes (f : Nat → Nat) (start : Nat)
    (h : ∀ n, start ≤ n → f (n + 1) ≤ f n) :
    ∃ k, start ≤ k ∧ ∀ n, k ≤ n → f n = f k := by
  classical
  have hex : ∃ v, ∃ n, start ≤ n ∧ f n = v := ⟨f start, start, le_rfl, rfl⟩
  obtain ⟨k, hk, hkr⟩ := Nat.find_spec hex
  refine ⟨k, hk, ?_⟩
  intro n hn
  have upper : f n ≤ f k := by
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact (h n (by omega)).trans ih
  have lower := Nat.find_min' hex (show ∃ j, start ≤ j ∧ f j = f n from ⟨n, by omega, rfl⟩)
  omega

/-- Entry-or-own-failure, without any non-failure premise on either actor. -/
theorem pending_eventually_outcome (r : Run) (hf : ProtocolScheduling r)
    (hc : CriticalCompletion r) {p : Proc} {start : Nat}
    (hp : Pending (r.state start) p) :
    ∃ finish, start ≤ finish ∧ outcome (r.state finish) (r.command finish) p = true := by
  by_contra hn
  have never : ∀ n, start ≤ n → outcome (r.state n) (r.command n) p = false := by
    intro n hle
    cases he : outcome (r.state n) (r.command n) p
    · rfl
    · exact False.elim (hn ⟨n, hle, he⟩)
  have pending : ∀ n, start ≤ n → Pending (r.state n) p := by
    intro n hle
    induction n, hle using Nat.le_induction with
    | base => exact hp
    | succ n hle ih =>
      exact ((progress_obligations (r.invariant n) ih).2 _ _ (r.valid n) (never n hle)).1
  have desc n (hle : start ≤ n) :=
    (progress_obligations (r.invariant n) (pending n hle)).2 _ _ (r.valid n) (never n hle)
  obtain ⟨k, hk, stable⟩ := progress_rank_stabilizes (fun n => progressRank p (r.state n)) start
    (fun n hn => (desc n hn).2.1)
  have actor : ∀ n, k ≤ n → progressActor p (r.state n) = progressActor p (r.state k) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      exact ((desc n (by omega)).2.2.1 ((stable (n+1) (by omega)).trans
        (stable n hn).symm)).trans ih
  obtain ⟨n, hn, acted⟩ := owed_eventually_acts r hf hc
    (progress_obligations (r.invariant k) (pending k hk)).1
  have acted' : acts (r.command n) (progressActor p (r.state n)) = true := by
    simpa [actor n hn] using acted
  have strict := (desc n (by omega)).2.2.2 acted'
  have a := stable n hn
  have b := stable (n+1) (by omega)
  omega

/-- A first outcome resolves the same request, before replacement can occur. -/
theorem pending_first_outcome (r : Run) (hf : ProtocolScheduling r)
    (hc : CriticalCompletion r) {p : Proc} {start : Nat}
    (hp : Pending (r.state start) p) :
    ∃ finish, start ≤ finish ∧
      (r.event finish = .entry p ∨ r.event finish = .fail p) ∧
      ∀ k, start ≤ k → k < finish →
        Pending (r.state k) p ∧ r.event k ≠ .fail p ∧ r.event k ≠ .entry p := by
  classical
  have hex := pending_eventually_outcome r hf hc hp
  let finish := Nat.find hex
  have hfin := Nat.find_spec hex
  have before : ∀ k, start ≤ k → k < finish →
      outcome (r.state k) (r.command k) p = false := by
    intro k hk hlt
    cases he : outcome (r.state k) (r.command k) p
    · rfl
    · have := Nat.find_min' hex (show start ≤ k ∧ outcome (r.state k) (r.command k) p = true from ⟨hk, he⟩)
      omega
  refine ⟨finish, hfin.1, ?_, ?_⟩
  · simpa [outcome, Run.event, finish] using hfin.2
  · intro k hk hlt
    have hpend : Pending (r.state k) p := by
      induction k, hk using Nat.le_induction with
      | base => exact hp
      | succ k hk ih =>
        exact ((progress_obligations (r.invariant k) (ih (by omega))).2 _ _
          (r.valid k) (before k hk (by omega))).1
    have hb := before k hk hlt
    simp only [outcome, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hb
    exact ⟨hpend, hb.2, hb.1⟩

/-- Theorem 3-1: every non-failing pending requester takes its own matching entry.
The peer has no failure bound, eventual stability, or participation premise. -/
theorem per_request_progress (r : Run) (hf : ProtocolScheduling r)
    (hc : CriticalCompletion r) {p : Proc} {start : Nat}
    (hp : Pending (r.state start) p)
    (noFailure : ∀ k, start ≤ k → r.event k ≠ .fail p) :
    ∃ finish, Served r p start finish := by
  obtain ⟨finish, hle, he, hb⟩ := pending_first_outcome r hf hc hp
  exact ⟨finish, hle, he.resolve_right (noFailure finish hle), hb⟩

theorem Served.no_replacement {r : Run} {p : Proc} {start finish k : Nat}
    (hs : Served r p start finish) (hk : start ≤ k) (hlt : k < finish) :
    r.event k ≠ .request p :=
  pending_not_request _ _ _ (hs.2.2 k hk hlt).1

/-- If some pending requester does not fail, some new entry occurs. -/
theorem deadlock_freedom (r : Run) (hf : ProtocolScheduling r)
    (hc : CriticalCompletion r) {start : Nat}
    (requester : ∃ p, Pending (r.state start) p ∧
      ∀ k, start ≤ k → r.event k ≠ .fail p) :
    ∃ finish p, start ≤ finish ∧ r.event finish = .entry p := by
  obtain ⟨p, hp, hnf⟩ := requester
  obtain ⟨finish, hs⟩ := per_request_progress r hf hc hp hnf
  exact ⟨finish, p, hs.1, hs.2.1⟩

end EconomicalSolutions.Algorithm1

#print axioms EconomicalSolutions.Algorithm1.pending_first_outcome
#print axioms EconomicalSolutions.Algorithm1.per_request_progress
#print axioms EconomicalSolutions.Algorithm1.deadlock_freedom
