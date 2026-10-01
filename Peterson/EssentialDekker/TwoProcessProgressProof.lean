import Peterson.EssentialDekker.TwoProcessProgress

namespace Peterson.EssentialDekker.TwoProcess.Progress

theorem valid_certified {E : Execution} (h : Valid E) (n : Nat) : Certified (E.state n) := by
  induction n with
  | zero => obtain ⟨t, ht⟩ := h.1; rw [ht]; exact certificate_initial t
  | succ n ih =>
    rw [h.2 n]
    cases E.event n with
    | none => exact ih
    | some a => exact certificate_step _ a ih

theorem pc_next_other (s : State) (p a : Proc) (ha : a ≠ p) :
    (next s a).pc p = s.pc p := by
  rcases s with ⟨x,y,f,g,t⟩
  cases p <;> cases a <;> cases x <;> cases y <;>
    simp_all [next, State.pc, State.setPC, State.setFlag]

set_option maxHeartbeats 4000000 in
 theorem pending_next (s : State) (p a : Proc) : Pending s p →
    ¬ (s.pc p = .guardPeer ∧ s.flag (!p) = false ∧ a = p) → Pending (next s a) p := by
  unfold Pending
  rcases s with ⟨x,y,f,g,t⟩
  cases x <;> cases y <;> cases f <;> cases g <;> cases t <;> cases p <;> cases a <;> decide

theorem pending_succ {E : Execution} (h : Valid E) {p : Proc} {n : Nat}
    (hp : Pending (E.state n) p) (he : ¬ Entry E p n) : Pending (E.state (n+1)) p := by
  rw [h.2 n]
  cases ha : E.event n with
  | none => exact hp
  | some a =>
    apply pending_next _ p a hp
    intro ⟨hpc, hf, hap⟩
    exact he ⟨hpc, hf, by simpa [hap] using ha⟩

/-- Only the selected actor changes its private location. -/
theorem pc_succ_unselected {E : Execution} (h : Valid E) {p : Proc} {n : Nat}
    (ha : E.event n ≠ some p) : (E.state (n+1)).pc p = (E.state n).pc p := by
  rw [h.2 n]
  cases he : E.event n with
  | none => rfl
  | some a => exact pc_next_other _ p a (by intro heq; exact ha (by simpa [heq] using he))

/-- Fairness and critical completion together prevent permanent neglect of any
already active actor. They still impose no obligation on an idle client. -/
theorem active_eventually_selected {E : Execution} (h : Valid E)
    (hf : WeakProtocolFair E) (hc : CriticalCompletes E) {p : Proc} {n : Nat}
    (hp : (E.state n).pc p ≠ .idle) : ∃ k, n ≤ k ∧ E.event k = some p := by
  by_contra hn
  have hnever : ∀ k, n ≤ k → E.event k ≠ some p := by
    intro k hk he; exact hn ⟨k,hk,he⟩
  have hpc : ∀ k, n ≤ k → (E.state k).pc p = (E.state n).pc p := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih => exact (pc_succ_unselected h (hnever k hk)).trans ih
  by_cases hcrit : (E.state n).pc p = .critical
  · obtain ⟨k,hk,_,he⟩ := hc p n hcrit
    exact hnever k hk he
  · apply hn
    apply hf p n
    intro k hk
    exact ⟨by simpa [hpc k hk] using hp, by simpa [hpc k hk] using hcrit⟩

/-- A nonincreasing natural rank has a constant suffix. -/
theorem rank_stabilizes (r : Nat → Nat) (m : Nat)
    (hs : ∀ n, m ≤ n → r (n+1) ≤ r n) :
    ∃ k, m ≤ k ∧ ∀ n, k ≤ n → r n = r k := by
  classical
  have hex : ∃ v, ∃ n, m ≤ n ∧ r n = v := ⟨r m,m,le_rfl,rfl⟩
  obtain ⟨k,hk,hkr⟩ := Nat.find_spec hex
  refine ⟨k,hk,?_⟩
  intro n hn
  have hupper : r n ≤ r k := by
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact (hs n (by omega)).trans ih
  have hlower := Nat.find_min' hex (show ∃ j, m ≤ j ∧ r j = r n from ⟨n,by omega,rfl⟩)
  omega

/-- Every pending request eventually takes its own entry step. -/
theorem pending_eventually_entry {E : Execution} (h : Valid E)
    (hf : WeakProtocolFair E) (hc : CriticalCompletes E) {p : Proc} {m : Nat}
    (hp : Pending (E.state m) p) : ∃ n, m ≤ n ∧ Entry E p n := by
  by_contra hno
  have hne : ∀ n, m ≤ n → ¬ Entry E p n := by
    intro n hn he; exact hno ⟨n,hn,he⟩
  have hpend : ∀ n, m ≤ n → Pending (E.state n) p := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hp
    | succ n hn ih => exact pending_succ h ih (hne n hn)
  have hdesc : ∀ n, m ≤ n →
      rank (E.state (n+1)) p ≤ rank (E.state n) p ∧
      (rank (E.state (n+1)) p = rank (E.state n) p →
        blocker (E.state (n+1)) p = blocker (E.state n) p ∧
        E.event n ≠ some (blocker (E.state n) p)) := by
    intro n hn
    have hpn := hpend (n+1) (by omega)
    rw [h.2 n] at hpn ⊢
    cases he : E.event n with
    | none => simp
    | some a =>
      simp only [he] at hpn ⊢
      obtain ⟨hr,hb⟩ := certificate_descent _ p a (valid_certified h n) (hpend n hn) hpn
      refine ⟨hr, fun heq => ?_⟩
      obtain ⟨hb,ha⟩ := hb heq
      exact ⟨hb, fun heq => ha (Option.some.inj heq)⟩
  obtain ⟨k,hk,hstable⟩ := rank_stabilizes (fun n => rank (E.state n) p) m
    (fun n hn => (hdesc n hn).1)
  have hb : ∀ n, k ≤ n → blocker (E.state n) p = blocker (E.state k) p := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      have heq : rank (E.state (n+1)) p = rank (E.state n) p :=
        (hstable _ (by omega)).trans (hstable n hn).symm
      exact ((hdesc n (by omega)).2 heq).1.trans ih
  obtain ⟨n,hn,he⟩ := active_eventually_selected h hf hc
    (certificate_active _ p (valid_certified h k) (hpend k hk))
  have heq : rank (E.state (n+1)) p = rank (E.state n) p :=
    (hstable _ (by omega)).trans (hstable n hn).symm
  exact ((hdesc n (by omega)).2 heq).2 (by simpa only [hb n hn] using he)

/-- The private request starts a pending passage even though its flag is false. -/
theorem request_pending {E : Execution} (h : Valid E) {p : Proc} {n : Nat}
    (hr : Request E p n) : Pending (E.state (n+1)) p := by
  rw [h.2 n,hr.2]
  simp only [next,hr.1]
  cases p <;> simp [Pending, State.setPC, State.pc]

/-- No new request can start while this one remains pending. -/
theorem pending_not_request {E : Execution} {p : Proc} {n : Nat}
    (hp : Pending (E.state n) p) : ¬ Request E p n := by
  intro hr
  simp [Pending,hr.1] at hp

/-- Every private request has a matching entry, with the same request pending
throughout the intervening states. Either initial turn and repeated peers are covered. -/
theorem request_eventually_entry {E : Execution} (h : Valid E)
    (hf : WeakProtocolFair E) (hc : CriticalCompletes E) {p : Proc} {r : Nat}
    (hr : Request E p r) :
    ∃ n, r < n ∧ Entry E p n ∧
      ∀ k, r < k → k ≤ n → Pending (E.state k) p := by
  classical
  have hex := pending_eventually_entry h hf hc (request_pending h hr)
  let n := Nat.find hex
  have hn := Nat.find_spec hex
  have hinterval : ∀ k, r+1 ≤ k → k ≤ n → Pending (E.state k) p := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; exact request_pending h hr
    | succ k hk ih =>
      intro hkn
      apply pending_succ h (ih (by omega))
      intro he
      have hl := Nat.find_min' hex (show r+1 ≤ k ∧ Entry E p k from ⟨hk,he⟩)
      change n ≤ k at hl
      omega
  exact ⟨n,by omega,hn.2,fun k hk hkn => hinterval k (by omega) hkn⟩

end Peterson.EssentialDekker.TwoProcess.Progress

#print axioms Peterson.EssentialDekker.TwoProcess.Progress.request_eventually_entry
