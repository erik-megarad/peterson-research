module
public import CircularElection.Frontier

/-! Local occurrence plans for the actual asynchronous protocol. -/
@[expose] public section
namespace CircularElection
variable {n : Nat} {Id : Type} [LinearOrder Id]
variable (owner : Fin n → Id) (hn : 0 < n) (hi : Function.Injective owner)

def frontierAt : Nat → Frontier owner
  | 0 => Frontier.first owner hn
  | r + 1 => (frontierAt r).advance hi

def inputAt (p : Fin n) (k : Nat) : Id :=
  if k % 2 = 0 then (frontierAt owner hn hi (k / 2)).incomingEven p
  else (frontierAt owner hn hi (k / 2)).incomingOdd p

theorem inputAt_even (p : Fin n) (r : Nat) :
    inputAt owner hn hi p (2 * r) = (frontierAt owner hn hi r).incomingEven p := by
  simp [inputAt]

theorem inputAt_odd (p : Fin n) (r : Nat) :
    inputAt owner hn hi p (2 * r + 1) = (frontierAt owner hn hi r).incomingOdd p := by
  have hdiv : (2 * r + 1) / 2 = r := by omega
  have hmod : (2 * r + 1) % 2 = 1 := by omega
  simp [inputAt, hdiv, hmod]

theorem inputAt_return (p : Fin n) (k : Nat) (he : inputAt owner hn hi p k = owner p) :
    IsMaximum owner p := by
  apply (frontierAt owner hn hi (k / 2)).incoming_return_maximum hi p
  unfold inputAt at he
  split at he
  · exact Or.inl he
  · exact Or.inr he

theorem frontier_active_decreases (p : Fin n) {r s : Nat} (hrs : r ≤ s)
    (ha : (frontierAt owner hn hi s).Active p) : (frontierAt owner hn hi r).Active p := by
  induction s, hrs using Nat.le_induction with
  | base => exact ha
  | succ s hrs ih =>
    apply ih
    exact ((frontierAt owner hn hi s).advance_active hi p).mp ha |>.1

/-- Each local process follows its own ordinal; there is no shared round clock.
Unused registers are unconstrained, and elected states record only safety. -/
def LocalPlan (p : Fin n) (sent received : Nat) (l : Local Id) : Prop :=
  match l.pc with
  | .firstSend => ∃ r, sent = 2 * r ∧ received = 2 * r ∧
      (frontierAt owner hn hi r).Active p ∧
      l.tid = (frontierAt owner hn hi r).candidate ((frontierAt owner hn hi r).block p)
  | .firstReceive => ∃ r, sent = 2 * r + 1 ∧ received = 2 * r ∧
      (frontierAt owner hn hi r).Active p ∧
      l.tid = (frontierAt owner hn hi r).candidate ((frontierAt owner hn hi r).block p)
  | .secondSend => ∃ r, sent = 2 * r + 1 ∧ received = 2 * r + 1 ∧
      (frontierAt owner hn hi r).Active p ∧
      l.tid = (frontierAt owner hn hi r).candidate ((frontierAt owner hn hi r).block p) ∧
      l.ntid = some ((frontierAt owner hn hi r).incomingEven p)
  | .secondReceive => ∃ r, sent = 2 * r + 2 ∧ received = 2 * r + 1 ∧
      (frontierAt owner hn hi r).Active p ∧
      l.tid = (frontierAt owner hn hi r).candidate ((frontierAt owner hn hi r).block p) ∧
      l.ntid = some ((frontierAt owner hn hi r).incomingEven p)
  | .compare => ∃ r, sent = 2 * r + 2 ∧ received = 2 * r + 2 ∧
      (frontierAt owner hn hi r).Active p ∧
      l.tid = (frontierAt owner hn hi r).candidate ((frontierAt owner hn hi r).block p) ∧
      l.ntid = some ((frontierAt owner hn hi r).incomingEven p) ∧
      l.nntid = some ((frontierAt owner hn hi r).incomingOdd p)
  | .relayReceive => sent = received ∧ ¬ (frontierAt owner hn hi (received / 2)).Active p
  | .relaySend => sent + 1 = received ∧ ¬ (frontierAt owner hn hi (sent / 2)).Active p ∧
      l.tid = inputAt owner hn hi p sent
  | .elected => IsMaximum owner p

theorem inputAt_relay_edge (p : Fin n) (k : Nat)
    (ha : ¬ (frontierAt owner hn hi (k / 2)).Active p) :
    inputAt owner hn hi (next p) k = inputAt owner hn hi p k := by
  unfold inputAt
  split
  · rw [Frontier.even_edge, ite_eq_right ha]
  · rw [Frontier.odd_edge, ite_eq_right ha]

theorem inputAt_active_even (p : Fin n) (r : Nat)
    (ha : (frontierAt owner hn hi r).Active p) :
    inputAt owner hn hi (next p) (2 * r) =
      (frontierAt owner hn hi r).candidate ((frontierAt owner hn hi r).block p) := by
  rw [inputAt_even, Frontier.even_edge, ite_eq_left ha]

theorem inputAt_active_odd (p : Fin n) (r : Nat)
    (ha : (frontierAt owner hn hi r).Active p) :
    inputAt owner hn hi (next p) (2 * r + 1) =
      max ((frontierAt owner hn hi r).candidate ((frontierAt owner hn hi r).block p))
        ((frontierAt owner hn hi r).incomingEven p) := by
  rw [inputAt_odd, Frontier.odd_edge, ite_eq_left ha]

/-- Local instructions preserve the ordinal plan and emit its exact next
value. A successful receive is supplied its actual FIFO-head value. -/
theorem local_plan_step (p : Fin n) (a : Action n) (l : Local Id) (q : List Id)
    (r : Local Id × List Id × Option Id) (sent received : Nat)
    (hp : LocalPlan owner hn hi p sent received l)
    (hq : ∀ v rest, q = v :: rest → inputAt owner hn hi p received = v)
    (hs : localStep (owner p) a l q = some r) :
    LocalPlan owner hn hi p (sent + r.2.2.toList.length)
      (received + (match a with | .receive _ => 1 | _ => 0)) r.1 ∧
    (∀ v, r.2.2 = some v → inputAt owner hn hi (next p) sent = v) ∧
    r.2.1.length + (match a with | .receive _ => 1 | _ => 0) = q.length := by
  rcases l with ⟨pc, tid, ntid, nntid⟩
  cases a with
  | idle | deliver _ => simp [localStep] at hs
  | send z =>
    cases pc <;> simp only [localStep] at hs <;> try contradiction
    case firstSend =>
      obtain ⟨k, hsent, hrecv, ha, ht⟩ := hp
      simp only at ht
      cases hs
      refine ⟨?_, ?_, by simp⟩
      · exact ⟨k, by simpa [LocalPlan, hsent, hrecv] using And.intro ha ht⟩
      · intro v hv
        cases hv
        simpa [hsent, ht] using inputAt_active_even owner hn hi p k ha
    case secondSend =>
      obtain ⟨k, hsent, hrecv, ha, ht, hnt⟩ := hp
      simp only at ht hnt
      simp only [hnt] at hs
      cases hs
      refine ⟨?_, ?_, by simp⟩
      · refine ⟨k, ?_, ?_, ha, ht, rfl⟩ <;> simp [hsent, hrecv, Nat.add_assoc]
      · intro v hv
        cases hv
        simpa [hsent, ht] using inputAt_active_odd owner hn hi p k ha
    case relaySend =>
      obtain ⟨hc, ha, ht⟩ := hp
      cases hs
      refine ⟨?_, ?_, by simp⟩
      · change sent + 1 = received + 0 ∧
          ¬ (frontierAt owner hn hi ((received + 0) / 2)).Active p
        refine ⟨by omega, ?_⟩
        intro hactive
        exact ha (frontier_active_decreases owner hn hi p (by omega) hactive)
      · intro v hv
        cases hv
        rw [inputAt_relay_edge owner hn hi p sent ha, ← ht]
  | receive z =>
    cases pc <;> cases q <;> simp only [localStep] at hs <;> try contradiction
    case firstReceive.cons v rest =>
      obtain ⟨k, hsent, hrecv, ha, ht⟩ := hp
      have hv : (frontierAt owner hn hi k).incomingEven p = v := by
        simpa [hrecv, inputAt_even] using hq v rest rfl
      split at hs
      · rename_i he
        cases hs
        refine ⟨?_, ?_, by simp⟩
        · exact (frontierAt owner hn hi k).incoming_return_maximum hi p (Or.inl (hv.trans he))
        · simp
      · cases hs
        refine ⟨?_, ?_, by simp⟩
        · refine ⟨k, ?_, ?_, ha, ht, ?_⟩ <;> simp [hsent, hrecv, hv]
        · simp
    case secondReceive.cons v rest =>
      obtain ⟨k, hsent, hrecv, ha, ht, hnt⟩ := hp
      have hv : (frontierAt owner hn hi k).incomingOdd p = v := by
        simpa [hrecv, inputAt_odd] using hq v rest rfl
      split at hs
      · rename_i he
        cases hs
        refine ⟨?_, ?_, by simp⟩
        · exact (frontierAt owner hn hi k).incoming_return_maximum hi p (Or.inr (hv.trans he))
        · simp
      · cases hs
        refine ⟨?_, ?_, by simp⟩
        · refine ⟨k, ?_, ?_, ha, ht, hnt, ?_⟩ <;> simp [hsent, hrecv, hv, Nat.add_assoc]
        · simp
    case relayReceive.cons v rest =>
      obtain ⟨hc, ha⟩ := hp
      have hv := hq v rest rfl
      split at hs
      · rename_i he
        cases hs
        refine ⟨?_, ?_, by simp⟩
        · exact inputAt_return owner hn hi p received (hv.trans he)
        · simp
      · cases hs
        refine ⟨?_, ?_, by simp⟩
        · change sent + 0 + 1 = received + 1 ∧
            ¬ (frontierAt owner hn hi ((sent + 0) / 2)).Active p ∧
            v = inputAt owner hn hi p (sent + 0)
          refine ⟨by omega, ?_, ?_⟩
          · simpa [hc] using ha
          · simpa [hc] using hv.symm
        · simp
  | compare z =>
    cases pc <;> simp only [localStep] at hs <;> try contradiction
    obtain ⟨k, hsent, hrecv, ha, ht, hnt, hnnt⟩ := hp
    simp only at ht hnt hnnt
    simp only [ht, hnt, hnnt] at hs
    split at hs
    · rename_i hsurvive
      have hs' : RoundSurvives (frontierAt owner hn hi k).candidate
          (finRotate (frontierAt owner hn hi k).size).symm ((frontierAt owner hn hi k).block p) := by
        apply (Frontier.comparison_is_survival _ p).mp
        simpa [ht] using hsurvive
      have hactive : (frontierAt owner hn hi (k + 1)).Active p :=
        (Frontier.advance_active _ hi p).mpr ⟨ha, hs'⟩
      have hcandidate := (frontierAt owner hn hi k).advance_candidate hi p hactive
      cases hs
      refine ⟨?_, ?_, by simp⟩
      · refine ⟨k + 1, ?_, ?_, hactive, ?_⟩
        · simp [hsent]; omega
        · simp [hrecv]; omega
        · exact hcandidate.symm
      · simp
    · rename_i hfail
      have hnot : ¬ (frontierAt owner hn hi (k + 1)).Active p := by
        intro hactive
        have hsurvive := (Frontier.advance_active _ hi p).mp hactive |>.2
        have htest := (Frontier.comparison_is_survival _ p).mpr hsurvive
        exact hfail (by simpa [ht] using htest)
      cases hs
      refine ⟨?_, ?_, by simp⟩
      · change sent + 0 = received + 0 ∧
          ¬ (frontierAt owner hn hi ((received + 0) / 2)).Active p
        have hd : (2 * k + 2) / 2 = k + 1 := by omega
        refine ⟨by omega, ?_⟩
        simpa [hrecv, hd] using hnot
      · simp

end CircularElection
