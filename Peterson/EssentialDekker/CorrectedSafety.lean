import Peterson.EssentialDekker.Corrected

/-! Repeated mutual exclusion for the reviewed ≥-corrected Figure 6.
The proof uses the final guard scan, not a lower-level capacity bound.
See the collection’s Essential Dekker guide for the final-scan argument. -/
namespace Peterson.EssentialDekker.Corrected.Safety

variable {m : Nat} {s : State m}

/-- Zero-based position of a distinct peer in the ascending scan. -/
def rank (p q : Proc m) : Nat := if q.val < p.val then q.val else q.val - 1

/-- Guard scans retain their own level flag; occupants retain the final flag. -/
def Holds (s : State m) : Prop := ∀ p,
  match s.pc p with
  | .scan j true _ _ => (s.flag p).val = j.val + 1
  | .critical | .exit => (s.flag p).val = m + 1
  | _ => True

/-- The final guard scan has passed this peer with count still zero, or the
actor has completed that scan and has not yet cleared its flag on exit. -/
def Cleared (s : State m) (p q : Proc m) : Prop :=
  match s.pc p with
  | .scan j true c count => j.val = m ∧ count = 0 ∧ rank p q < c.val
  | .critical | .exit => True
  | _ => False

/-- Two distinct actors have not both cleared one another. -/
def Ordered (s : State m) : Prop := ∀ p q, p ≠ q → ¬ (Cleared s p q ∧ Cleared s q p)

theorem rank_lt (p q : Proc m) (h : p ≠ q) : rank p q < m + 1 := by
  have hp := p.isLt
  have hq := q.isLt
  have hn : p.val ≠ q.val := fun e => h (Fin.ext e)
  unfold rank
  split <;> omega

theorem rank_eq (p q : Proc m) (c : Level m) (h : p ≠ q)
    (he : rank p q = c.val) : q = peer p c := by
  have hn : p.val ≠ q.val := fun e => h (Fin.ext e)
  apply Fin.ext
  unfold rank at he
  unfold peer
  split <;> split at he <;> simp only <;> omega

theorem holds_initial : Holds (initial m) := by simp [Holds, initial]

theorem pc_other (a p : Proc m) (h : p ≠ a) : (next s a).pc p = s.pc p := by
  cases hp : s.pc a <;> simp [next, hp, State.setPC, Function.update, h]

theorem flag_other (a p : Proc m) (h : p ≠ a) : (next s a).flag p = s.flag p := by
  cases hp : s.pc a <;> simp [next, hp, State.setPC, Function.update, h]

theorem holds_next (hs : Holds s) (a : Proc m) : Holds (next s a) := by
  intro p
  by_cases h : p = a
  · subst p
    have ha := hs a
    cases hp : s.pc a
    all_goals try (rename_i j guard c count; cases guard)
    all_goals simp only [next, hp, State.setPC, Function.update]
    all_goals simp only [hp] at ha
    all_goals simp only [Holds] at *
    all_goals split_ifs <;> simp_all [passed]
    all_goals try (split_ifs <;> simp_all)
    all_goals omega
  · rw [pc_other a p h, flag_other a p h]
    exact hs p

theorem cleared_flag (hs : Holds s) {p q : Proc m} (hc : Cleared s p q) :
    (s.flag p).val = m + 1 := by
  have hh := hs p
  cases hp : s.pc p <;> simp_all [Cleared]
  rename_i j g c k
  cases g <;> simp_all

theorem cleared_other (a p q : Proc m) (h : p ≠ a) :
    Cleared (next s a) p q ↔ Cleared s p q := by
  simp only [Cleared, pc_other a p h]

/-- A peer holding its top flag cannot be newly cleared by one actor step. -/
theorem cleared_next (a q : Proc m) (hne : a ≠ q)
    (hf : (s.flag q).val = m + 1) (hc : Cleared (next s a) a q) :
    Cleared s a q := by
  have hr := rank_lt a q hne
  cases hp : s.pc a
  all_goals try (rename_i j guard c count; cases guard)
  all_goals simp only [Cleared, next, hp, State.setPC, Function.update] at hc ⊢
  all_goals split_ifs at hc <;> simp_all [passed]
  all_goals try (split_ifs at hc <;> simp_all)
  all_goals
    have hj := j.isLt
    have hci := c.isLt
    try omega
  all_goals
    have hn : rank a q ≠ c.val := by
      intro he
      have heq := rank_eq a q c hne he
      have hf' : (s.flag (peer a c)).val = m + 1 := by rw [← heq]; exact hf
      omega
    omega

theorem ordered_initial : Ordered (initial m) := by simp [Ordered, Cleared, initial]

theorem ordered_next (hf : Holds s) (ho : Ordered s) (a : Proc m) :
    Ordered (next s a) := by
  intro p q hne ⟨hp, hq⟩
  by_cases hpa : p = a
  · subst p
    have hq' := (cleared_other a q a hne.symm).mp hq
    exact ho a q hne ⟨cleared_next a q hne (cleared_flag hf hq') hp, hq'⟩
  · have hp' := (cleared_other a p q hpa).mp hp
    by_cases hqa : q = a
    · subst q
      exact ho p a hne ⟨hp', cleared_next a p hne.symm (cleared_flag hf hp') hq⟩
    · exact ho p q hne ⟨hp', (cleared_other a q p hqa).mp hq⟩

/-- Finite reachability under the existing source-close actor transition. -/
inductive Reachable : State m → Prop where
  | initial : Reachable (initial m)
  | step {s : State m} (reachable : Reachable s) (a : Proc m) : Reachable (next s a)

theorem invariant (h : Reachable s) : Holds s ∧ Ordered s := by
  induction h with
  | initial => exact ⟨holds_initial, ordered_initial⟩
  | step _ a ih => exact ⟨holds_next ih.1 a, ordered_next ih.1 ih.2 a⟩

/-- Every reachable state has at most one critical-section occupant, for all n=m+2.
No fairness or progress premise is used. -/
theorem mutual_exclusion (h : Reachable s) (p q : Proc m)
    (hp : s.pc p = .critical) (hq : s.pc q = .critical) : p = q := by
  by_contra hne
  exact (invariant h).2 p q hne ⟨by simp [Cleared, hp], by simp [Cleared, hq]⟩

theorem run_reachable (actors : List (Proc m)) : Reachable (run (initial m) actors) := by
  suffices ∀ (t : State m), Reachable t → Reachable (run t actors) from this _ .initial
  induction actors with
  | nil => intro t ht; exact ht
  | cons a rest ih => intro t ht; exact ih (next t a) (.step ht a)

/-- The explicit finite-schedule form of arbitrary-process repeated safety. -/
theorem run_mutual_exclusion (actors : List (Proc m)) (p q : Proc m)
    (hp : (run (initial m) actors).pc p = .critical)
    (hq : (run (initial m) actors).pc q = .critical) : p = q :=
  mutual_exclusion (run_reachable actors) p q hp hq

#print axioms mutual_exclusion
#print axioms run_mutual_exclusion

end Peterson.EssentialDekker.Corrected.Safety
