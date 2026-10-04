module

public import CircularElection.Model

@[expose] public section
namespace CircularElection
variable {n : Nat} {Id : Type} [LinearOrder Id]

def LocalOrigin (P : Id → Prop) (l : Local Id) : Prop :=
  P l.tid ∧ (∀ v ∈ l.ntid, P v) ∧ (∀ v ∈ l.nntid, P v)

def DataOrigin (P : Id → Prop) (s : State n Id) : Prop :=
  (∀ p, LocalOrigin P (s.process p)) ∧
  (∀ p v, v ∈ s.edge p → P v) ∧ (∀ p v, v ∈ s.inbox p → P v)

private theorem max_origin (P : Id → Prop) {x y : Id} (hx : P x) (hy : P y) :
    P (max x y) := by
  rcases le_total x y with h | h
  · simpa [max_eq_right h] using hy
  · simpa [max_eq_left h] using hx

private theorem local_origin (P : Id → Prop) (owner : Id) (a : Action n)
    (l : Local Id) (q : List Id) (r : Local Id × List Id × Option Id)
    (hl : LocalOrigin P l) (hq : ∀ v ∈ q, P v)
    (h : localStep owner a l q = some r) :
    LocalOrigin P r.1 ∧ (∀ v ∈ r.2.1, P v) ∧ (∀ v ∈ r.2.2, P v) := by
  rcases l with ⟨pc, tid, ntid, nntid⟩
  simp only [LocalOrigin] at hl
  cases a <;> cases pc <;>
    simp only [localStep] at h <;> try contradiction
  all_goals
    repeat first | split at h | cases h
    all_goals simp_all [LocalOrigin, max_origin]
  all_goals subst r; simp_all

omit [LinearOrder Id] in
private theorem commit_origin (P : Id → Prop) (s : State n Id) (p : Fin n)
    (r : Local Id × List Id × Option Id) (hs : DataOrigin P s)
    (hr : LocalOrigin P r.1 ∧ (∀ v ∈ r.2.1, P v) ∧ (∀ v ∈ r.2.2, P v)) :
    DataOrigin P (commitLocal s p r) := by
  rcases r with ⟨l, q, out⟩
  rcases hs with ⟨hp, he, hi⟩
  rcases hr with ⟨hl, hq, ho⟩
  cases out <;> simp only [commitLocal, DataOrigin]
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · intro i
      by_cases h : i = p <;> simp_all
    · intro i v hv
      by_cases h : i = p <;> simp_all <;> grind
    · intro i v hv
      by_cases h : i = p <;> simp_all
      grind

/-- Every instruction preserves any set closed under choosing an existing value.
No order/injectivity or maximum-preservation premise is smuggled into this fact. -/
theorem step_origin (P : Id → Prop) (owner : Fin n → Id) {s t : State n Id}
    {a : Action n} (hs : DataOrigin P s) (h : (lts owner).Tr s a t) : DataOrigin P t := by
  change execute owner s a = some t at h
  cases a with
  | idle =>
    simp only [execute, Option.some.injEq] at h
    exact h ▸ hs
  | deliver p =>
    cases heq : s.edge p with
    | nil => simp [execute, heq] at h
    | cons v rest =>
      simp only [execute, heq, Option.some.injEq] at h
      subst t
      rcases hs with ⟨hp, he, hi⟩
      have hv : P v := he p v (by simp [heq])
      refine ⟨hp, ?_, ?_⟩
      · intro i w hw
        by_cases h : i = p
        · subst i
          simp only [Function.update_self] at hw
          exact he p w (by simp [heq, hw])
        · simp only [Function.update_of_ne h] at hw
          exact he i w hw
      · intro i w hw
        by_cases h : i = next p
        · subst i
          simp only [Function.update_self, List.mem_append, List.mem_singleton] at hw
          rcases hw with hw | rfl
          · exact hi _ _ hw
          · exact hv
        · simp only [Function.update_of_ne h] at hw
          exact hi i w hw
  | send p | receive p | compare p =>
    simp only [execute, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    exact commit_origin P s p r hs (local_origin P (owner p) _ _ _ r (hs.1 p) (hs.2.2 p) hr)

/-- All reachable register and queue values were present among the immutable
initial identifiers. Copies and migrating carriers are explicitly allowed. -/
theorem identifier_origin (owner : Fin n → Id) {s : State n Id}
    (h : Reachable owner s) : DataOrigin (fun v => ∃ p, owner p = v) s := by
  obtain ⟨as, h⟩ := h
  have hi : DataOrigin (fun v => ∃ p, owner p = v) (initial owner) := by
    simp [DataOrigin, LocalOrigin, initial]
  exact Cslib.LTS.mtrInv_of_trInv
    (fun _ _ _ htr hs => step_origin _ owner hs htr) _ _ _ h hi

end CircularElection
