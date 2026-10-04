module
public import CircularElection.History
public import CircularElection.Maximum
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! Algebra used by the occurrence-stream safety proof. Cyclic carrier and
origin-block facts are constructed in Frontier.lean and connected to actual
FIFO instructions by Plan.lean and Safety.lean. -/
@[expose] public section
namespace CircularElection
variable {Id : Type} [LinearOrder Id]

/-- The printed comparison after an incoming pair from two preceding carriers. -/
def RoundSurvives {Carrier : Type} (candidate : Carrier → Id)
    (previous : Carrier → Carrier) (p : Carrier) : Prop :=
  max (candidate p) (candidate (previous (previous p))) ≤ candidate (previous p)

instance {Carrier : Type} (candidate : Carrier → Id) (previous : Carrier → Carrier)
    (p : Carrier) : Decidable (RoundSurvives candidate previous p) :=
  inferInstanceAs (Decidable (max (candidate p) (candidate (previous (previous p))) ≤
    candidate (previous p)))

/-- Distinct neighboring candidates cannot both survive. The singleton is
excluded by the inequality between the two predecessor candidates. -/
theorem round_no_adjacent {Carrier : Type} (candidate : Carrier → Id)
    (previous : Carrier → Carrier) (p : Carrier)
    (hd : candidate (previous p) ≠ candidate (previous (previous p)))
    (hp : RoundSurvives candidate previous p) :
    ¬ RoundSurvives candidate previous (previous p) := by
  intro hq
  have h₁ : candidate (previous (previous p)) ≤ candidate (previous p) :=
    le_trans (le_max_right _ _) hp
  have h₂ : candidate (previous p) ≤ candidate (previous (previous p)) :=
    le_trans (le_max_left _ _) hq
  exact hd (le_antisymm h₂ h₁)

/-- The carrier after a maximum survives and adopts that maximum. This holds
also for a one- or two-carrier cycle, using the published non-strict test. -/
theorem round_maximum_survives {Carrier : Type} (candidate : Carrier → Id)
    (previous : Carrier → Carrier) (p : Carrier)
    (hm : ∀ q, candidate q ≤ candidate (previous p)) :
    RoundSurvives candidate previous p :=
  max_le (hm p) (hm (previous (previous p)))

/-- A finite nonempty cycle always retains a maximum candidate somewhere. The
predecessor's surjectivity supplies its next carrier; no fairness is involved. -/
theorem round_survivor_exists {Carrier : Type} [Fintype Carrier] [Nonempty Carrier]
    (candidate : Carrier → Id) (previous : Carrier → Carrier)
    (hs : Function.Surjective previous) :
    ∃ p, RoundSurvives candidate previous p ∧
      ∀ q, candidate q ≤ candidate (previous p) := by
  obtain ⟨q, _, hq⟩ := Finset.exists_max_image Finset.univ candidate
    (Finset.univ_nonempty : (Finset.univ : Finset Carrier).Nonempty)
  obtain ⟨p, hp⟩ := hs q
  have hm : ∀ x, candidate x ≤ candidate (previous p) := by
    intro x
    rw [hp]
    exact hq x (Finset.mem_univ x)
  exact ⟨p, round_maximum_survives candidate previous p hm, hm⟩

/-- Adoption cannot merge two distinct candidate occurrences: surviving
carriers take the candidate of their distinct preceding carriers. -/
theorem round_adoption_injective {Carrier : Type} (candidate : Carrier → Id)
    (previous : Carrier → Carrier) (hc : Function.Injective candidate)
    (hp : Function.Injective previous) :
    Function.Injective (fun p : {p // RoundSurvives candidate previous p} =>
      candidate (previous p.val)) := by
  intro p q h
  apply Subtype.ext
  exact hp (hc h)

omit [LinearOrder Id] in
/-- A receiver's block and a candidate's origin block differ, so an injective
owner assignment excludes that candidate from being the receiver's own ID. -/
theorem block_origin_excludes {Position Carrier : Type}
    (owner : Position → Id) (block : Position → Carrier) (origin : Carrier → Position)
    (hi : Function.Injective owner) (hb : ∀ c, block (origin c) = c)
    (p : Position) (c : Carrier) (hn : c ≠ block p) : owner (origin c) ≠ owner p := by
  intro he
  have ho := hi he
  apply hn
  rw [← hb c, ho]

/-- On a cycle with at least three carriers, the two preceding blocks exclude
both incoming candidate origins, for active and relay receivers alike. The
block and predecessor conditions are supplied by the frontier construction. -/
theorem round_pair_excludes {Position Carrier : Type}
    (owner : Position → Id) (block : Position → Carrier) (origin : Carrier → Position)
    (previous : Carrier → Carrier) (hi : Function.Injective owner)
    (hb : ∀ c, block (origin c) = c) (p : Position)
    (h₁ : previous (block p) ≠ block p)
    (h₂ : previous (previous (block p)) ≠ block p) :
    owner (origin (previous (block p))) ≠ owner p ∧
    max (owner (origin (previous (block p))))
      (owner (origin (previous (previous (block p))))) ≠ owner p := by
  have ha := block_origin_excludes owner block origin hi hb p _ h₁
  have hb' := block_origin_excludes owner block origin hi hb p _ h₂
  refine ⟨ha, ?_⟩
  rcases le_total (owner (origin (previous (block p))))
      (owner (origin (previous (previous (block p))))) with h | h
  · simpa [max_eq_right h] using hb'
  · simpa [max_eq_left h] using ha

/-- With two carriers the odd input is the maximum of the complete candidate
set. If this equals a receiver's owner, that owner is globally maximum. -/
theorem two_carrier_odd_return {Position Carrier : Type}
    (owner : Position → Id) (origin : Carrier → Position) (a b : Carrier)
    (hcover : ∀ c, c = a ∨ c = b)
    (hmaximum : ∀ p, ∃ c, owner p ≤ owner (origin c)) (p : Position)
    (hreturn : max (owner (origin a)) (owner (origin b)) = owner p) :
    ∀ q, owner q ≤ owner p := by
  intro q
  obtain ⟨c, hc⟩ := hmaximum q
  rw [← hreturn]
  rcases hcover c with rfl | rfl
  · exact le_trans hc (le_max_left _ _)
  · exact le_trans hc (le_max_right _ _)

/-- If one carrier remains, preservation of a dominating candidate makes
both prospective incoming occurrences the original global maximum. -/
theorem singleton_return {Position Carrier : Type}
    (owner : Position → Id) (origin : Carrier → Position) (a : Carrier)
    (hcover : ∀ c, c = a)
    (hmaximum : ∀ p, ∃ c, owner p ≤ owner (origin c)) (p : Position)
    (hreturn : owner (origin a) = owner p) : ∀ q, owner q ≤ owner p := by
  intro q
  obtain ⟨c, hc⟩ := hmaximum q
  rw [hcover c, hreturn] at hc
  exact hc

omit [LinearOrder Id] in
/-- Mathlib's cyclic permutation agrees with the accepted physical successor. -/
theorem rotate_is_actual_next {n : Nat} (p : Fin n) : finRotate n p = next p := by
  let : NeZero n := p.neZero
  apply Fin.ext
  simp [finRotate_apply, next, Fin.add_def]

omit [LinearOrder Id] in
/-- On a cycle of at least two positions its predecessor is never itself. -/
theorem rotate_previous_ne {m : Nat} (hm : 2 ≤ m) (p : Fin m) :
    (finRotate m).symm p ≠ p := by
  intro he
  have ht : finRotate m p = p := by
    calc
      finRotate m p = finRotate m ((finRotate m).symm p) := congrArg (finRotate m) he.symm
      _ = p := (finRotate m).apply_symm_apply p
  have hv := congrArg Fin.val ht
  rw [rotate_is_actual_next] at hv
  change (p.val + 1) % m = p.val at hv
  have hp := p.isLt
  by_cases hs : p.val + 1 < m
  · rw [Nat.mod_eq_of_lt hs] at hv
    omega
  · have hs' : p.val + 1 = m := by omega
    rw [hs', Nat.mod_self] at hv
    omega

omit [LinearOrder Id] in
/-- On a cycle of at least three carriers neither of the two preceding
carriers is the receiving carrier. This discharges the pair lemma's geometry
for canonical cycles, including receivers situated inside relay segments. -/
theorem rotate_previous_twice_ne {m : Nat} (hm : 3 ≤ m) (p : Fin m) :
    (finRotate m).symm ((finRotate m).symm p) ≠ p := by
  intro he
  have ht : finRotate m (finRotate m p) = p := by
    have hh := congrArg (fun q => finRotate m (finRotate m q)) he
    simpa only [Equiv.apply_symm_apply] using hh.symm
  have hv := congrArg Fin.val ht
  simp only [rotate_is_actual_next] at hv
  change (((p.val + 1) % m + 1) % m) = p.val at hv
  have hp := p.isLt
  by_cases hs : p.val + 1 < m
  · rw [Nat.mod_eq_of_lt hs] at hv
    by_cases ht : p.val + 2 < m
    · have htt : p.val + 1 + 1 < m := by omega
      rw [Nat.mod_eq_of_lt htt] at hv
      omega
    · have htt : p.val + 1 + 1 = m := by omega
      rw [htt, Nat.mod_self] at hv
      omega
  · have htt : p.val + 1 = m := by omega
    rw [htt, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < m)] at hv
    omega

/-- The larger-cycle return exclusion has no extra predecessor-distinctness
premises once the carrier cycle is represented by Fin m. The origin-block
partition itself is supplied by the complete frontier recurrence. -/
theorem cyclic_round_pair_excludes {Position : Type} {m : Nat} (hm : 3 ≤ m)
    (owner : Position → Id) (block : Position → Fin m) (origin : Fin m → Position)
    (hi : Function.Injective owner) (hb : ∀ c, block (origin c) = c) (p : Position) :
    owner (origin ((finRotate m).symm (block p))) ≠ owner p ∧
    max (owner (origin ((finRotate m).symm (block p))))
      (owner (origin ((finRotate m).symm ((finRotate m).symm (block p))))) ≠ owner p :=
  round_pair_excludes owner block origin (finRotate m).symm hi hb p
    (rotate_previous_ne (by omega) _) (rotate_previous_twice_ne hm _)

end CircularElection
