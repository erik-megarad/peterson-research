module
public import CircularElection.CycleSubset

/-! Proof-carrying ideal carrier frontiers, constructed independently of any
actual schedule. The actual LTS still has individual asynchronous steps. -/
@[expose] public section
namespace CircularElection
variable {n : Nat} {Id : Type} [LinearOrder Id]

structure Frontier (owner : Fin n → Id) where
  size : Nat
  positive : 0 < size
  physical : Fin size → Fin n
  block : Fin n → Fin size
  origin : Fin size → Fin n
  physical_block : ∀ c, block (physical c) = c
  origin_block : ∀ c, block (origin c) = c
  edge_blocks : ∀ p, block (next p) =
    if p ∈ Set.range physical then finRotate size (block p) else block p
  dominates : ∀ p, ∃ c, owner p ≤ owner (origin c)

namespace Frontier
variable {owner : Fin n → Id}

def candidate (f : Frontier owner) (c : Fin f.size) : Id := owner (f.origin c)

theorem physical_injective (f : Frontier owner) : Function.Injective f.physical := by
  intro p q h
  have hh := congrArg f.block h
  simpa only [f.physical_block] using hh

theorem candidate_injective (f : Frontier owner) (hi : Function.Injective owner) :
    Function.Injective f.candidate := by
  intro p q h
  have hh := congrArg f.block (hi h)
  simpa only [f.origin_block] using hh

def first (owner : Fin n → Id) (hn : 0 < n) : Frontier owner where
  size := n
  positive := hn
  physical := fun p => p
  block := fun p => p
  origin := fun p => p
  physical_block _ := rfl
  origin_block _ := rfl
  edge_blocks p := by
    have h : p ∈ Set.range (fun p : Fin n => p) := ⟨p, rfl⟩
    rw [ite_eq_left h]
    exact (rotate_is_actual_next p).symm
  dominates p := ⟨p, le_rfl⟩

def survivors (f : Frontier owner) : Finset (Fin f.size) :=
  Finset.univ.filter (RoundSurvives f.candidate (finRotate f.size).symm)

theorem survivors_positive (f : Frontier owner) : 0 < f.survivors.card := by
  let : Nonempty (Fin f.size) := ⟨⟨0, f.positive⟩⟩
  obtain ⟨p, hp, _⟩ := round_survivor_exists f.candidate (finRotate f.size).symm
    (finRotate f.size).symm.surjective
  exact Finset.card_pos.mpr ⟨p, by simp [survivors, hp]⟩

def selected (f : Frontier owner) : Fin f.survivors.card ↪o Fin f.size :=
  f.survivors.orderEmbOfFin rfl

def coarsen (f : Frontier owner) : Fin f.size → Fin f.survivors.card :=
  compressedBlock f.survivors f.survivors_positive

theorem coarsen_selected (f : Frontier owner) (i : Fin f.survivors.card) :
    f.coarsen (f.selected i) = i := compressedBlock_selected _ _ i

theorem selected_mem (f : Frontier owner) (i : Fin f.survivors.card) :
    f.selected i ∈ f.survivors := f.survivors.orderEmbOfFin_mem rfl i

theorem coarsen_next (f : Frontier owner) (c : Fin f.size) :
    f.coarsen (finRotate f.size c) =
      if c ∈ f.survivors then finRotate f.survivors.card (f.coarsen c) else f.coarsen c := by
  rw [rotate_is_actual_next]
  exact compressedBlock_next f.survivors f.survivors_positive c

theorem previous_coarsens_to_survivor (f : Frontier owner) (hi : Function.Injective owner)
    (i : Fin f.survivors.card) :
    f.coarsen ((finRotate f.size).symm (f.selected i)) = i := by
  by_cases hs : 2 ≤ f.size
  · have hp : RoundSurvives f.candidate (finRotate f.size).symm (f.selected i) := by
      simpa [survivors] using f.selected_mem i
    have hd : f.candidate ((finRotate f.size).symm (f.selected i)) ≠
        f.candidate ((finRotate f.size).symm ((finRotate f.size).symm (f.selected i))) := by
      intro he
      exact rotate_previous_ne hs _ ((f.candidate_injective hi he).symm)
    have hn := round_no_adjacent f.candidate (finRotate f.size).symm (f.selected i) hd hp
    have hnot : (finRotate f.size).symm (f.selected i) ∉ f.survivors := by
      simpa [survivors] using hn
    have ht := f.coarsen_next ((finRotate f.size).symm (f.selected i))
    simpa only [Equiv.apply_symm_apply, ite_eq_right hnot, f.coarsen_selected] using ht.symm
  · have he : (finRotate f.size).symm (f.selected i) = f.selected i := by
      apply Fin.ext
      have hp := ((finRotate f.size).symm (f.selected i)).isLt
      have hq := (f.selected i).isLt
      omega
    rw [he, f.coarsen_selected]

/-- The full recurrence retains all origin-location and maximum facts for the
next ideal frontier, for arbitrary ring size and injective original owners. -/
def advance (f : Frontier owner) (hi : Function.Injective owner) : Frontier owner where
  size := f.survivors.card
  positive := f.survivors_positive
  physical i := f.physical (f.selected i)
  block p := f.coarsen (f.block p)
  origin i := f.origin ((finRotate f.size).symm (f.selected i))
  physical_block i := by rw [f.physical_block, f.coarsen_selected]
  origin_block i := by rw [f.origin_block, f.previous_coarsens_to_survivor hi]
  edge_blocks p := by
    classical
    by_cases ho : p ∈ Set.range f.physical
    · obtain ⟨c, rfl⟩ := ho
      rw [f.edge_blocks, ite_eq_left (by exact ⟨c, rfl⟩), f.physical_block, f.coarsen_next]
      by_cases hc : c ∈ f.survivors
      · let i := (f.survivors.orderIsoOfFin rfl).symm ⟨c, hc⟩
        have he : f.selected i = c := by
          exact congrArg Subtype.val ((f.survivors.orderIsoOfFin rfl).apply_symm_apply ⟨c, hc⟩)
        have hnew : f.physical c ∈ Set.range (fun i => f.physical (f.selected i)) :=
          ⟨i, by change f.physical (f.selected i) = f.physical c; rw [he]⟩
        simp [hc, hnew]
      · have hnew : f.physical c ∉ Set.range (fun i => f.physical (f.selected i)) := by
          rintro ⟨i, he⟩
          have he' := f.physical_injective he
          exact hc (he' ▸ f.selected_mem i)
        simp [hc, hnew]
    · have hnew : p ∉ Set.range (fun i => f.physical (f.selected i)) := by
        rintro ⟨i, he⟩
        exact ho ⟨f.selected i, he⟩
      simp [f.edge_blocks p, ho, hnew]
  dominates p := by
    let : Nonempty (Fin f.size) := ⟨⟨0, f.positive⟩⟩
    obtain ⟨c, hc, hm⟩ := round_survivor_exists f.candidate (finRotate f.size).symm
      (finRotate f.size).symm.surjective
    have hcmem : c ∈ f.survivors := by simp [survivors, hc]
    let i := (f.survivors.orderIsoOfFin rfl).symm ⟨c, hcmem⟩
    have he : f.selected i = c := by
      exact congrArg Subtype.val ((f.survivors.orderIsoOfFin rfl).apply_symm_apply ⟨c, hcmem⟩)
    obtain ⟨q, hq⟩ := f.dominates p
    refine ⟨i, ?_⟩
    rw [he]
    exact le_trans hq (hm q)

def Active (f : Frontier owner) (p : Fin n) : Prop := p ∈ Set.range f.physical

instance (f : Frontier owner) (p : Fin n) : Decidable (f.Active p) :=
  inferInstanceAs (Decidable (∃ c, f.physical c = p))

def incomingEven (f : Frontier owner) (p : Fin n) : Id :=
  f.candidate ((finRotate f.size).symm (f.block p))

def incomingOdd (f : Frontier owner) (p : Fin n) : Id :=
  max (f.incomingEven p)
    (f.candidate ((finRotate f.size).symm ((finRotate f.size).symm (f.block p))))

theorem advance_active (f : Frontier owner) (hi : Function.Injective owner) (p : Fin n) :
    (f.advance hi).Active p ↔ f.Active p ∧
      RoundSurvives f.candidate (finRotate f.size).symm (f.block p) := by
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨⟨f.selected i, rfl⟩, ?_⟩
    change RoundSurvives f.candidate (finRotate f.size).symm
      (f.block (f.physical (f.selected i)))
    rw [f.physical_block]
    simpa [survivors] using f.selected_mem i
  · rintro ⟨⟨c, rfl⟩, hc⟩
    rw [f.physical_block] at hc
    have hm : c ∈ f.survivors := by simpa [survivors] using hc
    let i := (f.survivors.orderIsoOfFin rfl).symm ⟨c, hm⟩
    have he : f.selected i = c :=
      congrArg Subtype.val ((f.survivors.orderIsoOfFin rfl).apply_symm_apply ⟨c, hm⟩)
    refine ⟨i, ?_⟩
    change f.physical (f.selected i) = f.physical c
    rw [he]

theorem advance_candidate (f : Frontier owner) (hi : Function.Injective owner) (p : Fin n)
    (ha : (f.advance hi).Active p) :
    (f.advance hi).candidate ((f.advance hi).block p) = f.incomingEven p := by
  obtain ⟨i, rfl⟩ := ha
  have hg := (f.advance hi).physical_block i
  change (f.advance hi).candidate
    ((f.advance hi).block ((f.advance hi).physical i)) = f.incomingEven ((f.advance hi).physical i)
  rw [hg]
  change owner (f.origin ((finRotate f.size).symm (f.selected i))) =
    owner (f.origin ((finRotate f.size).symm (f.block (f.physical (f.selected i)))))
  rw [f.physical_block]

theorem even_edge (f : Frontier owner) (p : Fin n) :
    f.incomingEven (next p) =
      if f.Active p then f.candidate (f.block p) else f.incomingEven p := by
  by_cases ha : f.Active p
  · have he := f.edge_blocks p
    have ha' : p ∈ Set.range f.physical := ha
    rw [ite_eq_left ha'] at he
    unfold incomingEven
    rw [he, Equiv.symm_apply_apply, ite_eq_left ha]
  · have he := f.edge_blocks p
    have ha' : p ∉ Set.range f.physical := ha
    rw [ite_eq_right ha'] at he
    unfold incomingEven
    rw [he, ite_eq_right ha]

theorem odd_edge (f : Frontier owner) (p : Fin n) :
    f.incomingOdd (next p) =
      if f.Active p then max (f.candidate (f.block p)) (f.incomingEven p) else f.incomingOdd p := by
  by_cases ha : f.Active p
  · have he := f.edge_blocks p
    have ha' : p ∈ Set.range f.physical := ha
    rw [ite_eq_left ha'] at he
    unfold incomingOdd incomingEven
    rw [he, Equiv.symm_apply_apply, ite_eq_left ha]
  · have he := f.edge_blocks p
    have ha' : p ∉ Set.range f.physical := ha
    rw [ite_eq_right ha'] at he
    unfold incomingOdd incomingEven
    rw [he, ite_eq_right ha]

theorem comparison_is_survival (f : Frontier owner) (p : Fin n) :
    max (f.candidate (f.block p)) (f.incomingOdd p) ≤ f.incomingEven p ↔
      RoundSurvives f.candidate (finRotate f.size).symm (f.block p) := by
  simp [incomingOdd, incomingEven, RoundSurvives]

/-- Any prospective incoming occurrence equal to the receiver's original ID
identifies a global maximum. This includes relay receivers and sizes 1 and 2. -/
theorem incoming_return_maximum (f : Frontier owner) (hi : Function.Injective owner)
    (p : Fin n) :
    (f.incomingEven p = owner p ∨ f.incomingOdd p = owner p) → IsMaximum owner p := by
  intro hr
  by_cases hs : 3 ≤ f.size
  · have hx := cyclic_round_pair_excludes hs owner f.block f.origin hi f.origin_block p
    rcases hr with he | ho
    · exact (hx.1 he).elim
    · exact (hx.2 ho).elim
  · by_cases ht : 2 ≤ f.size
    · have hm : f.size = 2 := by omega
      rcases hr with he | ho
      · have hx := block_origin_excludes owner f.block f.origin hi f.origin_block p
          ((finRotate f.size).symm (f.block p)) (rotate_previous_ne ht _)
        exact (hx he).elim
      · apply two_carrier_odd_return owner f.origin
          ((finRotate f.size).symm (f.block p))
          ((finRotate f.size).symm ((finRotate f.size).symm (f.block p)))
          ?_ f.dominates p ho
        intro c
        have hneq := rotate_previous_ne ht ((finRotate f.size).symm (f.block p))
        have h₁ := ((finRotate f.size).symm (f.block p)).isLt
        have h₂ := ((finRotate f.size).symm ((finRotate f.size).symm (f.block p))).isLt
        have hc := c.isLt
        have hn : ((finRotate f.size).symm (f.block p)).val ≠
            ((finRotate f.size).symm ((finRotate f.size).symm (f.block p))).val :=
          fun h => hneq (Fin.ext h.symm)
        have : c.val = ((finRotate f.size).symm (f.block p)).val ∨
            c.val = ((finRotate f.size).symm ((finRotate f.size).symm (f.block p))).val := by omega
        exact this.imp Fin.ext Fin.ext
    · have heq (c d : Fin f.size) : c = d := by
        apply Fin.ext
        have hc := c.isLt
        have hd := d.isLt
        omega
      have hreturn : f.candidate ((finRotate f.size).symm (f.block p)) = owner p := by
        rcases hr with he | ho
        · exact he
        · change max (f.candidate ((finRotate f.size).symm (f.block p)))
            (f.candidate ((finRotate f.size).symm ((finRotate f.size).symm (f.block p)))) =
            owner p at ho
          rw [heq ((finRotate f.size).symm ((finRotate f.size).symm (f.block p)))
            ((finRotate f.size).symm (f.block p)), max_self] at ho
          exact ho
      exact singleton_return owner f.origin ((finRotate f.size).symm (f.block p))
        (fun c => heq c _) f.dominates p hreturn

end Frontier
end CircularElection
