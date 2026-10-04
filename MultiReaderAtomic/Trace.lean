import MultiReaderAtomic.Examples

namespace MultiReaderAtomic

def quiescentActions : List (Action 1) :=
  [.invoke (.reader 0), .beginAccess (.reader 0), .endAccess (.reader 0),
   .beginAccess (.reader 0), .endAccess (.reader 0),
   .beginAccess (.reader 0), .endAccess (.reader 0), .localStep (.reader 0),
   .beginAccess (.reader 0), .endAccess (.reader 0),
   .beginAccess (.reader 0), .endAccess (.reader 0),
   .beginAccess (.reader 0), .endAccess (.reader 0), .localStep (.reader 0),
   .beginAccess (.reader 0), .endAccess (.reader 0),
   .beginAccess (.reader 0), .endAccess (.reader 0), .respond (.reader 0)]

/-- Twenty actual endpoint/local transitions complete a one-reader quiescent
call. The control read of RC carries its actual primitive-write witness (4). -/
theorem quiescent_reader_trace :
    ∃ s : State 1 Nat, (lts 0).MTr initial quiescentActions s ∧
      (⟨1, .reader 0, 1, 0, none, some (20, some ⟨0, none, 0⟩)⟩ : Call 1 Nat) ∈ s.calls := by
  refine' ⟨_, ?_, ?_⟩
  rotate_left 1
  · refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.invokeReader initial 0 rfl) ?_
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.beginRead _ (.reader 0) _ (.wc 0) _ rfl rfl) ?_
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.endRead _ (.reader 0) _ (.wc 0) _ _ ⟨0, none, 0⟩ rfl rfl ?_ ?_) ?_
    · simp [Eligible, initial, withThread]
    · simp [Supplies, initialValue]
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.beginWrite _ (.reader 0) _ (.rc 0) 0 _ rfl rfl rfl) ?_
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.endWrite _ (.reader 0) _ (.rc 0) _ _ rfl rfl) ?_
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.beginRead _ (.reader 0) _ .buff1 _ rfl rfl) ?_
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.endRead _ (.reader 0) _ .buff1 _ _ ⟨0, none, 0⟩ rfl rfl ?_ ?_) ?_
    · simp [Eligible, initial, withThread]
    · simp [Supplies, initialValue]
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.order _ (.reader 0) _ _ true rfl rfl) ?_
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.beginRead _ (.reader 0) _ (.fc 0) _ rfl rfl) ?_
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.endRead _ (.reader 0) _ (.fc 0) _ _ ⟨1, none, 0⟩ rfl rfl ?_ ?_) ?_
    · simp [Eligible, initial, withThread]
    · simp [Supplies, initialValue]
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.beginRead _ (.reader 0) _ (.wc 0) _ rfl rfl) ?_
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.endRead _ (.reader 0) _ (.wc 0) _ _ ⟨0, none, 0⟩ rfl rfl ?_ ?_) ?_
    · simp [Eligible, initial, withThread]
    · simp [Supplies, initialValue]
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.beginRead _ (.reader 0) _ .level _ rfl rfl) ?_
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.endRead _ (.reader 0) _ .level _ _ ⟨0, none, 0⟩ rfl rfl ?_ ?_) ?_
    · simp [Eligible, initial, withThread]
    · simp [Supplies, initialValue]
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.order _ (.reader 0) _ _ true rfl rfl) ?_
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.beginRead _ (.reader 0) _ (.rc 0) _ rfl rfl) ?_
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.endRead _ (.reader 0) _ (.rc 0) _ _ ⟨0, some 4, 0⟩ rfl rfl ?_ ?_) ?_
    · simp [Eligible, Precedes, initial, withThread, closeWrite]
    · simp [Supplies, initial, withThread, closeWrite]
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.beginRead _ (.reader 0) _ (.wc 0) _ rfl rfl) ?_
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.endRead _ (.reader 0) _ (.wc 0) _ _ ⟨0, none, 0⟩ rfl rfl ?_ ?_) ?_
    · simp [Eligible, initial, withThread]
    · simp [Supplies, initialValue]
    refine Cslib.LTS.MTr.stepL (lts := lts (n := 1) (0 : Nat)) (Step.respond _ (.reader 0) _ (some ⟨0, none, 0⟩) rfl rfl) ?_
    exact Cslib.LTS.MTr.refl
  · simp [initial, withThread]

end MultiReaderAtomic
