import MultiReaderAtomic.Targets

namespace MultiReaderAtomic

/-- Three tokens suffice even when both sampled tokens coincide. -/
theorem token_available (a b : Token) : ∃ t : Token, t ≠ a ∧ t ≠ b := by
  exact Fin.exists_ne_and_ne_of_two_lt a b (by decide)

theorem initial_tokens (j : Fin n) (v₀ : α) :
    initialValue v₀ (.wc j) = 0 ∧ initialValue v₀ (.rc j) = 1 ∧
    initialValue v₀ (.fc j) = 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Token reuse is permitted: sampled 1/1 can choose 0, then sampled 0/0
can choose 1, then sampled 1/1 can choose 0 again. No monotone epoch assumed. -/
theorem token_reuse :
    (0 : Token) ≠ 1 ∧ (1 : Token) ≠ 0 ∧ (0 : Token) ≠ 1 := by decide

def pendingWrite : WriteRecord Nat := ⟨10, 2, 1, 42, 10, none⟩

def overlappingWrite : WriteRecord Nat := ⟨10, 2, 1, 42, 10, some 30⟩

/-- Disjoint reads [12,14] and [20,22] can see new then old while write 10 is pending. -/
theorem regular_new_then_old :
    Eligible [pendingWrite] 12 14 (some 10) ∧
    Eligible [pendingWrite] 20 22 none := by
  simp [Eligible, Precedes, pendingWrite]

/-- A write that has finished during a long read remains eligible. -/
theorem finished_overlap_retained : Eligible [overlappingWrite] 12 40 (some 10) := by
  simp [Eligible, Precedes, overlappingWrite]

/-- Initialization is forbidden when a write precedes the read. -/
theorem quiescent_old_rejected : ¬ Eligible [overlappingWrite] 31 40 none := by
  simp [Eligible, Precedes, overlappingWrite]

/-- Returning an equal payload does not turn initialization into a later source. -/
theorem source_follows_witness :
    Supplies 42 [overlappingWrite] ⟨42, some 10, 1⟩ ∧
    ¬ Supplies 42 [overlappingWrite] ⟨42, some 10, 0⟩ := by
  simp [Supplies, overlappingWrite]

/-- Local transition relation used only for checking program expansion. Reads in
these traces still require separate Eligible/Supplies checks in the global LTS. -/
inductive Local (n : Nat) (α : Type) : Program n α → Program n α → Prop where
  | order (next : Bool → Program n α) (b) : Local n α (.order next) (next b)
  | token (a b t : Token) (next : Token → Program n α) (ha : t ≠ a) (hb : t ≠ b) :
      Local n α (.token a b next) (next t)
  | read (r : Register n) (next : Sample (Value α r) → Program n α) (v) :
      Local n α (.read r next) (next v)
  | write (r : Register n) (v : Value α r) (next) : Local n α (.write r v next) next

/-- Either operand can be first; each alternative still contains two reads. -/
theorem pair_left (a b : Register n) (next : Sample (Value α a) → Sample (Value α b) → Program n α) :
    Local n α (pair a b next) (.read a fun x => .read b fun y => next x y) := by
  exact Local.order _ true

theorem pair_right (a b : Register n) (next : Sample (Value α a) → Sample (Value α b) → Program n α) :
    Local n α (pair a b next) (.read b fun y => .read a fun x => next x y) := by
  exact Local.order _ false

/-- Saved Buff1, not Buff2, is selected after a forwarding observation at level 1.
The RC read and FC write remain before the done/response control point. -/
theorem forwarding_saved_buff1 (j : Fin n) (saved : Sample α) :
    readerFinish j saved true 1 0 0 =
      .read (.rc j) (fun t => .write (.fc j) t.value (.done (some saved))) := by
  simp [readerFinish]

theorem no_notice_reads_buff2 (j : Fin n) (saved : Sample α) :
    readerFinish j saved false 1 0 0 = .read .buff2 (fun v => .done (some v)) := by
  simp [readerFinish]

theorem changed_token_reads_buff2 (j : Fin n) (saved : Sample α) :
    readerFinish j saved true 2 0 1 = .read .buff2 (fun v => .done (some v)) := by
  simp [readerFinish]

/-- A complete trace through the forwarding branch: sample RC, finish FC, return
saved Buff1. This is a control-flow trace, not a global reachability claim. -/
theorem forwarding_local_trace (j : Fin n) (saved : Sample α) (rc : Sample Token) :
    ∃ middle,
      Local n α (readerFinish j saved true 1 0 0) middle ∧
      Local n α middle (.done (some saved)) := by
  rw [forwarding_saved_buff1]
  exact ⟨_, Local.read (.rc j) (fun t => .write (.fc j) t.value (.done (some saved))) rc,
    Local.write (.fc j) rc.value (.done (some saved))⟩

theorem initial_reachable (v₀ : α) : Reachable (n := n) v₀ initial := by
  exact ⟨[], Cslib.LTS.MTr.refl⟩

/-- A genuinely reachable pending reader call (not a fabricated call record). -/
theorem reader_invocation_reachable (v₀ : α) (j : Fin n) :
    Reachable v₀
      ({ withThread (initial : State n α) (.reader j)
          (some ⟨1, 0, .ready (readerProgram j)⟩) with
        calls := [⟨1, .reader j, 1, 0, none, none⟩] } : State n α) := by
  exact ⟨[.invoke (.reader j)], Cslib.LTS.MTr.single (lts v₀)
    (Step.invokeReader initial j rfl)⟩

/-- On enclosed completed histories, API precedence implies source precedence.
Proving enclosure for every reachable state is a structural M2b obligation. -/
theorem api_implies_source (events : List (Primitive n)) (a b : Call n α)
    (ha : Completed a) (hb : Completed b)
    (nonemptyA : ∃ e ∈ events, e.call = a.id)
    (nonemptyB : ∃ e ∈ events, e.call = b.id)
    (ends : ∀ e ∈ events, e.call = a.id → ∀ time result,
      a.response = some (time, result) → ∃ t, e.finish = some t ∧ t ≤ time)
    (starts : ∀ e ∈ events, e.call = b.id → b.invoked ≤ e.start)
    (before : APIBefore a b) : SourceBefore events a b := by
  refine ⟨ha, hb, nonemptyA, nonemptyB, ?_⟩
  intro ea hea eb heb hca hcb
  obtain ⟨time, result, response, lt⟩ := before
  obtain ⟨t, ht, hle⟩ := ends ea hea hca time result response
  exact ⟨t, ht, lt_of_le_of_lt hle (lt_of_lt_of_le lt (starts eb heb hcb))⟩

end MultiReaderAtomic
