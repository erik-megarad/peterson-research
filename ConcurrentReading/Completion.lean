import ConcurrentReading.Handshake

namespace ConcurrentReading

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- Remaining abstract writer actions, charging each scan position six actions. -/
def writerRank (n : Nat) (w : Writer α) : Nat :=
  match w.pc with
  | 1 => 10 + 6*n | 2 => 9 + 6*n | 3 => 8 + 6*n
  | 4 => 7 + 6*n | 5 => 6 + 6*n | 6 => 5 + 6*n
  | 7 => 4 + 6*(n-w.j) | 8 => 3 + 6*(n-w.j)
  | 9 => 2 + 6*(n-w.j) | 10 => 1 + 6*(n-w.j)
  | 11 => 6*(n-w.j) | 12 => 6*(n-w.j)-1
  | 13 => 3 | 14 => 2 | 15 => 1 | _ => 0

def ownRank (s : State α n) : Process n → Nat
  | .writer => writerRank n s.writer
  | .reader i => if (s.readers i).pc = 0 then 0 else 17 - (s.readers i).pc

theorem writer_rank_bound (w : Writer α) : writerRank n w < 16 + 6*n := by
  unfold writerRank
  split <;> omega

theorem own_rank_bound (s : State α n) (p : Process n) :
    ownRank s p < 16 + 6*n := by
  cases p with
  | writer => exact writer_rank_bound _
  | reader i =>
    have hi := i.isLt
    simp only [ownRank]; split <;> omega

theorem writer_rank_step {s t : State α n} (h : writerStep s = some t) :
    writerRank n t.writer + 1 ≤ writerRank n s.writer := by
  cases hr : s.rawWrite <;>
    unfold writerStep at h <;> dsimp only at h <;> split at h
  all_goals repeat' split at h
  all_goals simp [endWrite, hr] at h
  all_goals subst t
  all_goals simp_all [writerRank, beginWrite, emit]
  all_goals omega

theorem reader_rank_step {s t : State α n} (i : Fin n) (v : α)
    (h : readerStep s i v = some t) :
    ownRank t (.reader i) + 1 ≤ ownRank s (.reader i) := by
  unfold readerStep at h
  dsimp only at h
  split at h
  all_goals repeat' split at h
  all_goals simp [endRead, Option.bind_eq_some_iff] at h
  all_goals try obtain ⟨raw, hr, h⟩ := h
  all_goals try obtain ⟨sample, hc, h⟩ := h
  all_goals try subst t
  all_goals simp_all [ownRank, putReader, beginRead, emit]
  all_goals omega

theorem writer_preserves_readers {s t : State α n}
    (h : writerStep s = some t) : t.readers = s.readers := by
  cases hr : s.rawWrite <;>
    unfold writerStep at h <;> dsimp only at h <;> split at h
  all_goals repeat' split at h
  all_goals simp [endWrite, hr] at h
  all_goals subst t
  all_goals rfl

theorem reader_preserves_control {s t : State α n} (i : Fin n) (v : α)
    (h : readerStep s i v = some t) :
    t.writer = s.writer ∧ ∀ j, j ≠ i → t.readers j = s.readers j := by
  unfold readerStep at h
  dsimp only at h
  split at h
  all_goals repeat' split at h
  all_goals simp [endRead, Option.bind_eq_some_iff] at h
  all_goals try obtain ⟨raw, hr, h⟩ := h
  all_goals try obtain ⟨sample, hc, h⟩ := h
  all_goals try subst t
  all_goals simp_all [putReader, beginRead, emit]

theorem own_rank_step {s t : State α n} (a : Action α n) (p : Process n)
    (hb : busy s p) (h : step s a = some t) :
    ownRank t p + (if owner a = p then 1 else 0) ≤ ownRank s p := by
  cases a with
  | invokeWrite v =>
    simp only [step] at h
    split at h <;> simp [emit] at h
    subst t
    cases p <;> simp_all [busy, ownRank, owner]
  | invokeRead j =>
    simp only [step] at h
    split at h <;> simp [putReader, emit] at h
    subst t
    cases p with
    | writer => simp [ownRank, owner]
    | reader i =>
      by_cases hi : i = j
      · subst i; simp_all [busy]
      · simp_all [ownRank, owner, Ne.symm hi]
  | writer =>
    cases hw : writerStep s with
    | none => simp [step, hw] at h
    | some u =>
      have hd := writer_rank_step hw
      have hp := writer_preserves_readers hw
      simp [step, hw] at h
      subst t
      cases p <;> simp_all [ownRank, owner]
  | reader j v =>
    cases hr : readerStep s j v with
    | none => simp [step, hr] at h
    | some u =>
      have hd := reader_rank_step j v hr
      have hp := reader_preserves_control j v hr
      simp [step, hr] at h
      subst t
      cases p with
      | writer => simp_all [ownRank, owner]
      | reader i =>
        by_cases hi : i = j
        · subst i; simpa [owner, ownRank] using hd
        · simp_all [ownRank, owner, Ne.symm hi]

def ownCount (actions : Nat → Action α n) (p : Process n) (T : Nat) : Nat :=
  ((List.range T).filter (fun t => decide (owner (actions t) = p))).length

theorem own_count_succ (actions : Nat → Action α n) (p : Process n) (T : Nat) :
    ownCount actions p (T+1) = ownCount actions p T +
      (if owner (actions T) = p then 1 else 0) := by
  simp [ownCount, List.range_succ, List.filter_append]
  split <;> simp_all

theorem countdown_interval (states : Nat → State α n) (actions : Nat → Action α n)
    (hs : ∀ t, step (states t) (actions t) = some (states (t+1)))
    (p : Process n) (T : Nat) (hb : ∀ t, t ≤ T → busy (states t) p) :
    ownCount actions p T + ownRank (states T) p ≤ ownRank (states 0) p := by
  induction T with
  | zero => simp [ownCount]
  | succ T ih =>
    have hprev := ih (fun t ht => hb t (by omega))
    have hstep := own_rank_step (actions T) p (hb T (by omega)) (hs T)
    rw [own_count_succ]
    omega

/-- The exact protected completion target, for the actual transition system. -/
theorem own_completion : OwnCompletion := by
  intro α n hn v privateData states actions _ hs p T _ hc
  by_contra h
  have hb : ∀ t, t ≤ T → busy (states t) p := by
    intro t ht
    by_contra hidle
    exact h ⟨t, ht, hidle⟩
  have hd := countdown_interval states actions hs p T hb
  have hr := own_rank_bound (states 0) p
  change ownCount actions p T ≥ 16 + 6*n at hc
  omega

/-- Infinitely many own abstract actions imply an idle occurrence. Connecting
this abstract scheduling premise to physical execution requires each invoked raw
operation to terminate, so that its end action can occur. -/
theorem eventual_own_completion (states : Nat → State α n)
    (actions : Nat → Action α n)
    (hs : ∀ t, step (states t) (actions t) = some (states (t+1)))
    (p : Process n) (hown : ∀ K, ∃ T, K ≤ ownCount actions p T) :
    ∃ t, ¬ busy (states t) p := by
  obtain ⟨T, hc⟩ := hown (16 + 6*n)
  by_contra h
  have hb : ∀ t, t ≤ T → busy (states t) p := by
    intro t _
    by_contra hidle
    exact h ⟨t, hidle⟩
  have hd := countdown_interval states actions hs p T hb
  have hr := own_rank_bound (states 0) p
  omega

end ConcurrentReading
