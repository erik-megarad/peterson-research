import ConcurrentReading.Targets
import Aesop
import Lean.Elab.Tactic.Omega

namespace ConcurrentReading

set_option maxHeartbeats 2000000

/-- Control facts needed to justify the fresh acknowledgement. This predicate
does not assume anything about a raw read or the value stored in a buffer. -/
def Handshake (s : State α n) : Prop := ∀ i : Fin n,
  ((s.readers i).pc = 2 → (s.readers i).bit ≠ s.writing i →
    s.reading i = s.writing i) ∧
  (s.writer.j = i.val →
    (s.writer.pc = 8 → s.writer.bit ≠ s.writing i → s.reading i ≠ s.writing i) ∧
    (9 ≤ s.writer.pc → s.writer.pc ≤ 12 → s.reading i ≠ s.writing i) ∧
    (s.writer.pc = 12 → s.writer.bit = s.reading i))

theorem handshake_initial (v : α) (privateData : Fin n → α) :
    Handshake (initial v privateData) := by
  simp [Handshake, initial]

theorem handshake_writer {s t : State α n} (hs : Handshake s)
    (h : writerStep s = some t) : Handshake t := by
  cases hr : s.rawWrite <;>
    unfold writerStep at h <;>
    dsimp only at h <;>
    split at h
  all_goals repeat' split at h
  all_goals simp [endWrite, hr] at h
  all_goals subst t
  all_goals intro i
  all_goals have hi := hs i
  all_goals simp_all [Handshake, beginWrite, emit, Function.update_apply, Fin.ext_iff]
  all_goals aesop

theorem handshake_reader {s t : State α n} (hs : Handshake s)
    (j : Fin n) (corrupt : α) (h : readerStep s j corrupt = some t) : Handshake t := by
  cases hr : s.rawReads j <;>
    cases hc : (s.readers j).chosen <;>
    unfold readerStep at h <;>
    dsimp only at h <;>
    split at h
  all_goals repeat' split at h
  all_goals simp [endRead, hr, hc] at h
  all_goals subst t
  all_goals intro i
  all_goals have hi := hs i
  all_goals by_cases hij : i = j
  all_goals try subst i
  all_goals simp_all [Handshake, putReader, beginRead, emit]
  all_goals cases hb : (s.readers j).bit <;>
    cases hw : s.writing j <;>
    cases hd : s.reading j <;> simp_all
  all_goals have hj := hs j
  all_goals simp_all
  all_goals aesop

theorem handshake_step {s t : State α n} (hs : Handshake s)
    (a : Action α n) (h : step s a = some t) : Handshake t := by
  cases a with
  | invokeWrite v =>
    simp only [step] at h
    split at h <;> simp [emit] at h
    subst t
    simpa [Handshake] using (fun i => (hs i).1)
  | invokeRead j =>
    simp only [step] at h
    split at h <;> simp [emit, putReader] at h
    subst t
    intro i
    have hi := hs i
    by_cases hij : i = j <;> simp_all [Handshake]
  | writer =>
    cases hw : writerStep s with
    | none => simp [step, hw] at h
    | some u =>
      have hu := handshake_writer hs hw
      simp [step, hw] at h
      subst t
      exact hu
  | reader j corrupt =>
    cases hr : readerStep s j corrupt with
    | none => simp [step, hr] at h
    | some u =>
      have hu := handshake_reader hs j corrupt hr
      simp [step, hr] at h
      subst t
      exact hu

theorem handshake_run {s t : State α n} {as : List (Action α n)}
    (hs : Handshake s) (h : run s as = some t) : Handshake t := by
  induction as generalizing s with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst t
    exact hs
  | cons a as ih =>
    cases ht : step s a with
    | none => simp [run, ht] at h
    | some u =>
      simp only [run, ht, Option.bind_some] at h
      exact ih (handshake_step hs a ht) h

theorem handshake_reachable {v : α} {privateData : Fin n → α} {s : State α n}
    (h : Reachable v privateData s) : Handshake s := by
  obtain ⟨as, h⟩ := h
  exact handshake_run (handshake_initial v privateData) h

end ConcurrentReading
