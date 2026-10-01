import Peterson.EconomicalSolutions.TwoStateScheduling
import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-! Infinite bypass for the reviewed deterministic owner-register grammar.
The victim retains one original request and its full private history. Peer
failures are used explicitly; this does not prove the failure-free strengthening. -/
namespace EconomicalSolutions.TwoState.Program

variable {V : Type u} {M : Type v} (P : Program V M)

/-- Continuing a constant-peer history from an arbitrary index preserves the
entire local record, including every cached read and private counter. -/
theorem against_tail (s : State V M) (g : V) (p : Bool) (k : Nat)
    (hp : s p = P.against g p k) (hg : (s (!p)).value = g) :
    ∀ n, P.solo s p n p = P.against g p (k + n) := by
  intro n
  induction n with
  | zero => simpa only [solo, Nat.add_zero] using hp
  | succ n ih =>
    simp only [solo, run_self, solo_other, ih, hg, against]
    rfl

/-- Dead publication lets a fresh peer enter, by replaying a progress-derived
first entry beside a failed victim. The real victim is never reset or stepped. -/
theorem dead_peer_first_entry (progress : P.Progress) {s : State V M}
    (rs : P.Reachable s) (p : Bool) (hp : (s p).phase = .trying)
    (dead : (s (!p)).value = P.dead) :
    ∃ n, 0 < n ∧ (P.solo s p n p).phase = .cs ∧
      ∀ k, k < n → (P.solo s p k p).phase = .trying := by
  let t := P.next s (.fail (!p))
  have rt : P.Reachable t := .step (.fail (!p)) rs
  have same : s p = t p := by cases p <;> simp [t, next]
  have down : (t (!p)).phase = .down := by simp [t, next]
  obtain ⟨n, pos, hn, before⟩ := P.solo_first_entry progress rt p (by rw [← same]; exact hp) down
  have eq := P.solo_transfer s t p same (by simp [t, next, dead])
  exact ⟨n, pos, by rw [eq]; exact hn, fun k hk => by rw [eq]; exact before k hk⟩

/-- One boundary of the bypass schedule: the victim's exact history record,
with a critical peer. Reachability is evidence, never a supplied scheduler law. -/
def BypassReady (g : V) (p : Bool) (s : State V M) (k : Nat) : Prop :=
  P.Reachable s ∧ s p = P.against g p k ∧
    (s (!p)).phase = .cs ∧ (s (!p)).value = g

/-- Advance the victim, complete the peer's current visit, then actually fail,
restart and request the peer and let it enter again. -/
def bypassCommands (p : Bool) (d e : Nat) : List Command :=
  List.replicate d (.run p) ++
    [.complete (!p), .fail (!p), .restart (!p), .request (!p)] ++
      List.replicate e (.run (!p))

/-- The finite regenerative step behind infinite bypass. Both instruction
counts are positive. No solo-service, reachability or finite-memory assumption
is added: the peer entry is derived from initialized request progress. -/
theorem bypass_segment (safe : P.Safe) (progress : P.Progress) (g : V)
    (binary : ∀ v : V, v = P.dead ∨ v = g) (p : Bool)
    (cofinal : ∀ n, ∃ m, n ≤ m ∧ (P.against g p m).value = P.dead)
    {s : State V M} {k : Nat} (ready : P.BypassReady g p s k) :
    ∃ d e t, 0 < d ∧ 0 < e ∧
      P.lts.MTr s (bypassCommands p d e) t ∧ P.BypassReady g p t (k + d) ∧
      (P.solo s p d p).value = P.dead ∧
      (P.solo s p d (!p)).phase = .cs := by
  obtain ⟨m, hkm, hm⟩ := cofinal (k + 1)
  let d := m - k
  have dpos : 0 < d := by dsimp [d]; omega
  have kd : k + d = m := by dsimp [d]; omega
  let a := P.solo s p d
  have ra := P.solo_reachable ready.1 p d
  have ap : a p = P.against g p m := by
    simpa only [a, kd] using P.against_tail s g p k ready.2.1 ready.2.2.2 d
  have adead : (a p).value = P.dead := by rw [ap]; exact hm
  have acs : (a (!p)).phase = .cs := by simpa only [a, solo_other] using ready.2.2.1
  let b := P.newRequest (P.next a (.complete (!p))) (!p)
  have rb : P.Reachable b := P.newRequest_reachable (.step (.complete (!p)) ra) (!p)
  have bp : b p = a p := by
    cases p <;> simp [b, newRequest, next]
  have bq : b (!p) = P.waitingStart (!p) := P.newRequest_self _ _
  obtain ⟨e, epos, ecs, _⟩ := P.dead_peer_first_entry progress rb (!p)
    (by simp [bq, waitingStart]) (by simpa only [Bool.not_not, bp] using adead)
  let t := P.solo b (!p) e
  have rt : P.Reachable t := P.solo_reachable rb (!p) e
  have tp : t p = P.against g p (k + d) := by
    have h := P.solo_other b (!p) e
    have h' : t p = b p := by simpa only [Bool.not_not] using h
    rw [h', bp, ap, kd]
  have tg : (t (!p)).value = g := P.critical_binary safe progress g binary rt (!p) ecs
    (by simpa only [Bool.not_not, tp] using P.against_pending safe progress g binary p (k + d))
  have resetPath : P.lts.MTr a
      [.complete (!p), .fail (!p), .restart (!p), .request (!p)] b :=
    .stepL rfl (.stepL rfl (.stepL rfl (.stepL rfl .refl)))
  refine ⟨d, e, t, dpos, epos, ?_, ⟨rt, tp, ecs, tg⟩, adead, acs⟩
  exact ((P.solo_path s p d).comp P.lts resetPath).comp P.lts (P.solo_path b (!p) e)

/-- Every command belonging to every finite block occurs arbitrarily late in
CSLib's infinite concatenation. Positive block lengths preclude Zeno indexing. -/
theorem flatten_cofinal_command (ls : Cslib.ωSequence (List Command))
    (pos : ∀ k, 0 < (ls k).length) (c : Command) (mem : ∀ k, c ∈ ls k) :
    letI : Inhabited Command := ⟨.stutter⟩
    ∀ n, ∃ m, n ≤ m ∧ ls.flatten m = c := by
  let : Inhabited Command := ⟨.stutter⟩
  intro n
  have hm : c ∈ ls.flatten.extract (ls.cumLen n) (ls.cumLen (n + 1)) := by
    rw [Cslib.ωSequence.extract_flatten pos]; exact mem n
  rw [Cslib.ωSequence.extract_eq_ofFn, List.mem_ofFn] at hm
  obtain ⟨i, hi⟩ := hm
  exact ⟨ls.cumLen n + i, Nat.le_trans ((Cslib.ωSequence.cumLen_strictMono pos).id_le n)
    (Nat.le_add_right _ _), hi⟩

/-- The cofinal-dead branch gives a real admissible starvation continuation.
Each block advances the same victim history and completes/resets/requests the
peer before its next entry. Only the peer fails in this infinite suffix. -/
theorem cofinal_bypass (safe : P.Safe) (progress : P.Progress) (g : V)
    (binary : ∀ v : V, v = P.dead ∨ v = g) (p : Bool)
    (cofinal : ∀ n, ∃ m, n ≤ m ∧ (P.against g p m).value = P.dead) :
    ∃ r : P.Run, P.Reachable (r.state 0) ∧ P.Admissible r ∧
      (∀ n, (r.state n p).phase = .trying) ∧
      (∀ n, r.command n ≠ .fail p) ∧
      (∀ n, ∃ m, n ≤ m ∧ r.command m = .run p) ∧
      ¬ P.RequestProgress r := by
  classical
  let : Inhabited Command := ⟨.stutter⟩
  let Point := { a : State V M × Nat // P.BypassReady g p a.1 a.2 }
  obtain ⟨s, rs, sp, sc, sg⟩ := P.initial_critical_twin safe progress g binary p
  let x0 : Point := ⟨(s, 0), rs, sp, sc, sg⟩
  have step (x : Point) := P.bypass_segment safe progress g binary p cofinal x.property
  choose d e t hd he path ready dead critical using step
  let advance (x : Point) : Point := ⟨(t x, x.val.2 + d x), ready x⟩
  let xs : Nat → Point := fun n => Nat.rec x0 (fun _ x => advance x) n
  let ls : Cslib.ωSequence (List Command) := fun n => bypassCommands p (d (xs n)) (e (xs n))
  have pos : ∀ n, 0 < (ls n).length := by intro n; simp [ls, bypassCommands]
  have paths : ∀ n, P.lts.MTr (xs n).val.1 (ls n) (xs (n + 1)).val.1 := by
    intro n; exact path (xs n)
  obtain ⟨ss, valid, boundary⟩ := Cslib.LTS.OmegaExecution.flatten_mTr
    (lts := P.lts) (ts := Cslib.ωSequence.mk (fun n => (xs n).val.1)) (μls := ls) paths pos
  let r : P.Run := ⟨ss, ls.flatten, valid⟩
  have init : r.state 0 = s := by
    simpa only [Cslib.ωSequence.cumLen_zero, Cslib.ωSequence.get_fun, xs, Nat.rec_zero, x0, r]
      using boundary 0
  have never : ∀ n, r.command n ≠ .fail p ∧ r.command n ≠ .complete p := by
    apply (Cslib.ωSequence.forall_flatten_iff pos
      (fun c => c ≠ .fail p ∧ c ≠ .complete p)).2
    intro k
    cases p <;> simp [ls, bypassCommands, List.forall_iff_forall_mem] <;>
      intro c hc <;> rcases hc with ⟨_, rfl⟩ | rfl | rfl | rfl | rfl | ⟨_, rfl⟩ <;> simp
  have runs : ∀ n, ∃ m, n ≤ m ∧ r.command m = .run p := by
    apply flatten_cofinal_command ls pos (.run p)
    intro n
    have h := hd (xs n)
    simp [ls, bypassCommands, List.mem_replicate, Nat.ne_of_gt h]
  have failures : ∀ n, ∃ m, n ≤ m ∧ r.command m = .fail (!p) := by
    apply flatten_cofinal_command ls pos (.fail (!p))
    intro n; simp [ls, bypassCommands]
  have pending_boundary : ∀ k, (r.state (ls.cumLen k) p).phase = .trying := by
    intro k
    change (ss (ls.cumLen k) p).phase = .trying
    rw [boundary k, Cslib.ωSequence.get_fun, (xs k).property.2.1]
    exact P.against_pending safe progress g binary p _
  have noncritical : ∀ n, (r.state n p).phase ≠ .cs := by
    intro n hc
    have keep : ∀ m, n ≤ m → (r.state m p).phase = .cs := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact hc
      | succ m hm ih =>
        rw [← r.valid m]
        apply P.critical_persists _ _ p ih
        rintro (⟨hh, _⟩ | hh)
        · exact (never m).2 hh
        · exact (never m).1 hh
    have hh := keep (ls.cumLen n) ((Cslib.ωSequence.cumLen_strictMono pos).id_le n)
    rw [pending_boundary n] at hh
    cases hh
  have pending : ∀ n, (r.state n p).phase = .trying := by
    intro n
    induction n with
    | zero => simpa only [Cslib.ωSequence.cumLen_zero] using pending_boundary 0
    | succ n ih =>
      rw [← r.valid n]
      apply P.pending_persists _ _ p ih ?_ (never n).1
      intro entry
      exact noncritical (n + 1) (by rw [← r.valid n]; exact entry.2.2)
  have adm : P.Admissible r := by
    constructor
    · intro n q _
      by_cases h : q = p
      · subst q
        obtain ⟨m, hm, hc⟩ := runs n
        exact ⟨m, hm, Or.inl hc⟩
      · have hq : q = !p := by cases p <;> cases q <;> simp_all
        subst q
        obtain ⟨m, hm, hc⟩ := failures n
        exact ⟨m, hm, Or.inr hc⟩
    · intro n q hq
      by_cases h : q = p
      · subst q; exact False.elim (noncritical n hq)
      · have eq : q = !p := by cases p <;> cases q <;> simp_all
        subst q
        obtain ⟨m, hm, hc⟩ := failures n
        exact ⟨m, hm, Or.inr hc⟩
  refine ⟨r, init.symm ▸ rs, adm, pending, fun n => (never n).1, runs, ?_⟩
  intro hp
  obtain ⟨m, _, hm⟩ := hp 0 p (pending 0)
  rcases hm with hm | hm
  · exact noncritical (m + 1) (by rw [← r.valid m]; exact hm.2.2)
  · exact (never m).1 hm

/-- No deterministic program in the reviewed two-owner grammar with at most
two visible values satisfies both initialized safety and initialized progress.
Repeated peer failures are allowed; the separate failure-free claim is open. -/
theorem binary_impossibility (g : V) (binary : ∀ v : V, v = P.dead ∨ v = g) :
    ¬ (P.Safe ∧ P.Progress) := by
  rintro ⟨safe, progress⟩
  obtain ⟨p, cofinal⟩ := P.binary_cofinal_dead safe progress g binary
  obtain ⟨r, reach, adm, _, _, _, bad⟩ := P.cofinal_bypass safe progress g binary p cofinal
  exact bad (P.progress_reachable progress reach r rfl adm)

end EconomicalSolutions.TwoState.Program

#print axioms EconomicalSolutions.TwoState.Program.against_tail
#print axioms EconomicalSolutions.TwoState.Program.dead_peer_first_entry
#print axioms EconomicalSolutions.TwoState.Program.bypass_segment
#print axioms EconomicalSolutions.TwoState.Program.flatten_cofinal_command
#print axioms EconomicalSolutions.TwoState.Program.cofinal_bypass
#print axioms EconomicalSolutions.TwoState.Program.binary_impossibility
