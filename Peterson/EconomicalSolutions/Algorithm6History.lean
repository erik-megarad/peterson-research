module

public import Peterson.EconomicalSolutions.Algorithm6Invariant

@[expose] public section

namespace EconomicalSolutions.Algorithm6

/-- The history is the actual interpreter execution, with no extra witnesses
of list order, admission, or clock success supplied by the caller. -/
def ValidPrefix {n : Nat} (cfg : Config n) (trace : Nat → State n)
    (commands : Nat → Command n) (finish : Nat) : Prop :=
  trace 0 = initial n ∧ ∀ t, t < finish → next cfg (trace t) (commands t) = some (trace (t + 1))

theorem prefix_reachable {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish t : Nat}
    (valid : ValidPrefix cfg trace commands finish) (bound : t ≤ finish) : Reachable cfg (trace t) := by
  induction t with
  | zero => rw [valid.1]; exact .initial
  | succ t ih =>
    exact .step (ih (by omega)) ⟨commands t, valid.2 t (by omega), rfl⟩

theorem held_invisible {n : Nat} {l : Local n} (facts : LocalFacts l)
    (held : Holding l.pc) : visible l.value.clock = false := by
  cases hp : l.pc <;> simp_all [Holding, LocalFacts]

/-- The completed mixed-time scan still includes every currently visible
peer at the actual enqueue event. Peers that disappeared and restarted during
that scan cannot republish lower while admission remains held. -/
theorem enqueue_includes {n : Nat} {cfg : Config n} {s t : State n} {p q : Proc n}
    {b : Bool} (reach : Reachable cfg s) (pc : (s p).pc = .enqueue b) (other : q ≠ p)
    (vis : visible (s q).value.clock = true) (step : next cfg s (.run p) = some t) :
    q ∈ (t p).behind := by
  have scan := (reachable_invariant reach).scanFacts p
  simp only [ScanFacts, pc] at scan
  have mem : q ∈ (s p).behind := by simpa using scan q other vis
  simp only [next, ordinary, pc, Option.map_some, Option.some.injEq] at step
  subst t
  simpa using mem

/-- A queued owner's list cannot lose a continuously visible identifier in
one concrete step. The visibility of the owner after the step excludes abort
and release; prior visibility excludes a replacement enqueue episode. -/
theorem next_retains_member {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    {p q : Proc n} (reach : Reachable cfg s) (step : next cfg s c = some t)
    (own : visible (s p).value.clock = true) (after : visible (t p).value.clock = true)
    (peer : visible (s q).value.clock = true) (mem : q ∈ (s p).behind) : q ∈ (t p).behind := by
  cases c with
  | stutter => have eq : s = t := Option.some.inj step; simpa [← eq] using mem
  | run actor =>
    obtain ⟨l, h, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor
      have inv := reachable_invariant reach
      have change := ordinary_change (inv.localFacts p) (inv.scanFacts p) h
      simp only [setLocal_self] at after ⊢
      cases change with
      | gone gone => simp [gone] at after
      | retained _ keep => exact keep q peer mem
      | arrival held _ => have := held_invisible (inv.localFacts p) held; simp_all
    · simpa [eq] using mem
  | fail actor | restart actor =>
    simp only [next] at step
    split at step
    all_goals try contradiction
    all_goals simp only [Option.some.injEq] at step
    all_goals subst t
    all_goals by_cases eq : p = actor
    all_goals first
      | (subst actor; simp [reset, dead, visible] at after)
      | simpa [eq] using mem

/-- A precise surviving interval, reconstructed from concrete states. A reset
creates an off state and therefore cannot be concealed inside this interval. -/
def VisibleDuring {n : Nat} (trace : Nat → State n) (p : Proc n) (a b : Nat) : Prop :=
  ∀ t, a ≤ t → t ≤ b → visible (trace t p).value.clock = true

theorem member_persists {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (ab : a ≤ b) (bf : b ≤ finish)
    (owner : VisibleDuring trace p a b) (peer : VisibleDuring trace q a b)
    (mem : q ∈ (trace a p).behind) : q ∈ (trace b p).behind := by
  induction b, ab using Nat.le_induction with
  | base => exact mem
  | succ b ab ih =>
    have old := ih (by omega) (by intro t lo hi; exact owner t lo (by omega))
      (by intro t lo hi; exact peer t lo (by omega))
    exact next_retains_member (prefix_reachable valid (by omega)) (valid.2 b (by omega))
      (owner b ab (by omega)) (owner (b + 1) (by omega) (le_refl _))
      (peer b ab (by omega)) old

/-- The earlier visible episode remains in the later entrant's list throughout
both surviving intervals, even while instructions, failures of other processes,
and restarts are interleaved. This is derived from the actual enqueue and reads. -/
theorem enqueued_blocker_persists {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b : Nat} {p q : Proc n} {bit : Bool}
    (valid : ValidPrefix cfg trace commands finish) (ab : a + 1 ≤ b) (bf : b ≤ finish)
    (atTime : (trace a p).pc = .enqueue bit) (command : commands a = .run p) (other : q ≠ p)
    (owner : VisibleDuring trace p (a + 1) b) (peer : VisibleDuring trace q a b) :
    q ∈ (trace b p).behind := by
  apply member_persists valid ab bf owner
    (by intro t lo hi; exact peer t (by omega) hi)
  apply enqueue_includes (prefix_reachable valid (by omega)) atTime other (peer a (le_refl _) (by omega))
  simpa [command] using valid.2 a (by omega)

theorem visible_interval_no_failure {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b t : Nat} {p : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (vis : VisibleDuring trace p a b) (atTime : a ≤ t) (tb : t < b) : commands t ≠ .fail p := by
  intro bad
  have step := valid.2 t (by omega)
  rw [bad] at step
  simp only [next] at step
  split at step
  · contradiction
  · have eq := Option.some.inj step
    have after := vis (t + 1) (by omega) (by omega)
    rw [← eq] at after
    simp [reset, dead, visible] at after

theorem finite_execution_safety {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish : Nat} (valid : ValidPrefix cfg trace commands finish) :
    ∀ t, t ≤ finish → MutualExclusion (trace t) := by
  intro t bound
  exact safety n cfg (trace t) (prefix_reachable valid bound)

/-- Controls of the original enqueued episode before its first outer entry.
Unlike visibility alone this excludes completed episodes and their release. -/
def Queued {n : Nat} (pc : PC n) : Prop :=
  match pc with
  | .maintain _ | .lowerTick _ | .test | .publish | .enter => True
  | _ => False

theorem queued_visible {n : Nat} {l : Local n} (facts : LocalFacts l)
    (queued : Queued l.pc) : visible l.value.clock = true := by
  cases hp : l.pc <;> cases ht : l.value.clock <;> simp_all [Queued, LocalFacts, visible]

theorem enqueue_event_iff {n : Nat} {s : State n} {c : Command n} {p : Proc n} :
    label s c = .enqueue p ↔ c = .run p ∧ ∃ b, (s p).pc = .enqueue b := by
  cases c <;> simp only [label]
  case run q =>
    by_cases eq : q = p
    · subst q
      cases hp : (s p).pc
      case' upperJoin cp => cases cp
      case' upperTick count cp => cases cp
      case' lowerTick cp => cases cp
      all_goals simp_all
    · cases hp : (s q).pc
      case' upperJoin cp => cases cp
      case' upperTick count cp => cases cp
      case' lowerTick cp => cases cp
      all_goals simp_all
  all_goals simp

theorem entry_event_iff {n : Nat} {s : State n} {c : Command n} {p : Proc n} :
    label s c = .entry p ↔ c = .run p ∧ (s p).pc = .enter := by
  cases c <;> simp only [label]
  case run q =>
    by_cases eq : q = p
    · subst q
      cases hp : (s p).pc
      case' upperJoin cp => cases cp
      case' upperTick count cp => cases cp
      case' lowerTick cp => cases cp
      all_goals simp_all
    · cases hp : (s q).pc
      case' upperJoin cp => cases cp
      case' upperTick count cp => cases cp
      case' lowerTick cp => cases cp
      all_goals simp_all
  all_goals simp

theorem enqueue_queued {n : Nat} {cfg : Config n} {s t : State n}
    {c : Command n} {p : Proc n} (step : next cfg s c = some t)
    (event : label s c = .enqueue p) : Queued (t p).pc := by
  obtain ⟨rfl, b, pc⟩ := enqueue_event_iff.mp event
  simp only [next, ordinary, pc, Option.map_some, Option.some.injEq] at step
  subst t
  simp [Queued]

/-- Only the episode's own entry or failure can end its queued phase.
In particular a restart or replacement cannot be hidden in this interval. -/
theorem next_queued {n : Nat} {cfg : Config n} {s t : State n} {c : Command n}
    {p : Proc n} (queued : Queued (s p).pc) (step : next cfg s c = some t)
    (noEntry : label s c ≠ .entry p) (noAbort : label s c ≠ .fail p) : Queued (t p).pc := by
  cases c with
  | stutter => have eq := Option.some.inj step; simpa [← eq] using queued
  | run actor =>
    obtain ⟨l, h, rfl⟩ := Option.map_eq_some_iff.mp step
    by_cases eq : p = actor
    · subst actor
      simp only [setLocal_self]
      cases hp : (s p).pc <;> simp only [hp, Queued] at queued
      case maintain rest =>
        cases rest <;> simp only [ordinary, hp, Option.some.injEq] at h <;> subst l <;> trivial
      case lowerTick cp =>
        simp only [ordinary, hp] at h
        obtain ⟨cl, _, rfl⟩ := Option.map_eq_some_iff.mp h
        dsimp only
        split <;> trivial
      case test => simp only [ordinary, hp, Option.some.injEq] at h; subst l; dsimp only; split <;> trivial
      case publish => simp only [ordinary, hp, Option.some.injEq] at h; subst l; trivial
      case enter => simp [label, hp] at noEntry
    · simpa [eq] using queued
  | fail actor =>
    have ne : p ≠ actor := by intro eq; subst actor; exact noAbort rfl
    simp only [next] at step
    split at step
    · contradiction
    · have eq := Option.some.inj step; simpa [← eq, ne] using queued
  | restart actor =>
    simp only [next] at step
    split at step
    · rename_i down
      have ne : p ≠ actor := by intro eq; subst actor; simp [down, Queued] at queued
      have eq := Option.some.inj step; simpa [← eq, ne] using queued
    · contradiction

/-- Entry or abort ends the pending obligation of this episode. -/
def Resolves {n : Nat} (event : Label n) (p : Proc n) : Prop :=
  event = .entry p ∨ event = .fail p

theorem queued_until_resolution {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b : Nat} {p : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (ab : a + 1 ≤ b) (bf : b ≤ finish)
    (arrival : label (trace a) (commands a) = .enqueue p)
    (unresolved : ∀ t, a < t → t < b → ¬ Resolves (label (trace t) (commands t)) p) :
    Queued (trace b p).pc := by
  induction b, ab using Nat.le_induction with
  | base => exact enqueue_queued (valid.2 a (by omega)) arrival
  | succ b ab ih =>
    have old := ih (by omega) (by intro t lo hi; exact unresolved t lo (by omega))
    exact next_queued old (valid.2 b (by omega))
      (fun h => unresolved b (by omega) (by omega) (Or.inl h))
      (fun h => unresolved b (by omega) (by omega) (Or.inr h))

theorem visible_until_resolution {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b : Nat} {p : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (bf : b ≤ finish)
    (arrival : label (trace a) (commands a) = .enqueue p)
    (unresolved : ∀ t, a < t → t < b → ¬ Resolves (label (trace t) (commands t)) p) :
    VisibleDuring trace p (a + 1) b := by
  intro t lo hi
  exact queued_visible ((reachable_invariant (prefix_reachable valid (by omega : t ≤ finish))).localFacts p)
    (queued_until_resolution valid lo (by omega) arrival
      (by intro u au ut; exact unresolved u au (by omega)))

/-- Two arrivals of one identifier belong to different episodes: the earlier
one must have entered or aborted before the later arrival. -/
theorem same_identifier_resolves_before_enqueue {n : Nat} {cfg : Config n}
    {trace : Nat → State n} {commands : Nat → Command n} {finish a b : Nat} {p : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (ab : a < b) (bf : b < finish)
    (first : label (trace a) (commands a) = .enqueue p)
    (second : label (trace b) (commands b) = .enqueue p) :
    ∃ t, a < t ∧ t < b ∧ Resolves (label (trace t) (commands t)) p := by
  by_contra absent
  have pending := queued_until_resolution valid (by omega : a + 1 ≤ b) (by omega) first
    (by intro t lo hi res; exact absent ⟨t, lo, hi, res⟩)
  obtain ⟨_, bit, pc⟩ := enqueue_event_iff.mp second
  simp [pc, Queued] at pending

/-- FIFO follows actual enqueue/entry events. The later entry is its first
resolution after arrival; no survival or eventual-entry premise is made for A.
This includes same-identifier episodes using the separate lifecycle argument. -/
theorem finite_prefix_fifo {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b c : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (ab : a < b) (bc : b < c)
    (cf : c < finish)
    (arrivalA : label (trace a) (commands a) = .enqueue p)
    (arrivalB : label (trace b) (commands b) = .enqueue q)
    (entryB : label (trace c) (commands c) = .entry q)
    (sameEpisodeB : ∀ t, b < t → t < c → ¬ Resolves (label (trace t) (commands t)) q) :
    ∃ t, a < t ∧ t < c ∧ Resolves (label (trace t) (commands t)) p := by
  by_cases eq : p = q
  · subst q
    obtain ⟨t, lo, hi, res⟩ := same_identifier_resolves_before_enqueue valid ab
      (by omega) arrivalA arrivalB
    exact ⟨t, lo, by omega, res⟩
  · by_contra absent
    have aUnresolved : ∀ t, a < t → t < c → ¬ Resolves (label (trace t) (commands t)) p := by
      intro t lo hi res; exact absent ⟨t, lo, hi, res⟩
    have aVisible := visible_until_resolution valid (by omega : c ≤ finish) arrivalA aUnresolved
    have bVisible := visible_until_resolution valid (by omega : c ≤ finish) arrivalB sameEpisodeB
    obtain ⟨runB, bit, pcB⟩ := enqueue_event_iff.mp arrivalB
    have mem := enqueued_blocker_persists valid (by omega : b + 1 ≤ c)
      (by omega : c ≤ finish) pcB runB eq bVisible
      (by intro t lo hi; exact aVisible t (by omega) hi)
    have pcC := (entry_event_iff.mp entryB).2
    have facts := (reachable_invariant (prefix_reachable valid (by omega : c ≤ finish))).localFacts q
    simp only [LocalFacts, pcC] at facts
    simp [facts.2] at mem

/-- The witness is the first resolution of A's original episode, not an entry
of a replacement. Queued control persists throughout the preceding interval. -/
theorem finite_prefix_fifo_original_episode {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish a b c : Nat} {p q : Proc n}
    (valid : ValidPrefix cfg trace commands finish) (ab : a < b) (bc : b < c)
    (cf : c < finish)
    (arrivalA : label (trace a) (commands a) = .enqueue p)
    (arrivalB : label (trace b) (commands b) = .enqueue q)
    (entryB : label (trace c) (commands c) = .entry q)
    (sameEpisodeB : ∀ t, b < t → t < c → ¬ Resolves (label (trace t) (commands t)) q) :
    ∃ t, a < t ∧ t < c ∧ Resolves (label (trace t) (commands t)) p ∧
      (∀ u, a < u → u < t → ¬ Resolves (label (trace u) (commands u)) p) ∧
      (∀ u, a < u → u ≤ t → Queued (trace u p).pc) := by
  classical
  have existsResolution := finite_prefix_fifo valid ab bc cf arrivalA arrivalB entryB sameEpisodeB
  let t := Nat.find existsResolution
  have bounds := Nat.find_spec existsResolution
  have first : ∀ u, a < u → u < t → ¬ Resolves (label (trace u) (commands u)) p := by
    intro u lo hi res
    exact Nat.find_min existsResolution hi ⟨lo, by omega, res⟩
  refine ⟨t, bounds.1, bounds.2.1, bounds.2.2, first, ?_⟩
  intro u lo hi
  exact queued_until_resolution valid (by omega) (by omega) arrivalA
    (by intro v av vu; exact first v av (by omega))

end EconomicalSolutions.Algorithm6

#print axioms EconomicalSolutions.Algorithm6.enqueue_includes
#print axioms EconomicalSolutions.Algorithm6.member_persists
#print axioms EconomicalSolutions.Algorithm6.enqueued_blocker_persists
#print axioms EconomicalSolutions.Algorithm6.visible_interval_no_failure
#print axioms EconomicalSolutions.Algorithm6.finite_execution_safety

#print axioms EconomicalSolutions.Algorithm6.next_queued
#print axioms EconomicalSolutions.Algorithm6.queued_until_resolution
#print axioms EconomicalSolutions.Algorithm6.visible_until_resolution
#print axioms EconomicalSolutions.Algorithm6.same_identifier_resolves_before_enqueue
#print axioms EconomicalSolutions.Algorithm6.finite_prefix_fifo
#print axioms EconomicalSolutions.Algorithm6.finite_prefix_fifo_original_episode
