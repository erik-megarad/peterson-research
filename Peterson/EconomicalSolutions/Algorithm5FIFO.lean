import Peterson.EconomicalSolutions.Algorithm5Invariant

namespace EconomicalSolutions.Algorithm5

/-- Control locations belonging to the same queued, not-yet-entered episode. -/
def QueuedPending {n : Nat} (pc : PC n) : Prop :=
  match pc with
  | .complete | .depart | .test | .absent _ _ | .prepare _ | .decrement _ | .enter => True
  | _ => False

theorem queued_nonnegative {n : Nat} {s : State n} {p : Proc n}
    (facts : QueueFacts s p) (pending : QueuedPending (s p).pc) :
    0 ≤ priority s p := by
  cases hp : (s p).pc <;> simp_all [QueuedPending, QueueFacts] <;> omega

/-- An uninterrupted queued episode stays queued and either retains its number
or decreases it by exactly one on its own ordinary instruction. -/
theorem queued_ordinary {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {l : Local n} (facts : QueueFacts s p) (pending : QueuedPending (s p).pc)
    (noEntry : label s (.run p) ≠ .entry p) (step : ordinary cfg s p = some l) :
    QueuedPending l.pc ∧
      (l.value.priority = priority s p ∨ l.value.priority = priority s p - 1) := by
  cases hp : (s p).pc <;> simp only [QueuedPending, hp] at pending
  all_goals try (rename_i rest k; cases rest)
  all_goals simp only [ordinary, hp] at step
  all_goals try (split at step)
  all_goals simp only [Option.some.injEq] at step
  all_goals subst l
  all_goals simp_all [QueuedPending, QueueFacts, label, priority]

/-- The interval excludes own entry and abort, not other processes' events.
It permits indefinitely delayed instructions and arbitrary peer restarts. -/
theorem queued_next {n : Nat} {cfg : Config n} {s t : State n} {p : Proc n}
    {c : Command n} (inv : Invariant s) (pending : QueuedPending (s p).pc)
    (noEntry : label s c ≠ .entry p) (noFail : label s c ≠ .fail p)
    (step : next cfg s c = some t) :
    QueuedPending (t p).pc ∧
      (priority t p = priority s p ∨ priority t p = priority s p - 1) := by
  cases c with
  | stutter => simp only [next, Option.some.injEq] at step; subst t; exact ⟨pending, Or.inl rfl⟩
  | run actor =>
    simp only [next] at step
    cases ho : ordinary cfg s actor with
    | none => simp [ho] at step
    | some l =>
      simp only [ho, Option.map_some, Option.some.injEq] at step; subst t
      by_cases eq : p = actor
      · subst actor
        simpa only [priority, setLocal_self] using queued_ordinary (inv.facts p) pending noEntry ho
      · simpa [priority, eq] using And.intro pending (Or.inl (Eq.refl (priority s p)) :
          priority s p = priority s p ∨ priority s p = priority s p - 1)
  | fail actor =>
    have other : p ≠ actor := by intro eq; subst actor; exact noFail rfl
    simp only [next] at step
    split at step
    · contradiction
    · simp only [Option.some.injEq] at step; subst t
      simpa [priority, other] using And.intro pending (Or.inl (Eq.refl (priority s p)) :
        priority s p = priority s p ∨ priority s p = priority s p - 1)
  | restart actor =>
    simp only [next] at step
    split at step
    · rename_i down
      have other : p ≠ actor := by
        intro eq; subst actor; simp [down, QueuedPending] at pending
      simp only [Option.some.injEq] at step; subst t
      simpa [priority, other] using And.intro pending (Or.inl (Eq.refl (priority s p)) :
        priority s p = priority s p ∨ priority s p = priority s p - 1)
    · contradiction

/-- Arrival is the actual separate step-3 write. Its ordering fact is derived
from the scanned-history invariant, not supplied by an execution premise. -/
theorem enqueue_next {n : Nat} {cfg : Config n} {s t : State n} {p : Proc n}
    {c : Command n} (reach : Reachable cfg s) (step : next cfg s c = some t)
    (event : label s c = .enqueue p) :
    QueuedPending (t p).pc ∧ 0 ≤ priority t p ∧
      (∀ q, q ≠ p → priority t q < priority t p) := by
  cases c with
  | fail actor | restart actor | stutter => simp [label] at event
  | run actor =>
    cases hp : (s actor).pc <;> simp only [label, hp] at event
    all_goals try contradiction
    rename_i v
    cases event
    have facts := (reachable_invariant reach).facts p
    simp only [QueueFacts, hp] at facts
    simp only [next, ordinary, hp, Option.map_some, Option.some.injEq] at step
    subst t
    refine ⟨by simp [QueuedPending], by simpa only [priority, setLocal_self] using facts.2.1, ?_⟩
    intro q other
    simpa only [priority, setLocal_self, setLocal_other s p q _ other] using facts.2.2.2 q other

theorem entry_zero {n : Nat} {cfg : Config n} {s : State n} {p : Proc n}
    {c : Command n} (reach : Reachable cfg s) (event : label s c = .entry p) :
    priority s p = 0 := by
  cases c with
  | fail actor | restart actor | stutter => simp [label] at event
  | run actor =>
    cases hp : (s actor).pc <;> simp only [label, hp] at event
    all_goals try contradiction
    cases event
    simpa only [QueueFacts, hp] using (reachable_invariant reach).facts p

/-- Single decrements cannot cross a surviving smaller number: meeting it
would contradict the independently proved successor-state uniqueness. -/
theorem queued_order_next {n : Nat} {cfg : Config n} {s t : State n}
    {a b : Proc n} {c : Command n} (reach : Reachable cfg s)
    (step : next cfg s c = some t) (different : a ≠ b)
    (pa : QueuedPending (s a).pc) (pb : QueuedPending (s b).pc)
    (ae : label s c ≠ .entry a) (af : label s c ≠ .fail a)
    (be : label s c ≠ .entry b) (bf : label s c ≠ .fail b)
    (ordered : priority s a < priority s b) : priority t a < priority t b := by
  have inv := reachable_invariant reach
  obtain ⟨ta, da⟩ := queued_next inv pa ae af step
  obtain ⟨_, db⟩ := queued_next inv pb be bf step
  have ti := invariant_next reach inv step
  have nonnegative := queued_nonnegative (ti.facts a) ta
  have distinct : priority t a ≠ priority t b := by
    intro eq; exact different (ti.unique a b nonnegative eq)
  rcases da with da | da <;> rcases db with db | db <;> omega

/-- Only the indicated finite prefix must execute; values outside it carry no
semantic obligation. Event index k labels the transition from state k to k+1. -/
structure FiniteExecution {n : Nat} (cfg : Config n) (length : Nat) where
  state : Nat → State n
  command : Nat → Command n
  initialized : state 0 = initial n
  step : ∀ k, k < length → next cfg (state k) (command k) = some (state (k + 1))

def FiniteExecution.event {n length : Nat} {cfg : Config n}
    (run : FiniteExecution cfg length) (k : Nat) : Label n :=
  label (run.state k) (run.command k)

theorem FiniteExecution.reachable {n length : Nat} {cfg : Config n}
    (run : FiniteExecution cfg length) {k : Nat} (bound : k ≤ length) :
    Reachable cfg (run.state k) := by
  induction k with
  | zero => rw [run.initialized]; exact .initial
  | succ k ih => exact .step (ih (by omega)) ⟨run.command k, run.step k (by omega), rfl⟩

/-- History identifies one exact request by its enqueue occurrence. Between
that occurrence and the endpoint, neither its entry nor its failure occurs.
No absence of peer failures, scheduling, or eventual-entry premise is added. -/
def EpisodeInterval {n length : Nat} {cfg : Config n}
    (run : FiniteExecution cfg length) (p : Proc n) (enqueue endPoint : Nat) : Prop :=
  enqueue < endPoint ∧ endPoint ≤ length ∧ run.event enqueue = .enqueue p ∧
    ∀ k, enqueue < k → k < endPoint →
      run.event k ≠ .entry p ∧ run.event k ≠ .fail p

theorem episode_pending {n length : Nat} {cfg : Config n}
    {run : FiniteExecution cfg length} {p : Proc n} {e t : Nat}
    (episode : EpisodeInterval run p e t) {k : Nat} (after : e < k) (before : k ≤ t) :
    QueuedPending (run.state k p).pc := by
  obtain ⟨et, tl, enqueue, uninterrupted⟩ := episode
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases first : k = e
    · subst k
      exact (enqueue_next (run.reachable (by omega)) (run.step e (by omega)) enqueue).1
    · have kp : QueuedPending (run.state k p).pc := ih (by omega) (by omega)
      have events := uninterrupted k (by omega) (by omega)
      exact (queued_next (reachable_invariant (run.reachable (by omega))) kp
        events.1 events.2 (run.step k (by omega))).1

/-- Throughout the overlap of the two exact episodes, their numerical order
is retained. The base case uses B's actual enqueue write. -/
theorem episode_priority_order {n length : Nat} {cfg : Config n}
    {run : FiniteExecution cfg length} {a b : Proc n} {ea eb t : Nat}
    (different : a ≠ b) (arrival : ea < eb)
    (aEpisode : EpisodeInterval run a ea t) (bEpisode : EpisodeInterval run b eb t)
    {k : Nat} (after : eb < k) (before : k ≤ t) :
    priority (run.state k) a < priority (run.state k) b := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases first : k = eb
    · subst k
      exact (enqueue_next (run.reachable (by have := bEpisode.2.1; omega))
        (run.step eb (by have := bEpisode.1; have := bEpisode.2.1; omega))
        bEpisode.2.2.1).2.2 a different
    · have ek : eb < k := by omega
      have kt : k < t := by omega
      have ae := aEpisode.2.2.2 k (by omega) kt
      have be := bEpisode.2.2.2 k ek kt
      exact queued_order_next (run.reachable (by have := bEpisode.2.1; omega))
        (run.step k (by have := bEpisode.2.1; omega)) different
        (episode_pending aEpisode (by omega) (by omega))
        (episode_pending bEpisode ek (by omega)) ae.1 ae.2 be.1 be.2
        (ih ek (by omega))

/-- Finite-prefix FIFO after the doorway. Even if A will wait forever, B's
entry cannot be the first entry-or-failure ending either exact queued episode.
No fairness, eventual entry, queue-order premise, or restart continuation. -/
theorem finite_prefix_fifo {n length : Nat} {cfg : Config n}
    {run : FiniteExecution cfg length} {a b : Proc n} {ea eb t : Nat}
    (different : a ≠ b) (arrival : ea < eb)
    (aEpisode : EpisodeInterval run a ea t) (bEpisode : EpisodeInterval run b eb t)
    (inPrefix : t < length) : run.event t ≠ .entry b := by
  intro entry
  have ordered := episode_priority_order different arrival aEpisode bEpisode bEpisode.1 (Nat.le_refl t)
  have zero := entry_zero (run.reachable (Nat.le_of_lt inPrefix)) entry
  have nonnegative := queued_nonnegative ((reachable_invariant
    (run.reachable (Nat.le_of_lt inPrefix))).facts a)
  have active := episode_pending aEpisode aEpisode.1 (Nat.le_refl t)
  have := nonnegative active
  omega

theorem EpisodeInterval.restrict {n length : Nat} {cfg : Config n}
    {run : FiniteExecution cfg length} {p : Proc n} {e t u : Nat}
    (episode : EpisodeInterval run p e t) (after : e < u) (before : u ≤ t) :
    EpisodeInterval run p e u := by
  refine ⟨after, Nat.le_trans before episode.2.1, episode.2.2.1, ?_⟩
  intro k ek ku
  exact episode.2.2.2 k ek (by omega)

/-- Entry of this occurrence of a queued request, with no intervening own
entry or failure that could instead make it a replacement request. -/
def EpisodeEntry {n length : Nat} {cfg : Config n}
    (run : FiniteExecution cfg length) (p : Proc n) (enqueue entry : Nat) : Prop :=
  EpisodeInterval run p enqueue entry ∧ entry < length ∧ run.event entry = .entry p

/-- When both exact surviving episodes enter, entries respect enqueue order.
The finite-prefix theorem above is stronger: it does not require A's entry. -/
theorem fifo_entry_order {n length : Nat} {cfg : Config n}
    {run : FiniteExecution cfg length} {a b : Proc n} {ea eb ta tb : Nat}
    (different : a ≠ b) (arrival : ea < eb)
    (aEntry : EpisodeEntry run a ea ta) (bEntry : EpisodeEntry run b eb tb) : ta < tb := by
  by_contra h
  have ba : tb ≤ ta := by omega
  exact finite_prefix_fifo different arrival
    (aEntry.1.restrict (by have := bEntry.1.1; omega) ba)
    bEntry.1 bEntry.2.1 bEntry.2.2

/-- An abort inside the interval invalidates that identity, regardless of
whether the same process later restarts and enqueues another request. -/
theorem failure_breaks_episode {n length : Nat} {cfg : Config n}
    {run : FiniteExecution cfg length} {p : Proc n} {e t k : Nat}
    (after : e < k) (before : k < t) (failure : run.event k = .fail p) :
    ¬ EpisodeInterval run p e t := by
  intro episode
  exact (episode.2.2.2 k after before).2 failure

end EconomicalSolutions.Algorithm5

#print axioms EconomicalSolutions.Algorithm5.enqueue_next
#print axioms EconomicalSolutions.Algorithm5.episode_pending
#print axioms EconomicalSolutions.Algorithm5.episode_priority_order
#print axioms EconomicalSolutions.Algorithm5.finite_prefix_fifo
#print axioms EconomicalSolutions.Algorithm5.fifo_entry_order
#print axioms EconomicalSolutions.Algorithm5.failure_breaks_episode
