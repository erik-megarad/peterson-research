module
public import CircularElection.Model
public import CircularElection.Origin
public import CircularElection.Targets
public import Mathlib.Data.Finset.Max

@[expose] public section
namespace CircularElection
variable {n : Nat} {Id : Type} [LinearOrder Id]

/-- Registers count only while the protocol will still use their values. -/
def LiveLocal (v : Id) (l : Local Id) : Prop :=
  (l.pc ∈ [PC.firstSend, .firstReceive, .secondSend, .secondReceive, .compare] ∧ l.tid = v) ∨
  (l.pc ∈ [PC.secondSend, .secondReceive, .compare] ∧ l.ntid = some v) ∨
  (l.pc = .compare ∧ l.nntid = some v) ∨
  (l.pc = .relaySend ∧ l.tid = v)

/-- Immutable owner IDs, elected processes and unused registers are excluded. -/
def LiveData (v : Id) (s : State n Id) : Prop :=
  (∃ p, LiveLocal v (s.process p)) ∨
  (∃ p, v ∈ s.edge p) ∨ (∃ p, v ∈ s.inbox p)

/-- Receive counts are proof witnesses, not wire messages or protocol state.
The local equations identify alternating first/second occurrence positions. -/
def LocalCount (sent received : Nat) (pc : PC) : Prop :=
  match pc with
  | .firstSend => sent = received ∧ received % 2 = 0
  | .firstReceive => sent = received + 1 ∧ received % 2 = 0
  | .secondSend => sent = received ∧ received % 2 = 1
  | .secondReceive => sent = received + 1 ∧ received % 2 = 1
  | .compare => sent = received ∧ received % 2 = 0
  | .relayReceive => sent = received
  | .relaySend => sent + 1 = received
  | .elected => True

/-- Every sent occurrence is either received or still in its FIFO path. -/
def Counted (s : State n Id) (received : Fin n → Nat) : Prop :=
  (∀ p, LocalCount (s.sent p) (received p) (s.process p).pc) ∧
  (∀ p, s.sent p = received (next p) + (s.inbox (next p)).length + (s.edge p).length)

private theorem next_injective : Function.Injective (next (n := n)) := by
  intro p q h
  have hp := p.isLt
  have hq := q.isLt
  have he := congrArg Fin.val h
  change (p.val + 1) % n = (q.val + 1) % n at he
  by_cases hpw : p.val + 1 < n <;> by_cases hqw : q.val + 1 < n
  all_goals
    try have : p.val + 1 = n := by omega
    try have : q.val + 1 = n := by omega
    simp_all [Nat.mod_eq_of_lt]
  all_goals apply Fin.ext; omega

omit [LinearOrder Id] in
private theorem initial_counted (owner : Fin n → Id) :
    Counted (initial owner) (fun _ => 0) := by
  simp [Counted, LocalCount, initial]

/-- The receive ordinal advances precisely on a successful receive. -/
def receivedAfter (received : Fin n → Nat) : Action n → Fin n → Nat
  | .receive p => Function.update received p (received p + 1)
  | _ => received

private theorem local_count_step (owner : Id) (p : Fin n) (a : Action n)
    (l : Local Id) (q : List Id) (r : Local Id × List Id × Option Id)
    (sent received : Nat) (ha : actProcess a = some p)
    (hc : LocalCount sent received l.pc) (hs : localStep owner a l q = some r) :
    LocalCount (sent + r.2.2.toList.length)
      (received + (match a with | .receive _ => 1 | _ => 0)) r.1.pc ∧
    r.2.1.length + (match a with | .receive _ => 1 | _ => 0) = q.length := by
  rcases l with ⟨pc, tid, ntid, nntid⟩
  cases a <;> cases pc <;> simp only [localStep] at hs <;> try contradiction
  all_goals try (split at hs)
  all_goals try (split at hs)
  all_goals try (split at hs)
  all_goals cases hs
  all_goals simp_all [LocalCount]
  all_goals omega

omit [LinearOrder Id] in
private theorem commit_counted (s : State n Id) (rc : Fin n → Nat) (p : Fin n)
    (r : Local Id × List Id × Option Id) (d : Nat) (hs : Counted s rc)
    (hc : LocalCount (s.sent p + r.2.2.toList.length) (rc p + d) r.1.pc)
    (hq : r.2.1.length + d = (s.inbox p).length) :
    Counted (commitLocal s p r) (Function.update rc p (rc p + d)) := by
  rcases r with ⟨l, q, out⟩
  cases out <;> constructor
  all_goals
    intro i
    have hp := hs.1 i
    have hi := hs.2 i
    by_cases he : i = p <;> by_cases hn : next i = p <;>
      simp_all [commitLocal]
    all_goals omega

/-- A maximum in an even (zero-based) FIFO occurrence position. -/
def EvenData (v : Id) : Nat → List Id → Prop
  | _, [] => False
  | k, x :: xs => (k % 2 = 0 ∧ x = v) ∨ EvenData v (k + 1) xs

omit [LinearOrder Id] in
private theorem evenData_append (v : Id) (k : Nat) (xs ys : List Id) :
    EvenData v k (xs ++ ys) ↔ EvenData v k xs ∨ EvenData v (k + xs.length) ys := by
  induction xs generalizing k with
  | nil => simp [EvenData]
  | cons x xs ih => simp [EvenData, ih, Nat.add_comm, Nat.add_left_comm, or_assoc]

omit [LinearOrder Id] in
private theorem evenData_mem (v : Id) (k : Nat) (xs : List Id)
    (h : EvenData v k xs) : v ∈ xs := by
  induction xs generalizing k with
  | nil => exact h.elim
  | cons x xs ih =>
    rcases h with ⟨_, rfl⟩ | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem x (ih _ h)

/-- Only a first-message maximum is needed as a persistent witness. -/
def FirstLocal (v : Id) (received : Nat) (l : Local Id) : Prop :=
  match l.pc with
  | .firstSend => l.tid = v
  | .secondSend | .secondReceive | .compare => l.ntid = some v
  | .relaySend => l.tid = v ∧ received % 2 = 1
  | _ => False

def FirstLive (v : Id) (s : State n Id) (rc : Fin n → Nat) : Prop :=
  (∃ p, FirstLocal v (rc p) (s.process p)) ∨
  (∃ p, EvenData v (rc p) (s.inbox p)) ∨
  (∃ p, EvenData v (rc (next p) + (s.inbox (next p)).length) (s.edge p))

private theorem local_first_step (v owner : Id) (a : Action n)
    (l : Local Id) (q : List Id) (r : Local Id × List Id × Option Id)
    (sent received : Nat)
    (hc : LocalCount sent received l.pc) (ho : LocalOrigin (· ≤ v) l)
    (hs : localStep owner a l q = some r)
    (hf : FirstLocal v received l ∨ EvenData v received q) :
    FirstLocal v (received + (match a with | .receive _ => 1 | _ => 0)) r.1 ∨
    EvenData v (received + (match a with | .receive _ => 1 | _ => 0)) r.2.1 ∨
    (r.2.2 = some v ∧ sent % 2 = 0) ∨ r.1.pc = .elected := by
  rcases l with ⟨pc, tid, ntid, nntid⟩
  cases a <;> cases pc <;> simp only [localStep] at hs <;> try contradiction
  all_goals try (split at hs)
  all_goals try (split at hs)
  all_goals try (split at hs)
  all_goals cases hs
  all_goals simp_all [FirstLocal, LocalCount, LocalOrigin, EvenData]
  all_goals grind

private theorem step_counted (owner : Fin n → Id) {s t : State n Id}
    {a : Action n} {rc : Fin n → Nat} (hc : Counted s rc)
    (h : (lts owner).Tr s a t) : Counted t (receivedAfter rc a) := by
  change execute owner s a = some t at h
  cases a with
  | idle =>
    simp only [execute, Option.some.injEq] at h
    exact h ▸ hc
  | deliver p =>
    cases he : s.edge p with
    | nil => simp [execute, he] at h
    | cons v rest =>
      simp only [execute, he, Option.some.injEq] at h
      subst t
      refine ⟨hc.1, ?_⟩
      intro i
      have hi := hc.2 i
      by_cases hip : i = p
      · subst i
        simp [receivedAfter, he] at hi ⊢
        omega
      · have hn : next i ≠ next p := fun h => hip (next_injective h)
        simpa [receivedAfter, Function.update_of_ne hip, Function.update_of_ne hn] using hi
  | send p | receive p | compare p =>
    simp only [execute, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    have hl := local_count_step (owner p) p _ (s.process p) (s.inbox p) r
      (s.sent p) (rc p) rfl (hc.1 p) hr
    all_goals
      simpa [receivedAfter] using commit_counted s rc p r _ hc hl.1 hl.2

omit [LinearOrder Id] in
private theorem commit_first (v : Id) (s : State n Id) (rc : Fin n → Nat)
    (p : Fin n) (r : Local Id × List Id × Option Id) (d : Nat)
    (hc : Counted s rc) (hq : r.2.1.length + d = (s.inbox p).length)
    (ht : FirstLocal v (rc p) (s.process p) ∨ EvenData v (rc p) (s.inbox p) →
      FirstLocal v (rc p + d) r.1 ∨ EvenData v (rc p + d) r.2.1 ∨
      (r.2.2 = some v ∧ s.sent p % 2 = 0) ∨ r.1.pc = .elected)
    (hf : FirstLive v s rc) :
    FirstLive v (commitLocal s p r) (Function.update rc p (rc p + d)) ∨
      Announced (commitLocal s p r) := by
  let rc' := Function.update rc p (rc p + d)
  have hbase (i : Fin n) :
      rc' (next i) + ((commitLocal s p r).inbox (next i)).length =
        rc (next i) + (s.inbox (next i)).length := by
    rcases r with ⟨l, q, out⟩
    cases out <;> by_cases hi : next i = p <;> simp_all [rc', commitLocal]
    all_goals omega
  have htransfer (h : FirstLocal v (rc p) (s.process p) ∨ EvenData v (rc p) (s.inbox p)) :
      FirstLive v (commitLocal s p r) rc' ∨ Announced (commitLocal s p r) := by
    rcases ht h with hl | hq' | ⟨ho, heven⟩ | he
    · left; left; refine ⟨p, ?_⟩
      rcases r with ⟨l, q, out⟩
      cases out <;> simpa [rc', commitLocal] using hl
    · left; right; left; refine ⟨p, ?_⟩
      rcases r with ⟨l, q, out⟩
      cases out <;> simpa [rc', commitLocal] using hq'
    · left; right; right; refine ⟨p, ?_⟩
      rw [hbase]
      rcases r with ⟨l, q, out⟩
      simp only at ho
      subst out
      simp only [commitLocal, Function.update_self]
      rw [evenData_append]
      right
      simpa [EvenData, ← hc.2 p] using heven
    · right; refine ⟨p, ?_⟩
      rcases r with ⟨l, q, out⟩
      cases out <;> simpa [commitLocal] using he
  rcases hf with ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩
  · by_cases hip : i = p
    · subst i; exact htransfer (Or.inl hi)
    · left; left; refine ⟨i, ?_⟩
      rcases r with ⟨l, q, out⟩
      cases out <;> simpa [rc', commitLocal, Function.update_of_ne hip] using hi
  · by_cases hip : i = p
    · subst i; exact htransfer (Or.inr hi)
    · left; right; left; refine ⟨i, ?_⟩
      rcases r with ⟨l, q, out⟩
      cases out <;> simpa [rc', commitLocal, Function.update_of_ne hip] using hi
  · left; right; right; refine ⟨i, ?_⟩
    change EvenData v (rc' (next i) + _) _
    rw [hbase]
    rcases r with ⟨l, q, out⟩
    cases out <;> by_cases hip : i = p <;> simp_all [commitLocal, evenData_append]

private theorem step_first (v : Id) (owner : Fin n → Id) {s t : State n Id}
    {a : Action n} {rc : Fin n → Nat} (hc : Counted s rc)
    (ho : DataOrigin (· ≤ v) s) (hf : FirstLive v s rc)
    (h : (lts owner).Tr s a t) : FirstLive v t (receivedAfter rc a) ∨ Announced t := by
  change execute owner s a = some t at h
  cases a with
  | idle =>
    simp only [execute, Option.some.injEq] at h
    exact Or.inl (h ▸ hf)
  | deliver p =>
    cases he : s.edge p with
    | nil => simp [execute, he] at h
    | cons x rest =>
      simp only [execute, he, Option.some.injEq] at h
      subst t
      left
      rcases hf with ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩
      · exact Or.inl ⟨i, hi⟩
      · right; left; refine ⟨i, ?_⟩
        by_cases hip : i = next p <;> simp_all [receivedAfter, evenData_append]
      · by_cases hip : i = p
        · subst i
          have hh : EvenData v (rc (next p)) (s.inbox (next p) ++ (x :: rest)) :=
            (evenData_append _ _ _ _).mpr (Or.inr (by simpa [he] using hi))
          have heq : s.inbox (next p) ++ (x :: rest) =
              (s.inbox (next p) ++ [x]) ++ rest := by simp
          rw [heq, evenData_append] at hh
          rcases hh with hin | hedge
          · exact Or.inr (Or.inl ⟨next p, by simpa [receivedAfter] using hin⟩)
          · exact Or.inr (Or.inr ⟨p, by simpa [receivedAfter] using hedge⟩)
        · have hn : next i ≠ next p := fun h => hip (next_injective h)
          exact Or.inr (Or.inr ⟨i, by simpa [receivedAfter, Function.update_of_ne hip, Function.update_of_ne hn] using hi⟩)
  | send p | receive p | compare p =>
    simp only [execute, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    have hl := local_count_step (owner p) p _ (s.process p) (s.inbox p) r
      (s.sent p) (rc p) rfl (hc.1 p) hr
    have ht := local_first_step v (owner p) _ (s.process p) (s.inbox p) r
      (s.sent p) (rc p) (hc.1 p) (ho.1 p) hr
    all_goals simpa [receivedAfter] using commit_first v s rc p r _ hc hl.2 ht hf

private theorem step_announced (owner : Fin n → Id) {s t : State n Id}
    {a : Action n} (hs : Announced s) (h : (lts owner).Tr s a t) : Announced t := by
  change execute owner s a = some t at h
  obtain ⟨i, hi⟩ := hs
  cases a with
  | idle =>
    simp only [execute, Option.some.injEq] at h
    exact h ▸ (show Announced s from ⟨i, hi⟩)
  | deliver p =>
    cases he : s.edge p with
    | nil => simp [execute, he] at h
    | cons x rest =>
      simp only [execute, he, Option.some.injEq] at h
      subst t
      exact ⟨i, hi⟩
  | send p | receive p | compare p =>
    simp only [execute, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    by_cases hip : i = p
    · subst i
      simp [localStep, hi] at hr
    · refine ⟨i, ?_⟩
      rcases r with ⟨l, q, out⟩
      cases out <;> simpa [commitLocal, Function.update_of_ne hip] using hi

omit [LinearOrder Id] in
private theorem firstLive_live (v : Id) (s : State n Id) (rc : Fin n → Nat)
    (hf : FirstLive v s rc) : LiveData v s := by
  rcases hf with ⟨p, hp⟩ | ⟨p, hp⟩ | ⟨p, hp⟩
  · left; refine ⟨p, ?_⟩
    cases he : (s.process p).pc <;> simp_all [FirstLocal, LiveLocal]
  · exact Or.inr (Or.inr ⟨p, evenData_mem _ _ _ hp⟩)
  · exact Or.inr (Or.inl ⟨p, evenData_mem _ _ _ hp⟩)

/-- Every reachable pre-announcement state retains any maximum initial ID in
live protocol data. Injectivity is unnecessary for this preservation result. -/
theorem maximum_live (owner : Fin n → Id) (pmax : Fin n) (hm : IsMaximum owner pmax)
    {s : State n Id} (hr : Reachable owner s) (hn : ¬ Announced s) :
    LiveData (owner pmax) s := by
  let Inv := fun s : State n Id => DataOrigin (· ≤ owner pmax) s ∧
    (Announced s ∨ ∃ rc, Counted s rc ∧ FirstLive (owner pmax) s rc)
  have hi : Inv (initial owner) := by
    refine ⟨?_, Or.inr ⟨fun _ => 0, initial_counted owner, ?_⟩⟩
    · simpa [DataOrigin, LocalOrigin, initial, IsMaximum] using hm
    · exact Or.inl ⟨pmax, rfl⟩
  have hstep : ∀ s a t, (lts owner).Tr s a t → Inv s → Inv t := by
    intro s a t ht hs
    refine ⟨step_origin _ owner hs.1 ht, ?_⟩
    rcases hs.2 with ha | ⟨rc, hc, hf⟩
    · exact Or.inl (step_announced owner ha ht)
    · rcases step_first _ owner hc hs.1 hf ht with hf' | ha
      · exact Or.inr ⟨receivedAfter rc a, step_counted owner hc ht, hf'⟩
      · exact Or.inl ha
  obtain ⟨as, hr⟩ := hr
  have hs := Cslib.LTS.mtrInv_of_trInv hstep _ _ _ hr hi
  rcases hs.2 with ha | ⟨rc, _, hf⟩
  · exact (hn ha).elim
  · exact firstLive_live _ _ rc hf

/-- Every positive ring has a maximum initial identifier still in live data
before announcement. This includes all injective initial assignments. -/
theorem live_maximum_exists (owner : Fin n → Id) (hn : 0 < n)
    {s : State n Id} (hr : Reachable owner s) (ha : ¬ Announced s) :
    ∃ p, IsMaximum owner p ∧ LiveData (owner p) s := by
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ owner
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
  have hm : IsMaximum owner p := fun q => hp q (Finset.mem_univ q)
  exact ⟨p, hm, maximum_live owner p hm hr ha⟩

end CircularElection
