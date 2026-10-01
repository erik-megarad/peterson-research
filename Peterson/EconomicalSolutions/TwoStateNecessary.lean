import Cslib.Foundations.Semantics.LTS.Basic

/-! A necessary condition for failure-tolerant two-process register programs.
This is not the two-state impossibility theorem. See the E6 economy target.
Programs may differ and private memory has no finiteness bound. -/
namespace EconomicalSolutions.TwoState

inductive Phase where
  | down | idle | trying | cs | release
  deriving DecidableEq

/-- Each constructor is one instruction. Reads cache a value privately; only
`write` and the final release-to-dead `retire` publish. `halt` is an endlessly
repeatable private idle instruction,
so stopping while a request is pending cannot make progress vacuous. -/
inductive Instruction (V : Type u) (M : Type v) where
  | readPeer (resume : V → M)
  | readOwn (resume : V → M)
  | write (value : V) (resume : M)
  | compute (resume : M)
  | enter (resume : M)
  | retire (resume : M)
  | halt

structure Local (V : Type u) (M : Type v) where
  phase : Phase
  memory : M
  value : V

abbrev State (V : Type u) (M : Type v) := Bool → Local V M

structure Program (V : Type u) (M : Type v) where
  dead : V
  start : Bool → M
  code : Bool → Phase → M → Instruction V M

inductive Command where
  | run (p : Bool) | request (p : Bool) | complete (p : Bool)
  | fail (p : Bool) | restart (p : Bool) | stutter
  deriving DecidableEq

variable {V : Type u} {M : Type v} (P : Program V M)

namespace Program

def protocol (phase : Phase) : Prop := phase = .trying ∨ phase = .release
instance (phase : Phase) : Decidable (protocol phase) := inferInstanceAs (Decidable (_ ∨ _))

def execute (p : Bool) (l : Local V M) (peer : V) : Local V M :=
  if protocol l.phase ∨ l.phase = .cs then
    match P.code p l.phase l.memory with
    | .readPeer f => { l with memory := f peer }
    | .readOwn f => { l with memory := f l.value }
    | .write v m => { l with value := v, memory := m }
    | .compute m => { l with memory := m }
    | .enter m => if l.phase = .trying then { l with phase := .cs, memory := m } else l
    | .retire m => if l.phase = .release then ⟨.idle, m, P.dead⟩ else l
    | .halt => l
  else l

/-- Invalid client commands stutter. Requests and critical completion are
separately delayable; restart resets private state, normal requests retain it. -/
def next (s : State V M) : Command → State V M
  | .run p => Function.update s p (P.execute p (s p) (s (!p)).value)
  | .request p => Function.update s p
      (if (s p).phase = .idle then { s p with phase := .trying } else s p)
  | .complete p => Function.update s p
      (if (s p).phase = .cs then { s p with phase := .release } else s p)
  | .fail p => Function.update s p ⟨.down, P.start p, P.dead⟩
  | .restart p => Function.update s p
      (if (s p).phase = .down then ⟨.idle, P.start p, P.dead⟩ else s p)
  | .stutter => s

def initial : State V M := fun p => ⟨.idle, P.start p, P.dead⟩
def lts : Cslib.LTS (State V M) Command := ⟨fun s c t => P.next s c = t⟩
inductive Reachable (P : Program V M) : State V M → Prop where
  | initial : Reachable P P.initial
  | step {s : State V M} (c : Command) : Reachable P s → Reachable P (P.next s c)

def Safe : Prop := ∀ s, P.Reachable s → ∀ p, (s p).phase = .cs → (s (!p)).phase ≠ .cs

def Entered (s : State V M) (c : Command) (p : Bool) : Prop :=
  c = .run p ∧ (s p).phase = .trying ∧ (P.next s c p).phase = .cs

def Acts (c : Command) (p : Bool) : Prop := c = .run p ∨ c = .fail p

def Completed (_P : Program V M) (s : State V M) (c : Command) (p : Bool) : Prop :=
  (c = .complete p ∧ (s p).phase = .cs) ∨ c = .fail p

/-- A continuation need not start initially. Correctness below is required only
of initialized runs; the reachable-continuation bridge is proved. -/
structure Run where
  state : Nat → State V M
  command : Nat → Command
  valid : ∀ n, P.next (state n) (command n) = state (n + 1)

def ProtocolScheduling (r : P.Run) : Prop :=
  ∀ n p, protocol (r.state n p).phase → ∃ m, n ≤ m ∧ Acts (r.command m) p

def CriticalCompletion (r : P.Run) : Prop :=
  ∀ n p, (r.state n p).phase = .cs →
    ∃ m, n ≤ m ∧ P.Completed (r.state m) (r.command m) p

def Admissible (r : P.Run) : Prop := P.ProtocolScheduling r ∧ P.CriticalCompletion r

/-- Entry or failure of the request that is pending at n. The transition
semantics prevent cancellation or a new request before either outcome. -/
def RequestProgress (r : P.Run) : Prop :=
  ∀ n p, (r.state n p).phase = .trying →
    ∃ m, n ≤ m ∧ (P.Entered (r.state m) (r.command m) p ∨ r.command m = .fail p)

def Progress : Prop :=
  ∀ r : P.Run, r.state 0 = P.initial → P.Admissible r → P.RequestProgress r

@[simp] theorem run_other (s : State V M) (p : Bool) :
    P.next s (.run p) (!p) = s (!p) := by cases p <;> simp [next]
@[simp] theorem run_self (s : State V M) (p : Bool) :
    P.next s (.run p) p = P.execute p (s p) (s (!p)).value := by simp [next]

/-- Protocol instructions cannot abandon a pending request except by entry. -/
theorem execute_pending (p : Bool) (l : Local V M) (v : V) (h : l.phase = .trying) :
    (P.execute p l v).phase = .trying ∨ (P.execute p l v).phase = .cs := by
  simp only [execute, h, protocol, true_or, ↓reduceIte]
  cases P.code p Phase.trying l.memory <;> simp [h]

/-- Client actions cannot cancel an outstanding request. The only exits are
its entry or its own failure, even if private computation halts or loops. -/
theorem pending_persists (s : State V M) (c : Command) (p : Bool)
    (h : (s p).phase = .trying) (he : ¬ P.Entered s c p) (hf : c ≠ .fail p) :
    (P.next s c p).phase = .trying := by
  cases c with
  | run q =>
    by_cases e : q = p
    · subst q
      have hh := P.execute_pending p (s p) (s (!p)).value h
      rw [run_self]
      exact hh.resolve_right (fun hc => he ⟨rfl, h, by simpa only [run_self] using hc⟩)
    · simp [next, Function.update_of_ne (Ne.symm e), h]
  | fail q =>
    have e : q ≠ p := by intro eq; subst q; exact hf rfl
    simp [next, Function.update_of_ne (Ne.symm e), h]
  | request q =>
    by_cases e : q = p
    · subst q; simp [next, h]
    · simp [next, Function.update_of_ne (Ne.symm e), h]
  | complete q =>
    by_cases e : q = p
    · subst q; simp [next, h]
    · simp [next, Function.update_of_ne (Ne.symm e), h]
  | restart q =>
    by_cases e : q = p
    · subst q; simp [next, h]
    · simp [next, Function.update_of_ne (Ne.symm e), h]
  | stutter => exact h

/-- Progress supplies a first outcome with the same request pending at every
prior time. This rules out interpreting RequestProgress as a later request. -/
theorem progress_first_outcome (r : P.Run) (hp : P.RequestProgress r)
    (n : Nat) (p : Bool) (hn : (r.state n p).phase = .trying) :
    ∃ m, n ≤ m ∧ (P.Entered (r.state m) (r.command m) p ∨ r.command m = .fail p) ∧
      ∀ k, n ≤ k → k < m → (r.state k p).phase = .trying ∧
        ¬ P.Entered (r.state k) (r.command k) p ∧ r.command k ≠ .fail p := by
  classical
  have hex := hp n p hn
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  have before : ∀ k, n ≤ k → k < m →
      ¬ P.Entered (r.state k) (r.command k) p ∧ r.command k ≠ .fail p := by
    intro k hnk hkm
    have hh := Nat.find_min hex hkm
    exact ⟨fun he => hh ⟨hnk, Or.inl he⟩, fun hf => hh ⟨hnk, Or.inr hf⟩⟩
  refine ⟨m, hm.1, hm.2, ?_⟩
  intro k hnk hkm
  refine ⟨?_, before k hnk hkm⟩
  induction k, hnk using Nat.le_induction with
  | base => exact hn
  | succ k hnk ih =>
    have hb := before k hnk (by omega)
    rw [← r.valid k]
    exact P.pending_persists _ _ p (ih (by omega)) hb.1 hb.2

theorem protocol_persists (s : State V M) (c : Command) (p : Bool)
    (h : protocol (s p).phase) (ha : ¬ Acts c p) : protocol (P.next s c p).phase := by
  cases c with
  | run q => have : q ≠ p := by intro e; subst q; exact ha (Or.inl rfl)
             simp [next, Function.update_of_ne (Ne.symm this), h]
  | fail q => have : q ≠ p := by intro e; subst q; exact ha (Or.inr rfl)
              simp [next, Function.update_of_ne (Ne.symm this), h]
  | request q => by_cases e : q = p
                 · subst q; rcases h with h | h <;> simp [next, h, protocol]
                 · simp [next, Function.update_of_ne (Ne.symm e), h]
  | complete q => by_cases e : q = p
                  · subst q; rcases h with h | h <;> simp [next, h, protocol]
                  · simp [next, Function.update_of_ne (Ne.symm e), h]
  | restart q => by_cases e : q = p
                 · subst q; rcases h with h | h <;> simp [next, h, protocol]
                 · simp [next, Function.update_of_ne (Ne.symm e), h]
  | stutter => exact h

theorem critical_persists (s : State V M) (c : Command) (p : Bool)
    (h : (s p).phase = .cs) (ha : ¬ P.Completed s c p) :
    (P.next s c p).phase = .cs := by
  cases c with
  | run q => by_cases e : q = p
             · subst q; rw [run_self]
               simp only [execute, h, protocol, or_true, ↓reduceIte]
               cases P.code p Phase.cs (s p).memory <;> simp [h]
             · simp [next, Function.update_of_ne (Ne.symm e), h]
  | fail q => have : q ≠ p := by intro e; subst q; exact ha (Or.inr rfl)
              simp [next, Function.update_of_ne (Ne.symm this), h]
  | complete q => have : q ≠ p := by intro e; subst q; exact ha (Or.inl ⟨rfl, h⟩)
                  simp [next, Function.update_of_ne (Ne.symm this), h]
  | request q => by_cases e : q = p
                 · subst q; simp [next, h]
                 · simp [next, Function.update_of_ne (Ne.symm e), h]
  | restart q => by_cases e : q = p
                 · subst q; simp [next, h]
                 · simp [next, Function.update_of_ne (Ne.symm e), h]
  | stutter => exact h

/-- Prefixing any actual step preserves both frozen-style admissibility clauses. -/
def Run.prepend (r : P.Run) (s : State V M) (c : Command)
    (h : P.next s c = r.state 0) : P.Run where
  state | 0 => s | n + 1 => r.state n
  command | 0 => c | n + 1 => r.command n
  valid | 0 => h | n + 1 => r.valid n

theorem admissible_prepend (r : P.Run) (s : State V M) (c : Command)
    (h : P.next s c = r.state 0) (hr : P.Admissible r) :
    P.Admissible (Run.prepend P r s c h) := by
  constructor
  · intro n p hp
    cases n with
    | zero =>
      by_cases ha : Acts c p
      · exact ⟨0, Nat.le_refl _, ha⟩
      · have hh := P.protocol_persists s c p hp ha
        rw [h] at hh
        obtain ⟨m, _, hm⟩ := hr.1 0 p hh
        exact ⟨m + 1, Nat.zero_le _, hm⟩
    | succ n =>
      obtain ⟨m, hn, hm⟩ := hr.1 n p hp
      exact ⟨m + 1, Nat.succ_le_succ hn, hm⟩
  · intro n p hp
    cases n with
    | zero =>
      by_cases ha : P.Completed s c p
      · exact ⟨0, Nat.le_refl _, ha⟩
      · have hh := P.critical_persists s c p hp ha
        rw [h] at hh
        obtain ⟨m, _, hm⟩ := hr.2 0 p hh
        exact ⟨m + 1, Nat.zero_le _, hm⟩
    | succ n =>
      obtain ⟨m, hn, hm⟩ := hr.2 n p hp
      exact ⟨m + 1, Nat.succ_le_succ hn, hm⟩

/-- Initialized progress suffices at every reachable suffix. No solo-service
premise or existence-of-admissible-continuations axiom is used. -/
theorem progress_reachable (hp : P.Progress) {s : State V M} (hs : P.Reachable s) :
    ∀ r : P.Run, r.state 0 = s → P.Admissible r → P.RequestProgress r := by
  induction hs with
  | initial => exact hp
  | @step s c hs ih =>
    intro r h hr n p hn
    let r' := Run.prepend P r s c h.symm
    have hh := ih r' rfl (P.admissible_prepend r s c h.symm hr)
    obtain ⟨m, hm, ho⟩ := hh (n + 1) p hn
    cases m with
    | zero => omega
    | succ m => exact ⟨m, Nat.le_of_succ_le_succ hm, ho⟩

/-- The concrete infinite sequence that schedules only p. It is defined for
all programs, including ones which never enter or which halt. -/
def solo (P : Program V M) (s : State V M) (p : Bool) : Nat → State V M
  | 0 => s
  | n + 1 => P.next (P.solo s p n) (.run p)

def soloRun (s : State V M) (p : Bool) : P.Run where
  state := P.solo s p
  command := fun _ => .run p
  valid _ := rfl

@[simp] theorem solo_other (s : State V M) (p : Bool) (n : Nat) :
    P.solo s p n (!p) = s (!p) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [solo, run_other] using ih

theorem solo_reachable {s : State V M} (hs : P.Reachable s) (p : Bool) (n : Nat) :
    P.Reachable (P.solo s p n) := by
  induction n with
  | zero => exact hs
  | succ n ih => exact .step (.run p) ih

/-- Under the assumption that no finite solo prefix reaches critical, the
original request stays pending forever. -/
theorem solo_pending (s : State V M) (p : Bool) (h : (s p).phase = .trying)
    (hn : ∀ n, (P.solo s p n p).phase ≠ .cs) :
    ∀ n, (P.solo s p n p).phase = .trying := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
    have hh := P.execute_pending p (P.solo s p n p) (P.solo s p n (!p)).value ih
    change (P.next (P.solo s p n) (.run p) p).phase = .trying
    rw [run_self]
    exact hh.resolve_right (by simpa only [solo, run_self] using hn (n + 1))

/-- Actual per-request progress forces a finite solo entry after peer failure.
Admissibility is constructed in the hypothetical never-entry case. -/
theorem solo_entry (hp : P.Progress) {s : State V M} (hs : P.Reachable s)
    (p : Bool) (h : (s p).phase = .trying) (hd : (s (!p)).phase = .down) :
    ∃ n, (P.solo s p n p).phase = .cs := by
  by_contra hn
  have hn' : ∀ n, (P.solo s p n p).phase ≠ .cs := by simpa using hn
  have adm : P.Admissible (P.soloRun s p) := by
    constructor
    · intro n q hq
      by_cases e : q = p
      · subst q; exact ⟨n, Nat.le_refl _, Or.inl rfl⟩
      · have eq : q = !p := by cases p <;> cases q <;> simp_all
        subst q
        have : protocol (s (!p)).phase := by simpa only [soloRun, solo_other] using hq
        simp [hd, protocol] at this
    · intro n q hq
      by_cases e : q = p
      · subst q; exact False.elim (hn' n hq)
      · have eq : q = !p := by cases p <;> cases q <;> simp_all
        subst q
        have : (s (!p)).phase = .cs := by simpa only [soloRun, solo_other] using hq
        simp [hd] at this
  obtain ⟨m, _, hm⟩ := P.progress_reachable hp hs (P.soloRun s p) rfl adm 0 p h
  rcases hm with hm | hm
  · exact hn' (m + 1) hm.2.2
  · cases hm

/-- The forced entry has a first finite occurrence. Before it, every state
still carries the original request; every scheduled command is its own run. -/
theorem solo_first_entry (hp : P.Progress) {s : State V M} (hs : P.Reachable s)
    (p : Bool) (h : (s p).phase = .trying) (hd : (s (!p)).phase = .down) :
    ∃ n, 0 < n ∧ (P.solo s p n p).phase = .cs ∧
      ∀ k, k < n → (P.solo s p k p).phase = .trying := by
  classical
  have he := P.solo_entry hp hs p h hd
  let n := Nat.find he
  have hn : (P.solo s p n p).phase = .cs := Nat.find_spec he
  have noearlier : ∀ k, k < n → (P.solo s p k p).phase ≠ .cs :=
    fun k hk => Nat.find_min he hk
  have pos : 0 < n := by
    by_contra hh
    have hz : n = 0 := by omega
    simp [hz, solo, h] at hn
  refine ⟨n, pos, hn, ?_⟩
  intro k hk
  induction k with
  | zero => exact h
  | succ k ih =>
    have hh := P.execute_pending p (P.solo s p k p) (P.solo s p k (!p)).value
      (ih (by omega))
    simpa only [solo, run_self] using
      hh.resolve_right (by simpa only [solo, run_self] using noearlier (k + 1) hk)

/-- The finite prefix is a path in CSLib's actual labelled transition system. -/
theorem solo_path (s : State V M) (p : Bool) (n : Nat) :
    P.lts.MTr s (List.replicate n (.run p)) (P.solo s p n) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    have hh := Cslib.LTS.MTr.stepR P.lts ih (μ := .run p) (s3 := P.solo s p (n + 1)) rfl
    simpa [List.replicate_succ'] using hh

/-- The finite replay keeps the observer's complete record and the peer's
visible value, without equating their private states or failure status. -/
theorem solo_transfer (s t : State V M) (p : Bool)
    (hl : s p = t p) (hv : (s (!p)).value = (t (!p)).value) :
    ∀ n, P.solo s p n p = P.solo t p n p := by
  intro n
  induction n with
  | zero => exact hl
  | succ n ih => simp only [solo, run_self, solo_other, ih, hv]

/-- A critical owner must publish a nondead value when its peer has a pending
original request, in any safe solution with initialized per-request progress. -/
theorem critical_nondead (safe : P.Safe) (progress : P.Progress)
    {s : State V M} (reachable : P.Reachable s) (i : Bool)
    (critical : (s i).phase = .cs) (pending : (s (!i)).phase = .trying) :
    (s i).value ≠ P.dead := by
  intro dead
  let t := P.next s (.fail i)
  have rt : P.Reachable t := .step (.fail i) reachable
  have same : t (!i) = s (!i) := by cases i <;> simp [t, next]
  have down : (t (!(!i))).phase = .down := by simp [t, next]
  have pend : (t (!i)).phase = .trying := by rw [same]; exact pending
  obtain ⟨n, _, hn, _⟩ := P.solo_first_entry progress rt (!i) pend down
  have visible : (s (!(!i))).value = (t (!(!i))).value := by simp [t, next, dead]
  have replay := P.solo_transfer s t (!i) same.symm visible n
  have collision : (P.solo s (!i) n (!i)).phase = .cs := by rw [replay]; exact hn
  have occupant : (P.solo s (!i) n i).phase = .cs := by
    have hh := P.solo_other s (!i) n
    have hh' : P.solo s (!i) n i = s i := by simpa using hh
    rw [hh']; exact critical
  exact safe _ (P.solo_reachable reachable (!i) n) i occupant collision

/-- The only binary-specific step: eliminate dead from the two-value alphabet. -/
theorem critical_binary (safe : P.Safe) (progress : P.Progress) (g : V)
    (binary : ∀ v : V, v = P.dead ∨ v = g)
    {s : State V M} (reachable : P.Reachable s) (i : Bool)
    (critical : (s i).phase = .cs) (pending : (s (!i)).phase = .trying) :
    (s i).value = g :=
  (binary (s i).value).resolve_left (P.critical_nondead safe progress reachable i critical pending)

end Program
end EconomicalSolutions.TwoState

#print axioms EconomicalSolutions.TwoState.Program.pending_persists
#print axioms EconomicalSolutions.TwoState.Program.progress_first_outcome
#print axioms EconomicalSolutions.TwoState.Program.admissible_prepend
#print axioms EconomicalSolutions.TwoState.Program.progress_reachable
#print axioms EconomicalSolutions.TwoState.Program.solo_pending
#print axioms EconomicalSolutions.TwoState.Program.solo_entry
#print axioms EconomicalSolutions.TwoState.Program.solo_first_entry
#print axioms EconomicalSolutions.TwoState.Program.solo_path
#print axioms EconomicalSolutions.TwoState.Program.solo_transfer
#print axioms EconomicalSolutions.TwoState.Program.critical_nondead
#print axioms EconomicalSolutions.TwoState.Program.critical_binary
