import MultiReaderAtomic.Execution
import MultiReaderAtomic.Restricted

/-! Finite own work of the unchanged Figure 1 program. Proof-side fuel counts
primitive invocations and local transitions separately; it is not physical time. -/
namespace MultiReaderAtomic

inductive ProgramBound {n : Nat} {α : Type} : Program n α → Nat → Nat → Prop where
  | done (result) : ProgramBound (.done result) 0 1
  | read (r : Register n) (next : Sample (Value α r) → Program n α) {a f} (tail : ∀ x, ProgramBound (next x) a f) :
      ProgramBound (.read r next) (a+1) (f+2)
  | write (r : Register n) (value : Value α r) (next : Program n α) {a f} (tail : ProgramBound next a f) :
      ProgramBound (.write r value next) (a+1) (f+2)
  | order (next : Bool → Program n α) {a f} (tail : ∀ b, ProgramBound (next b) a f) :
      ProgramBound (.order next) a (f+1)
  | token (x y : Token) (next : Token → Program n α) {a f} (tail : ∀ t, ProgramBound (next t) a f) :
      ProgramBound (.token x y next) a (f+1)
  | weaken {prog a f a' f'} (bound : ProgramBound prog a f)
      (accesses : a ≤ a') (fuel : f ≤ f') : ProgramBound prog a' f'

inductive PhaseBound {n : Nat} {α : Type} : Phase n α → Nat → Nat → Prop where
  | ready {prog a f} (bound : ProgramBound prog a f) : PhaseBound (.ready prog) a f
  | reading (r : Register n) (start : Nat) (next : Sample (Value α r) → Program n α) {a f} (tail : ∀ x, ProgramBound (next x) a f) :
      PhaseBound (.reading r start next) a (f+1)
  | writing (r : Register n) (start : Nat) (next : Program n α) {a f} (tail : ProgramBound next a f) :
      PhaseBound (.writing r start next) a (f+1)
  | weaken {phase a f a' f'} (bound : PhaseBound phase a f)
      (accesses : a ≤ a') (fuel : f ≤ f') : PhaseBound phase a' f'

theorem pair_bound (a b : Register n) (next : Sample (Value α a) → Sample (Value α b) → Program n α) {accesses fuel}
    (tail : ∀ x y, ProgramBound (next x y) accesses fuel) :
    ProgramBound (pair a b next) (accesses+2) (fuel+5) := by
  apply ProgramBound.order
  intro choice
  cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact .read b _ (fun y => .read a _ (fun x => tail x y))
  · exact .read a _ (fun x => .read b _ (fun y => tail x y))

theorem writerTail_bound (v : α) : ProgramBound (writerTail (n := n) v) 5 11 :=
  .write _ _ _ (.write _ _ _ (.write _ _ _ (.write _ _ _ (.write _ _ _ (.done _)))))

theorem writerLoop_bound (v : α) (readers : List (Fin n)) :
    ProgramBound (writerLoop v readers) (3*readers.length+5) (8*readers.length+11) := by
  induction readers with
  | nil => exact writerTail_bound v
  | cons j rest ih =>
    have h : ProgramBound (writerLoop v (j::rest)) (3*rest.length+5+1+2)
        (8*rest.length+11+2+1+5) :=
      pair_bound _ _ _ (fun _ _ => .token _ _ _ (fun _ => .write _ _ _ ih))
    simpa [List.length_cons, Nat.mul_add, Nat.add_assoc] using h

theorem readerFinish_bound (j : Fin n) (saved : Sample α) (forwarded : Bool)
    (level rc wc : Token) :
    ProgramBound (readerFinish j saved forwarded level rc wc) 2 5 := by
  unfold readerFinish
  split
  · exact .weaken (.read _ _ (fun _ => .done _)) (by omega) (by omega)
  · split
    · exact .read _ _ (fun _ => .write _ _ _ (.done _))
    · exact .weaken (.done _) (by omega) (by omega)

theorem readerScan_bound (j : Fin n) (saved : Sample α) (forwarded : Bool)
    (readers : List (Fin n)) :
    ProgramBound (readerScan j saved forwarded readers)
      (2*readers.length+5) (5*readers.length+12) := by
  induction readers generalizing forwarded with
  | nil => exact .read _ _ (fun _ => pair_bound _ _ _ (fun _ _ => readerFinish_bound _ _ _ _ _ _))
  | cons i rest ih =>
    have h := pair_bound (.fc i) (.wc i) _ (fun x y => ih (forwarded || decide (x.value = y.value)))
    simpa [readerScan, List.length_cons, Nat.mul_add, Nat.add_assoc] using h

theorem writerProgram_bound (v : α) :
    ProgramBound (writerProgram (n := n) v) (primitiveBudget n .writer) (8*n+11) := by
  simpa [writerProgram, primitiveBudget] using writerLoop_bound (n := n) v (List.finRange n)

theorem readerProgram_bound (j : Fin n) :
    ProgramBound (readerProgram (α := α) j) (primitiveBudget n (.reader j)) (5*n+18) := by
  have h : ProgramBound (readerProgram (α := α) j) (2*n+5+1+1+1) (5*n+12+2+2+2) :=
    .read _ _ (fun _ => .write _ _ _ (.read _ _ (fun saved => by
      simpa using readerScan_bound j saved false (List.finRange n))))
  simpa [primitiveBudget, Nat.add_assoc] using h

def ProgramResidual (prog : Program n α) (a f : Nat) : Prop :=
  match prog with
  | .done _ => 1 ≤ f
  | .read _ next => ∃ a' f', a'+1 ≤ a ∧ f'+2 ≤ f ∧ ∀ x, ProgramBound (next x) a' f'
  | .write _ _ next => ∃ a' f', a'+1 ≤ a ∧ f'+2 ≤ f ∧ ProgramBound next a' f'
  | .order next => ∃ a' f', a' ≤ a ∧ f'+1 ≤ f ∧ ∀ x, ProgramBound (next x) a' f'
  | .token _ _ next => ∃ a' f', a' ≤ a ∧ f'+1 ≤ f ∧ ∀ x, ProgramBound (next x) a' f'

theorem programBound_residual {prog : Program n α} {a f}
    (h : ProgramBound prog a f) : ProgramResidual prog a f := by
  induction h with
  | done => exact Nat.le_refl _
  | read r next tail => exact ⟨_, _, Nat.le_refl _, Nat.le_refl _, tail⟩
  | write r value next tail => exact ⟨_, _, Nat.le_refl _, Nat.le_refl _, tail⟩
  | order next tail => exact ⟨_, _, Nat.le_refl _, Nat.le_refl _, tail⟩
  | token x y next tail => exact ⟨_, _, Nat.le_refl _, Nat.le_refl _, tail⟩
  | @weaken prog a f a' f' bound ha hf ih =>
    cases prog <;> simp only [ProgramResidual] at ih ⊢
    · omega
    all_goals obtain ⟨a', f', h₁, h₂, ht⟩ := ih
    all_goals exact ⟨a', f', by omega, by omega, ht⟩

def PhaseResidual (phase : Phase n α) (a f : Nat) : Prop :=
  match phase with
  | .ready prog => ProgramBound prog a f
  | .reading _ _ next => ∃ a' f', a' ≤ a ∧ f'+1 ≤ f ∧ ∀ x, ProgramBound (next x) a' f'
  | .writing _ _ next => ∃ a' f', a' ≤ a ∧ f'+1 ≤ f ∧ ProgramBound next a' f'

theorem phaseBound_residual {phase : Phase n α} {a f}
    (h : PhaseBound phase a f) : PhaseResidual phase a f := by
  induction h with
  | ready bound => exact bound
  | reading r start next tail => exact ⟨_, _, Nat.le_refl _, Nat.le_refl _, tail⟩
  | writing r start next tail => exact ⟨_, _, Nat.le_refl _, Nat.le_refl _, tail⟩
  | @weaken phase a f a' f' bound ha hf ih =>
    cases phase <;> simp only [PhaseResidual] at ih ⊢
    · exact .weaken ih ha hf
    all_goals obtain ⟨a', f', h₁, h₂, ht⟩ := ih
    all_goals exact ⟨a', f', by omega, by omega, ht⟩

/-- Every consumed instruction lowers local fuel. A begin access also spends
one primitive invocation. An unrelated global step can retain the same fuel. -/
theorem instruction_bound {v₀ : α} {s : State n α} {phase phase' : Phase n α} {a f}
    (instruction : Instruction v₀ s phase phase') (bound : PhaseBound phase a f) :
    ∃ a' f', PhaseBound phase' a' f' ∧ a' ≤ a ∧ f' ≤ f ∧
      (phase ≠ phase' → f' < f) := by
  have h := phaseBound_residual bound
  cases instruction with
  | unchanged => exact ⟨a, f, bound, Nat.le_refl _, Nat.le_refl _, by simp⟩
  | order next b =>
    obtain ⟨a', f', ha, hf, ht⟩ := programBound_residual h
    exact ⟨a', f', .ready (ht b), ha, by omega, fun _ => by omega⟩
  | token x y choice next ha hb =>
    obtain ⟨a', f', h₁, h₂, ht⟩ := programBound_residual h
    exact ⟨a', f', .ready (ht choice), h₁, by omega, fun _ => by omega⟩
  | beginRead r next =>
    obtain ⟨a', f', ha, hf, ht⟩ := programBound_residual h
    exact ⟨a', f'+1, .reading r s.clock next ht, by omega, by omega, fun _ => by omega⟩
  | beginWrite r value next =>
    obtain ⟨a', f', ha, hf, ht⟩ := programBound_residual h
    exact ⟨a', f'+1, .writing r s.clock next ht, by omega, by omega, fun _ => by omega⟩
  | endRead r start next sample regular supplies =>
    obtain ⟨a', f', ha, hf, ht⟩ := h
    exact ⟨a', f', .ready (ht sample), ha, by omega, fun _ => by omega⟩
  | endWrite r start next =>
    obtain ⟨a', f', ha, hf, ht⟩ := h
    exact ⟨a', f', .ready ht, ha, by omega, fun _ => by omega⟩

theorem instruction_bound_exists {v₀ : α} {s : State n α} {phase phase' : Phase n α}
    (instruction : Instruction v₀ s phase phase')
    (bound : ∃ a f, PhaseBound phase a f) : ∃ a f, PhaseBound phase' a f := by
  obtain ⟨a, f, hb⟩ := bound
  obtain ⟨a', f', hb', _, _, _⟩ := instruction_bound instruction hb
  exact ⟨a', f', hb'⟩

theorem callStart_bound {v₀ : α} {p : Process n} {call index}
    {s : State n α} {phase} (h : CallStart v₀ p call index s phase) :
    ∃ a f, PhaseBound phase a f := by
  cases h with
  | writer s v past free => exact ⟨_, _, .ready (writerProgram_bound v)⟩
  | reader s j past free => exact ⟨_, _, .ready (readerProgram_bound j)⟩

theorem active_bound {v₀ : α} {s : State n α} (past : Reachable v₀ s)
    (p : Process n) (t : Thread n α) (active : s.threads p = some t) :
    ∃ a f, PhaseBound t.phase a f := by
  obtain ⟨start, phase, hs, segment⟩ := activeSegments_reachable past p t active
  have replay := callSegment_replay segment
  have hb := callStart_bound hs
  have general : ∀ {s₀ s : State n α} {phase₀ phase : Phase n α},
      CausalReplay v₀ p t.call t.writeIndex s₀ phase₀ s phase →
      (∃ a f, PhaseBound phase₀ a f) → ∃ a f, PhaseBound phase a f := by
    intro s₀ s phase₀ phase replay bound
    induction replay with
    | refl => exact bound
    | snoc prior step active instruction ih => exact instruction_bound_exists instruction ih
  exact general replay hb

/-- An occupied process cannot be reinvoked; all continuing steps retain its
call and write identities. A changed occupied thread consumes an instruction. -/
theorem step_thread_identity {v₀ : α} {s s' : State n α} {action : Action n}
    (step : Step v₀ s action s') (p : Process n) (t u : Thread n α)
    (before : s.threads p = some t) (after : s'.threads p = some u) :
    t.call = u.call ∧ t.writeIndex = u.writeIndex ∧ (t ≠ u → t.phase ≠ u.phase) := by
  have same : ∀ q replacement, p ≠ q →
      (Function.update s.threads q replacement) p = some u → t = u := by
    intro q replacement neq hu
    rw [Function.update_of_ne neq, before] at hu
    exact Option.some.inj hu
  cases step with
  | invokeWriter v free =>
    by_cases eq : p = .writer
    · subst p
      rw [free] at before
      contradiction
    · have eqtu := same .writer _ eq after
      cases eqtu
      exact ⟨rfl, rfl, by simp⟩
  | invokeReader j free =>
    by_cases eq : p = (.reader j)
    · subst p
      rw [free] at before
      contradiction
    · have eqtu := same (.reader j) _ eq after
      cases eqtu
      exact ⟨rfl, rfl, by simp⟩
  | order q x next b active control =>
    by_cases eq : p = q
    · subst p
      rw [active] at before
      cases Option.some.inj before
      simp only [withThread, Function.update_self, Option.some.injEq] at after
      cases after
      exact ⟨rfl, rfl, fun neq hphase => neq (by cases t; simp_all)⟩
    · have eqtu := same q _ eq after
      cases eqtu
      exact ⟨rfl, rfl, by simp⟩
  | token q x av bv choice next active control ha hb =>
    by_cases eq : p = q
    · subst p
      rw [active] at before
      cases Option.some.inj before
      simp only [withThread, Function.update_self, Option.some.injEq] at after
      cases after
      exact ⟨rfl, rfl, fun neq hphase => neq (by cases t; simp_all)⟩
    · have eqtu := same q _ eq after
      cases eqtu
      exact ⟨rfl, rfl, by simp⟩
  | beginRead q x r next active control =>
    by_cases eq : p = q
    · subst p
      rw [active] at before
      cases Option.some.inj before
      simp only [withThread, Function.update_self, Option.some.injEq] at after
      cases after
      exact ⟨rfl, rfl, fun neq hphase => neq (by cases t; simp_all)⟩
    · have eqtu := same q _ eq after
      cases eqtu
      exact ⟨rfl, rfl, by simp⟩
  | endRead q x r start next sample active control regular supplies =>
    by_cases eq : p = q
    · subst p
      rw [active] at before
      cases Option.some.inj before
      simp only [withThread, Function.update_self, Option.some.injEq] at after
      cases after
      exact ⟨rfl, rfl, fun neq hphase => neq (by cases t; simp_all)⟩
    · have eqtu := same q _ eq after
      cases eqtu
      exact ⟨rfl, rfl, by simp⟩
  | beginWrite q x r value next active control owner =>
    by_cases eq : p = q
    · subst p
      rw [active] at before
      cases Option.some.inj before
      simp only [withThread, Function.update_self, Option.some.injEq] at after
      cases after
      exact ⟨rfl, rfl, fun neq hphase => neq (by cases t; simp_all)⟩
    · have eqtu := same q _ eq after
      cases eqtu
      exact ⟨rfl, rfl, by simp⟩
  | endWrite q x r start next active control =>
    by_cases eq : p = q
    · subst p
      rw [active] at before
      cases Option.some.inj before
      simp only [withThread, Function.update_self, Option.some.injEq] at after
      cases after
      exact ⟨rfl, rfl, fun neq hphase => neq (by cases t; simp_all)⟩
    · have eqtu := same q _ eq after
      cases eqtu
      exact ⟨rfl, rfl, by simp⟩
  | respond q x result active control =>
    by_cases eq : p = q
    · subst p
      simp [withThread] at after
    · have eqtu := same q _ eq after
      cases eqtu
      exact ⟨rfl, rfl, by simp⟩
  | idle =>
    rw [before] at after
    cases Option.some.inj after
    exact ⟨rfl, rfl, by simp⟩

theorem step_active_bound {v₀ : α} {s s' : State n α} {action : Action n}
    (step : Step v₀ s action s') (p : Process n) (t u : Thread n α) {a f}
    (before : s.threads p = some t) (after : s'.threads p = some u)
    (bound : PhaseBound t.phase a f) :
    ∃ a' f', PhaseBound u.phase a' f' ∧ a' ≤ a ∧ f' ≤ f ∧ (t ≠ u → f' < f) := by
  obtain ⟨a', f', hb, ha, hf, hs⟩ :=
    instruction_bound (instruction_of_step step p t u before after) bound
  exact ⟨a', f', hb, ha, hf, fun h => hs ((step_thread_identity step p t u before after).2.2 h)⟩

theorem run_reachable {v₀ : α} {states : Nat → State n α}
    (run : Run v₀ states) (k : Nat) : Reachable v₀ (states k) := by
  induction k with
  | zero => rw [run.1]; exact ⟨[], .refl⟩
  | succ k ih =>
    obtain ⟨a, hs⟩ := run.2 k
    exact reachable_step ih hs

theorem run_bound_forward {v₀ : α} {states : Nat → State n α}
    (run : Run v₀ states) (p : Process n) (k m : Nat) (le : k ≤ m)
    (occupied : ∀ i, k ≤ i → ∃ t, (states i).threads p = some t)
    (t : Thread n α) (active : (states k).threads p = some t) {a f}
    (bound : PhaseBound t.phase a f) :
    ∃ u a' f', (states m).threads p = some u ∧ PhaseBound u.phase a' f' ∧ f' ≤ f := by
  obtain ⟨distance, rfl⟩ := Nat.exists_eq_add_of_le le
  induction distance with
  | zero => exact ⟨t, a, f, by simpa using active, bound, Nat.le_refl _⟩
  | succ d ih =>
    obtain ⟨u, a', f', hu, hb, hf⟩ := ih (by omega)
    obtain ⟨v, hv⟩ := occupied (k+d+1) (by omega)
    obtain ⟨action, hs⟩ := run.2 (k+d)
    obtain ⟨a'', f'', hb', _, hf', _⟩ := step_active_bound hs p u v hu (by simpa [Nat.add_assoc] using hv) hb
    exact ⟨v, a'', f'', by simpa [Nat.add_assoc] using hv, hb', Nat.le_trans hf' hf⟩

/-- Continued own scheduling suffices for departure in this endpoint model:
it already requires a waiting primitive's thread eventually to change. -/
theorem eventual_thread_idle {v₀ : α} {states : Nat → State n α}
    (run : Run v₀ states) (p : Process n) (schedule : ContinuedOwnScheduling states p)
    (k : Nat) : ∃ m, k ≤ m ∧ (states m).threads p = none := by
  classical
  by_contra never
  have occupied : ∀ i, k ≤ i → ∃ t, (states i).threads p = some t := by
    intro i hi
    cases h : (states i).threads p with
    | none => exact False.elim (never ⟨i, hi, h⟩)
    | some t => exact ⟨t, rfl⟩
  have existsFuel : ∃ f, ∃ i t a, k ≤ i ∧ (states i).threads p = some t ∧ PhaseBound t.phase a f := by
    obtain ⟨t, ht⟩ := occupied k (Nat.le_refl _)
    obtain ⟨a, f, hb⟩ := active_bound (run_reachable run k) p t ht
    exact ⟨f, k, t, a, Nat.le_refl _, ht, hb⟩
  obtain ⟨i, t, a, hi, ht, hb⟩ := Nat.find_spec existsFuel
  rcases schedule i t ht with ⟨m, hm, idle⟩ | ⟨m, u, hm, hu, changed⟩
  · exact never ⟨m, by omega, idle⟩
  · obtain ⟨u', a', f', hu', hb', hf'⟩ :=
      run_bound_forward run p i m hm (fun j hj => occupied j (by omega)) t ht hb
    rw [hu] at hu'
    cases Option.some.inj hu'
    obtain ⟨v, hv⟩ := occupied (m+1) (by omega)
    obtain ⟨action, hs⟩ := run.2 m
    have neq : u ≠ v := by intro eq; subst v; exact changed hv
    obtain ⟨a'', f'', hb'', _, _, decrease⟩ := step_active_bound hs p u v hu hv hb'
    have lower : f'' < Nat.find existsFuel := Nat.lt_of_lt_of_le (decrease neq) hf'
    exact Nat.find_min existsFuel lower ⟨m+1, v, a'', by omega, hv, hb''⟩

/-- A pending archived call is attached to its currently occupied caller. -/
def PendingCalls (s : State n α) : Prop :=
  ∀ c ∈ s.calls, c.response = none → ∃ t,
    s.threads c.process = some t ∧ t.call = c.id

theorem pendingCalls_step {v₀ : α} {s s' : State n α} {action : Action n}
    (step : Step v₀ s action s') (pending : PendingCalls s) : PendingCalls s' := by
  cases step with
  | invokeWriter v free =>
    intro c hc hr
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨t, ht, hid⟩ := pending c hc hr
      have neq : c.process ≠ .writer := by intro eq; rw [eq, free] at ht; contradiction
      exact ⟨t, by simpa [withThread, Function.update_of_ne neq] using ht, hid⟩
    · cases List.mem_singleton.mp hc
      exact ⟨⟨s.clock, s.nextWrite, .ready (writerProgram v)⟩, by simp [withThread], rfl⟩
  | invokeReader j free =>
    intro c hc hr
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨t, ht, hid⟩ := pending c hc hr
      have neq : c.process ≠ .reader j := by intro eq; rw [eq, free] at ht; contradiction
      exact ⟨t, by simpa [withThread, Function.update_of_ne neq] using ht, hid⟩
    · cases List.mem_singleton.mp hc
      exact ⟨⟨s.clock, 0, .ready (readerProgram j)⟩, by simp [withThread], rfl⟩
  | respond q x result active control =>
    intro c hc hr
    obtain ⟨old, hold, eq⟩ := List.mem_map.mp hc
    split at eq
    · cases eq; cases hr
    · rename_i neq
      cases eq
      obtain ⟨t, ht, hid⟩ := pending c hold hr
      have different : c.process ≠ q := by
        intro same
        rw [same, active] at ht
        cases Option.some.inj ht
        exact neq hid.symm
      exact ⟨t, by simpa [withThread, Function.update_of_ne different] using ht, hid⟩
  | idle => exact pending
  | order q x next b active control =>
    intro c hc hr
    obtain ⟨t, ht, hid⟩ := pending c hc hr
    by_cases eq : c.process = q
    · rw [eq, active] at ht
      cases Option.some.inj ht
      exact ⟨{x with phase := .ready (next b)}, by simp [withThread, eq], hid⟩
    · exact ⟨t, by simpa [withThread, Function.update_of_ne eq] using ht, hid⟩
  | token q x av bv choice next active control ha hb =>
    intro c hc hr
    obtain ⟨t, ht, hid⟩ := pending c hc hr
    by_cases eq : c.process = q
    · rw [eq, active] at ht
      cases Option.some.inj ht
      exact ⟨{x with phase := .ready (next choice)}, by simp [withThread, eq], hid⟩
    · exact ⟨t, by simpa [withThread, Function.update_of_ne eq] using ht, hid⟩
  | beginRead q x r next active control =>
    intro c hc hr
    obtain ⟨t, ht, hid⟩ := pending c hc hr
    by_cases eq : c.process = q
    · rw [eq, active] at ht
      cases Option.some.inj ht
      exact ⟨{x with phase := .reading r s.clock next}, by simp [withThread, eq], hid⟩
    · exact ⟨t, by simpa [withThread, Function.update_of_ne eq] using ht, hid⟩
  | endRead q x r start next sample active control regular supplies =>
    intro c hc hr
    obtain ⟨t, ht, hid⟩ := pending c hc hr
    by_cases eq : c.process = q
    · rw [eq, active] at ht
      cases Option.some.inj ht
      exact ⟨{x with phase := .ready (next sample)}, by simp [withThread, eq], hid⟩
    · exact ⟨t, by simpa [withThread, Function.update_of_ne eq] using ht, hid⟩
  | beginWrite q x r value next active control owner =>
    intro c hc hr
    obtain ⟨t, ht, hid⟩ := pending c hc hr
    by_cases eq : c.process = q
    · rw [eq, active] at ht
      cases Option.some.inj ht
      exact ⟨{x with phase := .writing r s.clock next}, by simp [withThread, eq], hid⟩
    · exact ⟨t, by simpa [withThread, Function.update_of_ne eq] using ht, hid⟩
  | endWrite q x r start next active control =>
    intro c hc hr
    obtain ⟨t, ht, hid⟩ := pending c hc hr
    by_cases eq : c.process = q
    · rw [eq, active] at ht
      cases Option.some.inj ht
      exact ⟨{x with phase := .ready next}, by simp [withThread, eq], hid⟩
    · exact ⟨t, by simpa [withThread, Function.update_of_ne eq] using ht, hid⟩

theorem pendingCalls_reachable {v₀ : α} {s : State n α}
    (past : Reachable v₀ s) : PendingCalls s := by
  obtain ⟨actions, trace⟩ := past
  have general : ∀ {s s' : State n α} {actions}, (lts v₀).MTr s actions s' →
      PendingCalls s → PendingCalls s' := by
    intro s s' actions trace pending
    induction trace with
    | refl => exact pending
    | stepL step tail ih => exact ih (pendingCalls_step step pending)
  exact general trace (by simp [PendingCalls, initial])

theorem run_call_extension {v₀ : α} {states : Nat → State n α}
    (run : Run v₀ states) (k m : Nat) (le : k ≤ m) (c : Call n α)
    (member : c ∈ (states k).calls) :
    ∃ later ∈ (states m).calls, later.id = c.id ∧ later.process = c.process := by
  obtain ⟨distance, rfl⟩ := Nat.exists_eq_add_of_le le
  induction distance with
  | zero => exact ⟨c, by simpa using member, rfl, rfl⟩
  | succ d ih =>
    obtain ⟨u, hu, hi, hp⟩ := ih (by omega)
    obtain ⟨action, hs⟩ := run.2 (k+d)
    obtain ⟨v, hv, extension⟩ := step_call_extension hs u hu
    exact ⟨v, by simpa [Nat.add_assoc] using hv, extension.1.trans hi, extension.2.1.trans hp⟩

/-- Matching high-level response, including permanently archived old versions.
The eventual response follows caller departure; no other process is scheduled. -/
theorem own_call_eventually_completed {v₀ : α} {states : Nat → State n α}
    (run : Run v₀ states) (p : Process n) (schedule : ContinuedOwnScheduling states p)
    (k : Nat) (c : Call n α) (member : c ∈ (states k).calls) (process : c.process = p) :
    ∃ m completed, k ≤ m ∧ completed ∈ (states m).calls ∧
      completed.id = c.id ∧ completed.process = p ∧ Completed completed := by
  obtain ⟨m, hm, idle⟩ := eventual_thread_idle run p schedule k
  obtain ⟨later, hl, hid, hp⟩ := run_call_extension run k m hm c member
  have response : later.response ≠ none := by
    intro absent
    obtain ⟨t, ht, _⟩ := pendingCalls_reachable (run_reachable run m) later hl absent
    rw [hp, process, idle] at ht
    contradiction
  cases h : later.response with
  | none => exact False.elim (response h)
  | some pair => exact ⟨m, later, hm, hl, hid, hp.trans process, pair.1, pair.2, h⟩

def CallIdsPast (s : State n α) : Prop := ∀ c ∈ s.calls, c.id < s.clock

theorem callIdsPast_step {v₀ : α} {s s' : State n α} {action}
    (step : Step v₀ s action s') (past : CallIdsPast s) : CallIdsPast s' := by
  cases step with
  | invokeWriter v free =>
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact Nat.lt_succ_of_lt (past c hc)
    · cases List.mem_singleton.mp hc; exact Nat.lt_succ_self _
  | invokeReader j free =>
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact Nat.lt_succ_of_lt (past c hc)
    · cases List.mem_singleton.mp hc; exact Nat.lt_succ_self _
  | respond q t result active control =>
    intro c hc
    obtain ⟨old, hold, eq⟩ := List.mem_map.mp hc
    have hp := past old hold
    split at eq <;> cases eq <;> exact Nat.lt_succ_of_lt hp
  | _ => intro c hc; exact Nat.lt_succ_of_lt (past c hc)

def OwnershipInvariant (s : State n α) : Prop :=
  ∀ p t, s.threads p = some t → t.call < s.clock ∧
    ∀ c ∈ s.calls, c.id = t.call → c.process = p ∧ c.response = none

theorem ownership_change {s s' : State n α} (old : OwnershipInvariant s)
    (q : Process n) (t : Thread n α) (active : s.threads q = some t)
    (replacement : Option (Thread n α))
    (sameCall : ∀ u, replacement = some u → u.call = t.call)
    (threads : s'.threads = Function.update s.threads q replacement)
    (calls : s'.calls = s.calls) (clock : s.clock < s'.clock) : OwnershipInvariant s' := by
  intro p u hu
  by_cases eq : p = q
  · subst p
    have hr : replacement = some u := by simpa [threads] using hu
    have hid := sameCall u hr
    obtain ⟨hpast, howned⟩ := old q t active
    exact ⟨by omega, fun c hc h => howned c (by simpa [calls] using hc) (h.trans hid)⟩
  · have before : s.threads p = some u := by simpa [threads, Function.update_of_ne eq] using hu
    obtain ⟨hpast, howned⟩ := old p u before
    exact ⟨by omega, fun c hc h => howned c (by simpa [calls] using hc) h⟩

theorem ownership_step {v₀ : α} {s s' : State n α} {action}
    (step : Step v₀ s action s') (past : CallIdsPast s)
    (old : OwnershipInvariant s) : OwnershipInvariant s' := by
  cases step with
  | invokeWriter v free =>
    intro p t ht
    by_cases eq : p = .writer
    · subst p
      simp only [withThread, Function.update_self, Option.some.injEq] at ht
      cases ht
      refine ⟨Nat.lt_succ_self _, ?_⟩
      intro c hc hid
      rcases List.mem_append.mp hc with hc | hc
      · have hp := past c hc; simp only at hid; omega
      · cases List.mem_singleton.mp hc; exact ⟨rfl, rfl⟩
    · have before : s.threads p = some t := by simpa [withThread, Function.update_of_ne eq] using ht
      obtain ⟨hp, ho⟩ := old p t before
      refine ⟨Nat.lt_succ_of_lt hp, ?_⟩
      intro c hc hid
      rcases List.mem_append.mp hc with hc | hc
      · exact ho c hc hid
      · cases List.mem_singleton.mp hc; simp only at hid; omega
  | invokeReader j free =>
    intro p t ht
    by_cases eq : p = .reader j
    · subst p
      simp only [withThread, Function.update_self, Option.some.injEq] at ht
      cases ht
      refine ⟨Nat.lt_succ_self _, ?_⟩
      intro c hc hid
      rcases List.mem_append.mp hc with hc | hc
      · have hp := past c hc; simp only at hid; omega
      · cases List.mem_singleton.mp hc; exact ⟨rfl, rfl⟩
    · have before : s.threads p = some t := by simpa [withThread, Function.update_of_ne eq] using ht
      obtain ⟨hp, ho⟩ := old p t before
      refine ⟨Nat.lt_succ_of_lt hp, ?_⟩
      intro c hc hid
      rcases List.mem_append.mp hc with hc | hc
      · exact ho c hc hid
      · cases List.mem_singleton.mp hc; simp only at hid; omega
  | respond q x result active control =>
    intro p t ht
    have neq : p ≠ q := by intro eq; subst p; simp [withThread] at ht
    have before : s.threads p = some t := by simpa [withThread, Function.update_of_ne neq] using ht
    obtain ⟨hp, ho⟩ := old p t before
    refine ⟨Nat.lt_succ_of_lt hp, ?_⟩
    intro c hc hid
    obtain ⟨prior, hprior, heq⟩ := List.mem_map.mp hc
    split at heq
    · rename_i sameId
      cases heq
      have ownP := (ho prior hprior hid).1
      have ownQ := (old q x active).2 prior hprior sameId
      exact False.elim (neq (ownP.symm.trans ownQ.1))
    · cases heq
      exact ho c hprior hid
  | idle =>
    intro p t ht
    obtain ⟨hp, ho⟩ := old p t ht
    exact ⟨Nat.lt_succ_of_lt hp, ho⟩
  | order q x next b active control =>
    apply ownership_change old q x active (some {x with phase := .ready (next b)})
    · intro u eq; cases eq; rfl
    · rfl
    · rfl
    · exact Nat.lt_succ_self _
  | token q x av bv choice next active control ha hb =>
    apply ownership_change old q x active (some {x with phase := .ready (next choice)})
    · intro u eq; cases eq; rfl
    · rfl
    · rfl
    · exact Nat.lt_succ_self _
  | beginRead q x r next active control =>
    apply ownership_change old q x active (some {x with phase := .reading r s.clock next})
    · intro u eq; cases eq; rfl
    · rfl
    · rfl
    · exact Nat.lt_succ_self _
  | endRead q x r start next sample active control regular supplies =>
    apply ownership_change old q x active (some {x with phase := .ready (next sample)})
    · intro u eq; cases eq; rfl
    · rfl
    · rfl
    · exact Nat.lt_succ_self _
  | beginWrite q x r value next active control owner =>
    apply ownership_change old q x active (some {x with phase := .writing r s.clock next})
    · intro u eq; cases eq; rfl
    · rfl
    · rfl
    · exact Nat.lt_succ_self _
  | endWrite q x r start next active control =>
    apply ownership_change old q x active (some {x with phase := .ready next})
    · intro u eq; cases eq; rfl
    · rfl
    · rfl
    · exact Nat.lt_succ_self _

theorem trace_call_extension {v₀ : α} {s s' : State n α} {actions}
    (trace : (lts v₀).MTr s actions s') (c : Call n α) (hc : c ∈ s.calls) :
    ∃ later ∈ s'.calls, later.id = c.id := by
  induction trace generalizing c with
  | refl => exact ⟨c, hc, rfl⟩
  | stepL step tail ih =>
    obtain ⟨u, hu, he⟩ := step_call_extension step c hc
    obtain ⟨v, hv, hi⟩ := ih u hu
    exact ⟨v, hv, hi.trans he.1⟩

theorem active_call_mem {v₀ : α} {s : State n α} (past : Reachable v₀ s)
    (p : Process n) (t : Thread n α) (active : s.threads p = some t) :
    ∃ c ∈ s.calls, c.id = t.call := by
  obtain ⟨start, phase, hs, segment⟩ := activeSegments_reachable past p t active
  have general : ∀ {p : Process n} {call index : Nat} {start : State n α} {phase : Phase n α}, CallStart v₀ p call index start phase →
      ∃ c ∈ start.calls, c.id = call := by
    intro p call index start phase hs
    cases hs with
    | writer s v past free => exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
    | reader s j past free => exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
  have atStart := general hs
  obtain ⟨c, hc, hid⟩ := atStart
  obtain ⟨actions, trace⟩ := callSegment_trace segment
  obtain ⟨later, hl, hi⟩ := trace_call_extension trace c hc
  exact ⟨later, hl, hi.trans hid⟩

theorem active_calls_distinct {v₀ : α} {s : State n α} (past : Reachable v₀ s)
    (owned : OwnershipInvariant s) (p q : Process n) (t u : Thread n α)
    (ht : s.threads p = some t) (hu : s.threads q = some u)
    (sameCall : t.call = u.call) : p = q := by
  obtain ⟨c, hc, hid⟩ := active_call_mem past p t ht
  exact ((owned p t ht).2 c hc hid).1.symm.trans
    ((owned q u hu).2 c hc (hid.trans sameCall)).1

def AccessCount (s : State n α) (call : Nat) : Nat :=
  (s.primitives.filter (fun e => e.call == call)).length

theorem accessCount_close (s : State n α) (start time : Nat) (witness : Option Nat) (call : Nat) :
    AccessCount {s with primitives := closePrimitive s.primitives start time witness} call = AccessCount s call := by
  unfold AccessCount closePrimitive
  have general : ∀ events : List (Primitive n),
      ((events.map fun e => if e.id = start then {e with finish := some time, witness := witness} else e).filter
        (fun e => e.call == call)).length = (events.filter (fun e => e.call == call)).length := by
    intro events
    induction events with
    | nil => rfl
    | cons e rest ih =>
      by_cases he : e.id = start <;> by_cases hc : e.call = call <;>
        simp [he, hc, ih]
  exact general s.primitives

theorem accessCount_append (s : State n α) (event : Primitive n) (call : Nat) :
    AccessCount {s with primitives := s.primitives ++ [event]} call =
      AccessCount s call + if event.call = call then 1 else 0 := by
  by_cases eq : event.call = call <;> simp [AccessCount, List.filter_append, eq]

def PrimitiveCallsPast (s : State n α) : Prop := ∀ e ∈ s.primitives, e.call < s.clock

theorem primitiveCallsPast_step {v₀ : α} {s s' : State n α} {action}
    (step : Step v₀ s action s') (owned : OwnershipInvariant s)
    (past : PrimitiveCallsPast s) : PrimitiveCallsPast s' := by
  cases step with
  | beginRead q t r next active control =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact Nat.lt_succ_of_lt (past e he)
    · cases List.mem_singleton.mp he; exact Nat.lt_succ_of_lt (owned q t active).1
  | beginWrite q t r value next active control owner =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact Nat.lt_succ_of_lt (past e he)
    · cases List.mem_singleton.mp he; exact Nat.lt_succ_of_lt (owned q t active).1
  | endRead q t r start next sample active control regular supplies =>
    intro e he
    obtain ⟨old, hold, eq⟩ := List.mem_map.mp he
    have hp := past old hold
    split at eq <;> cases eq <;> exact Nat.lt_succ_of_lt hp
  | endWrite q t r start next active control =>
    intro e he
    obtain ⟨old, hold, eq⟩ := List.mem_map.mp he
    have hp := past old hold
    split at eq <;> cases eq <;> exact Nat.lt_succ_of_lt hp
  | _ => intro e he; exact Nat.lt_succ_of_lt (past e he)

theorem accessCount_fresh (s : State n α) (past : PrimitiveCallsPast s) : AccessCount s s.clock = 0 := by
  unfold AccessCount
  have empty : s.primitives.filter (fun e => e.call == s.clock) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    have h := past e he
    simp only [beq_iff_eq]
    exact Nat.ne_of_lt h
  rw [empty]; rfl

def WorkInvariant (s : State n α) : Prop :=
  ∀ p t, s.threads p = some t → ∃ a f,
    PhaseBound t.phase a f ∧ AccessCount s t.call + a ≤ primitiveBudget n p

def CallsBudget (s : State n α) : Prop :=
  ∀ c ∈ s.calls, AccessCount s c.id ≤ primitiveBudget n c.process

theorem work_change {v₀ : α} {s s' : State n α}
    (past : Reachable v₀ s) (owned : OwnershipInvariant s) (work : WorkInvariant s)
    (q : Process n) (t : Thread n α) (active : s.threads q = some t)
    (replacement : Option (Thread n α))
    (threads : s'.threads = Function.update s.threads q replacement)
    (new : ∀ a f, PhaseBound t.phase a f → ∀ u, replacement = some u →
      ∃ a' f', PhaseBound u.phase a' f' ∧ u.call = t.call ∧
        AccessCount s' u.call + a' ≤ AccessCount s t.call + a)
    (otherCounts : ∀ call, call ≠ t.call → AccessCount s' call = AccessCount s call) :
    WorkInvariant s' := by
  intro p u hu
  by_cases eq : p = q
  · subst p
    obtain ⟨a, f, hb, budget⟩ := work q t active
    have hr : replacement = some u := by simpa [threads] using hu
    obtain ⟨a', f', hb', _, cost⟩ := new a f hb u hr
    exact ⟨a', f', hb', Nat.le_trans cost budget⟩
  · have before : s.threads p = some u := by simpa [threads, Function.update_of_ne eq] using hu
    obtain ⟨a, f, hb, budget⟩ := work p u before
    have neq : u.call ≠ t.call := by
      intro same
      exact eq (active_calls_distinct past owned p q u t before active same)
    exact ⟨a, f, hb, by simpa [otherCounts u.call neq] using budget⟩

theorem work_step {v₀ : α} {s s' : State n α} {action}
    (past : Reachable v₀ s) (step : Step v₀ s action s')
    (owned : OwnershipInvariant s) (primitivePast : PrimitiveCallsPast s)
    (work : WorkInvariant s) : WorkInvariant s' := by
  cases step with
  | invokeWriter v free =>
    intro p t ht
    by_cases eq : p = .writer
    · subst p
      simp only [withThread, Function.update_self, Option.some.injEq] at ht
      cases ht
      exact ⟨_, _, .ready (writerProgram_bound v), by
        change AccessCount s s.clock + primitiveBudget n .writer ≤ primitiveBudget n .writer
        rw [accessCount_fresh s primitivePast]; omega⟩
    · exact work p t (by simpa [withThread, Function.update_of_ne eq] using ht)
  | invokeReader j free =>
    intro p t ht
    by_cases eq : p = .reader j
    · subst p
      simp only [withThread, Function.update_self, Option.some.injEq] at ht
      cases ht
      exact ⟨_, _, .ready (readerProgram_bound j), by
        change AccessCount s s.clock + primitiveBudget n (.reader j) ≤ primitiveBudget n (.reader j)
        rw [accessCount_fresh s primitivePast]; omega⟩
    · exact work p t (by simpa [withThread, Function.update_of_ne eq] using ht)
  | idle => exact work
  | respond q t result active control =>
    apply work_change past owned work q t active none rfl
    · intro a f hb u impossible; cases impossible
    · intro call neq; rfl
  | order q t next b active control =>
    apply work_change past owned work q t active (some {t with phase := .ready (next b)}) rfl
    · intro a f hb u eq
      cases eq
      have hr := phaseBound_residual hb
      rw [control] at hr
      obtain ⟨a', f', ha', hf', tail⟩ := programBound_residual hr
      refine ⟨a', f', .ready (tail b), rfl, ?_⟩
      change AccessCount s t.call + a' ≤ AccessCount s t.call + a
      omega
    · intro call neq
      rfl
  | token q t av bv choice next active control ha hb =>
    apply work_change past owned work q t active (some {t with phase := .ready (next choice)}) rfl
    · intro a f hb u eq
      cases eq
      have hr := phaseBound_residual hb
      rw [control] at hr
      obtain ⟨a', f', ha', hf', tail⟩ := programBound_residual hr
      refine ⟨a', f', .ready (tail choice), rfl, ?_⟩
      change AccessCount s t.call + a' ≤ AccessCount s t.call + a
      omega
    · intro call neq
      rfl
  | beginRead q t r next active control =>
    apply work_change past owned work q t active (some {t with phase := .reading r s.clock next}) rfl
    · intro a f hb u eq
      cases eq
      have hr := phaseBound_residual hb
      rw [control] at hr
      obtain ⟨a', f', ha', hf', tail⟩ := programBound_residual hr
      refine ⟨a', f'+1, .reading r s.clock next tail, rfl, ?_⟩
      have count := accessCount_append s (⟨s.clock, t.call, r, false, s.clock, none, none⟩) t.call
      simp only [ite_true] at count
      change AccessCount {s with primitives := s.primitives ++ [_]} t.call + a' ≤ _
      rw [count]; omega
    · intro call neq
      simp [AccessCount, List.filter_append, Ne.symm neq]
  | beginWrite q t r value next active control owner =>
    apply work_change past owned work q t active (some {t with phase := .writing r s.clock next}) rfl
    · intro a f hb u eq
      cases eq
      have hr := phaseBound_residual hb
      rw [control] at hr
      obtain ⟨a', f', ha', hf', tail⟩ := programBound_residual hr
      refine ⟨a', f'+1, .writing r s.clock next tail, rfl, ?_⟩
      have count := accessCount_append s (⟨s.clock, t.call, r, true, s.clock, none, none⟩) t.call
      simp only [ite_true] at count
      change AccessCount {s with primitives := s.primitives ++ [_]} t.call + a' ≤ _
      rw [count]; omega
    · intro call neq
      simp [AccessCount, List.filter_append, Ne.symm neq]
  | endRead q t r start next sample active control regular supplies =>
    apply work_change past owned work q t active (some {t with phase := .ready (next sample)}) rfl
    · intro a f hb u eq
      cases eq
      have hr := phaseBound_residual hb
      rw [control] at hr
      obtain ⟨a', f', ha', hf', tail⟩ := hr
      refine ⟨a', f', .ready (tail sample), rfl, ?_⟩
      have count := accessCount_close s start s.clock sample.witness t.call
      change AccessCount {s with primitives := closePrimitive s.primitives start s.clock sample.witness} t.call + a' ≤ _
      rw [count]; omega
    · intro call neq
      exact accessCount_close s start s.clock sample.witness call
  | endWrite q t r start next active control =>
    apply work_change past owned work q t active (some {t with phase := .ready next}) rfl
    · intro a f hb u eq
      cases eq
      have hr := phaseBound_residual hb
      rw [control] at hr
      obtain ⟨a', f', ha', hf', tail⟩ := hr
      refine ⟨a', f', .ready tail, rfl, ?_⟩
      have count := accessCount_close s start s.clock none t.call
      change AccessCount {s with primitives := closePrimitive s.primitives start s.clock none} t.call + a' ≤ _
      rw [count]; omega
    · intro call neq
      exact accessCount_close s start s.clock none call

theorem callsBudget_begin {s s' : State n α} (owned : OwnershipInvariant s)
    (budget : CallsBudget s) (q : Process n) (t : Thread n α)
    (active : s.threads q = some t)
    (ownBudget : AccessCount s t.call + 1 ≤ primitiveBudget n q)
    (calls : s'.calls = s.calls)
    (counts : ∀ call, AccessCount s' call = AccessCount s call + if t.call = call then 1 else 0) :
    CallsBudget s' := by
  intro c hc
  have member : c ∈ s.calls := by simpa [calls] using hc
  rw [counts c.id]
  by_cases eq : t.call = c.id
  · have process := ((owned q t active).2 c member eq.symm).1
    simpa [eq, process] using ownBudget
  · simpa [eq] using budget c member

theorem callsBudget_step {v₀ : α} {s s' : State n α} {action}
    (step : Step v₀ s action s') (owned : OwnershipInvariant s)
    (primitivePast : PrimitiveCallsPast s) (work : WorkInvariant s)
    (budget : CallsBudget s) : CallsBudget s' := by
  cases step with
  | invokeWriter v free =>
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact budget c hc
    · cases List.mem_singleton.mp hc
      change AccessCount s s.clock ≤ _
      rw [accessCount_fresh s primitivePast]; exact Nat.zero_le _
  | invokeReader j free =>
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact budget c hc
    · cases List.mem_singleton.mp hc
      change AccessCount s s.clock ≤ _
      rw [accessCount_fresh s primitivePast]; exact Nat.zero_le _
  | respond q t result active control =>
    intro c hc
    obtain ⟨old, hold, eq⟩ := List.mem_map.mp hc
    have hb := budget old hold
    split at eq <;> cases eq <;> exact hb
  | endRead q t r start next sample active control regular supplies =>
    intro c hc
    have count := accessCount_close s start s.clock sample.witness c.id
    change AccessCount {s with primitives := closePrimitive s.primitives start s.clock sample.witness} c.id ≤ _
    rw [count]; exact budget c hc
  | endWrite q t r start next active control =>
    intro c hc
    have count := accessCount_close s start s.clock none c.id
    change AccessCount {s with primitives := closePrimitive s.primitives start s.clock} c.id ≤ _
    rw [count]; exact budget c hc
  | beginRead q t r next active control =>
    apply callsBudget_begin owned budget q t active
    · obtain ⟨a, f, hb, hcost⟩ := work q t active
      have hr := phaseBound_residual hb
      rw [control] at hr
      obtain ⟨a', f', ha, hf, tail⟩ := programBound_residual hr
      omega
    · rfl
    · intro call
      exact accessCount_append s (⟨s.clock, t.call, r, false, s.clock, none, none⟩) call
  | beginWrite q t r value next active control owner =>
    apply callsBudget_begin owned budget q t active
    · obtain ⟨a, f, hb, hcost⟩ := work q t active
      have hr := phaseBound_residual hb
      rw [control] at hr
      obtain ⟨a', f', ha, hf, tail⟩ := programBound_residual hr
      omega
    · rfl
    · intro call
      exact accessCount_append s (⟨s.clock, t.call, r, true, s.clock, none, none⟩) call
  | _ => exact budget

def CompletionInvariant (s : State n α) : Prop :=
  CallIdsPast s ∧ OwnershipInvariant s ∧ PrimitiveCallsPast s ∧ WorkInvariant s ∧ CallsBudget s

theorem completionInvariant_step {v₀ : α} {s s' : State n α} {action}
    (past : Reachable v₀ s) (step : Step v₀ s action s')
    (inv : CompletionInvariant s) : CompletionInvariant s' := by
  obtain ⟨calls, owned, primitives, work, budget⟩ := inv
  exact ⟨callIdsPast_step step calls, ownership_step step calls owned,
    primitiveCallsPast_step step owned primitives,
    work_step past step owned primitives work,
    callsBudget_step step owned primitives work budget⟩

theorem completionInvariant_reachable {v₀ : α} {s : State n α}
    (past : Reachable v₀ s) : CompletionInvariant s := by
  obtain ⟨actions, trace⟩ := past
  have general : ∀ {s s' : State n α} {actions}, (lts v₀).MTr s actions s' →
      Reachable v₀ s → CompletionInvariant s → CompletionInvariant s' := by
    intro s s' actions trace hs inv
    induction trace with
    | refl => exact inv
    | stepL step tail ih => exact ih (reachable_step hs step) (completionInvariant_step hs step inv)
  exact general trace ⟨[], .refl⟩ (by
    simp [CompletionInvariant, CallIdsPast, OwnershipInvariant, PrimitiveCallsPast,
      WorkInvariant, CallsBudget, initial])

/-- The exact protected M3 target, on the original both-orders model. The
termination premise is retained; the endpoint scheduling condition suffices. -/
theorem ownCompletion : OwnCompletion n α := by
  intro v₀ states p positive run schedule primitives k c member process
  obtain ⟨m, completed, hm, hc, hid, hp, done⟩ :=
    own_call_eventually_completed run p schedule k c member process
  have budget := (completionInvariant_reachable (run_reachable run m)).2.2.2.2 completed hc
  exact ⟨m, completed, hm, hc, hid, done, by simpa [AccessCount, hid, hp] using budget⟩

theorem restrictedOwnCompletion : RestrictedOwnCompletion n α := by
  intro v₀ states p positive run schedule primitives
  exact ownCompletion v₀ states p positive (restricted_run_original run) schedule primitives

end MultiReaderAtomic
