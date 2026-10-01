import Peterson.EconomicalSolutions.Algorithm2Foundation

/-! Initialized solo execution, measured in successful instructions of the
frozen interpreter. The restricted LTS below merely records the selected
command and excludes critical pre-states; it adds no algorithm operations. -/
namespace EconomicalSolutions.Algorithm2.Solo

variable {n : Nat}

/-- All peers keep their initialized local state. -/
def state (p : Proc n) (l : Local n) : State n := setLocal (initial n) p l

@[simp] theorem state_self (p : Proc n) (l : Local n) : state p l p = l := by
  simp [state, setLocal]

@[simp] theorem state_other (p q : Proc n) (l : Local n) (h : q ≠ p) :
    state p l q = ⟨.idle, dead⟩ := by simp [state, setLocal, h, initial]

@[simp] theorem set_state (p : Proc n) (l l' : Local n) :
    setLocal (state p l) p l' = state p l' := by
  funext i
  by_cases h : i = p <;> simp [setLocal, state, h]

@[simp] theorem state_idle (p : Proc n) : state p ⟨.idle, dead⟩ = initial n := by
  funext i
  simp [state, setLocal, initial]

theorem read_dead (p : Proc n) (l : Local n) (j : Leaf n) (h : j.val ≠ p.val) :
    visible (state p l) j = dead := by
  unfold state
  rw [visible_setLocal_other _ _ _ _ h]
  simp [visible, initial]

/-- A successful actual run of p, carrying the actual label, before entry.
The no-critical precondition makes every finite path a first-entry path. -/
def soloLTS (cfg : Config n) (p : Proc n) : Cslib.LTS (State n) (Label n) :=
  ⟨fun s a t => next cfg s (.run p) = some t ∧ label s (.run p) = a ∧ (s p).pc ≠ .cs⟩

abbrev Steps (cfg : Config n) (p : Proc n) (s : State n) (m : Nat) (t : State n) :=
  (soloLTS cfg p).MTr s (List.replicate m (.instruction p)) t

theorem Steps.comp {cfg : Config n} {p : Proc n} {s t u : State n} {a b : Nat}
    (x : Steps cfg p s a t) (y : Steps cfg p t b u) : Steps cfg p s (a + b) u := by
  unfold Steps
  rw [List.replicate_add]
  exact Cslib.LTS.MTr.comp _ x y

theorem edge {cfg : Config n} {p : Proc n} {l l' : Local n} {a : Label n}
    (step : ordinary cfg p (state p l) = some l')
    (lab : label (state p l) (.run p) = a) (pre : l.pc ≠ .cs) :
    (soloLTS cfg p).Tr (state p l) a (state p l') := by
  exact ⟨by simp [next, step], lab, by simpa using pre⟩

/-- Includes every read, including dummy leaves, and the empty-suffix return. -/
theorem scan_path (cfg : Config n) (p : Proc n) (c : Continuation) (k : Nat)
    (positive : 0 < k) (xs : List (Leaf n))
    (other : ∀ j ∈ xs, j.val ≠ p.val) (q : Value) :
    Steps cfg p (state p ⟨.scan c k xs, q⟩) (xs.length + 1)
      (state p ⟨resume cfg p c k dead, q⟩) := by
  induction xs with
  | nil =>
    apply Cslib.LTS.MTr.single
    apply edge <;> simp [ordinary, label]
  | cons j xs ih =>
    have read := read_dead p ⟨.scan c k (j :: xs), q⟩ j (other j (by simp))
    have step : (soloLTS cfg p).Tr
        (state p ⟨.scan c k (j :: xs), q⟩) (.instruction p)
        (state p ⟨.scan c k xs, q⟩) := by
      apply edge
      · simp [ordinary, read, dead, ScanBridge.dead, show ¬ k ≤ 0 by omega]
      · simp [label]
      · simp
    simpa only [Steps, List.length_cons, List.replicate_succ] using
      Cslib.LTS.MTr.stepL step (ih (by intro j hj; exact other j (by simp [hj])))

theorem order_other (cfg : Config n) (p : Proc n) (k : Nat) :
    ∀ j ∈ cfg.order p k, j.val ≠ p.val := by
  intro j hj eq
  have h := ((cfg.complete p k j).mp hj).2
  exact h (by rw [eq])

/-- Three complete scans, two writes, one own read, and pass. -/
theorem level_path (cfg : Config n) (p : Proc n) (k : Nat) (positive : 0 < k)
    (q : Value) :
    Steps cfg p (state p ⟨scan cfg p .first k, q⟩)
      (3 * (cfg.order p k).length + 7)
      (state p ⟨if k < height n then scan cfg p .first (k + 1) else .enter,
        ⟨k, true⟩⟩) := by
  let v : Value := ⟨k, true⟩
  have first := scan_path cfg p .first k positive (cfg.order p k) (order_other cfg p k) q
  have second := scan_path cfg p .second k positive (cfg.order p k) (order_other cfg p k) v
  have wait := scan_path cfg p .wait k positive (cfg.order p k) (order_other cfg p k) v
  simp only [resume, dead, ScanBridge.dead, show (0 : Nat) ≠ k by omega,
    show ¬ k < 0 by omega, show 0 < k from positive, ite_false, ite_true] at first second wait
  have write1 : Steps cfg p (state p ⟨.write1 k v, q⟩) 1
      (state p ⟨scan cfg p .second k, v⟩) := by
    apply Cslib.LTS.MTr.single
    apply edge <;> simp [ordinary, label]
  have self2 : Steps cfg p (state p ⟨.self2 k, v⟩) 1
      (state p ⟨.write2 k v, v⟩) := by
    apply Cslib.LTS.MTr.single
    apply edge <;> simp [ordinary, label]
  have write2 : Steps cfg p (state p ⟨.write2 k v, v⟩) 1
      (state p ⟨scan cfg p .wait k, v⟩) := by
    apply Cslib.LTS.MTr.single
    apply edge <;> simp [ordinary, label]
  have pass : Steps cfg p (state p ⟨.pass k, v⟩) 1
      (state p ⟨if k < height n then scan cfg p .first (k + 1) else .enter, v⟩) := by
    apply Cslib.LTS.MTr.single
    apply edge <;> simp [ordinary, label]
  convert (((((first.comp write1).comp second).comp self2).comp write2).comp wait).comp pass using 1 <;>
    simp [scan]
  omega

/-- Work performed at positive levels 1 through k. -/
def work (cfg : Config n) (p : Proc n) : Nat → Nat
  | 0 => 0
  | k + 1 => work cfg p k + 3 * (cfg.order p (k + 1)).length + 7

def boundary (cfg : Config n) (p : Proc n) (k : Nat) : Local n :=
  ⟨if k < height n then scan cfg p .first (k + 1) else .enter,
    if k = 0 then dead else ⟨k, true⟩⟩

theorem climb_path (cfg : Config n) (p : Proc n) (k : Nat) (bound : k ≤ height n) :
    Steps cfg p (state p (boundary cfg p 0)) (work cfg p k)
      (state p (boundary cfg p k)) := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
    have earlier := ih (by omega)
    have one := level_path cfg p (k + 1) (by omega) (boundary cfg p k).q
    have same : scan cfg p .first (k + 1) = (boundary cfg p k).pc := by
      simp [boundary, show k < height n by omega]
    rw [same] at one
    have composed := earlier.comp one
    simpa [boundary, work, Nat.add_assoc] using composed

/-- The actual request, every level instruction, and actual entry. -/
theorem initialized_path (cfg : Config n) (p : Proc n) :
    (soloLTS cfg p).MTr (initial n)
      (.request p :: (List.replicate (work cfg p (height n)) (.instruction p) ++ [.entry p]))
      (state p { boundary cfg p (height n) with pc := .cs }) := by
  have request : (soloLTS cfg p).Tr (initial n) (.request p)
      (state p (boundary cfg p 0)) := by
    rw [← state_idle p]
    apply edge
    · by_cases h : height n = 0
      · simp [ordinary, boundary, h]
      · simp [ordinary, boundary, h, show 0 < height n by omega]
    · simp [label]
    · simp
  have enter : (soloLTS cfg p).Tr (state p (boundary cfg p (height n))) (.entry p)
      (state p { boundary cfg p (height n) with pc := .cs }) := by
    apply edge <;> simp [ordinary, label, boundary]
  exact .stepL request ((climb_path cfg p (height n) (by rfl)).stepR _ enter)

/-- Deterministic iteration of the selected command. The default is only to
make the function total; `path_execution` proves every counted call succeeds. -/
def execute (cfg : Config n) (p : Proc n) (s : State n) : Nat → State n
  | 0 => s
  | i + 1 => (next cfg (execute cfg p s i) (.run p)).getD (execute cfg p s i)

theorem execute_shift (cfg : Config n) (p : Proc n) (s t : State n)
    (step : next cfg s (.run p) = some t) (i : Nat) :
    execute cfg p s (i + 1) = execute cfg p t i := by
  induction i with
  | zero => simp [execute, step]
  | succ i ih => rw [execute, ih, execute]

/-- Convert the actual finite command path to consecutive time-indexed states.
Each listed label is computed by the interpreter at that exact pre-state. -/
theorem path_execution {cfg : Config n} {p : Proc n} {s t : State n}
    {labels : List (Label n)} (path : (soloLTS cfg p).MTr s labels t) :
    execute cfg p s labels.length = t ∧
      ∀ i (hi : i < labels.length),
        next cfg (execute cfg p s i) (.run p) = some (execute cfg p s (i + 1)) ∧
        label (execute cfg p s i) (.run p) = labels[i] ∧
        (execute cfg p s i p).pc ≠ .cs := by
  induction path with
  | refl => simp [execute]
  | @stepL s a u labels t step rest ih =>
    have shift := execute_shift cfg p s u step.1
    constructor
    · simpa only [List.length_cons, shift] using ih.1
    · intro i hi
      cases i with
      | zero => simpa [execute, step.1] using step.2
      | succ i =>
        have old := ih.2 i (by simpa using hi)
        simpa only [shift, List.getElem_cons_succ] using old

/-- The restricted path forgets directly to the original labelled interpreter. -/
theorem path_lts {cfg : Config n} {p : Proc n} {s t : State n}
    {labels : List (Label n)} (path : (soloLTS cfg p).MTr s labels t) :
    (lts cfg).MTr s labels t := by
  induction path with
  | refl => exact .refl
  | stepL step _ ih => exact .stepL ⟨.run p, step.1, step.2.1⟩ ih

/-- Any other execution of the same successful commands has the same states. -/
theorem execute_unique (cfg : Config n) (p : Proc n) (s : State n)
    (trace : Nat → State n) (start : trace 0 = s) (steps : Nat)
    (valid : ∀ i < steps, next cfg (trace i) (.run p) = some (trace (i + 1))) :
    ∀ i ≤ steps, trace i = execute cfg p s i := by
  intro i hi
  induction i with
  | zero => exact start
  | succ i ih =>
    have prev := ih (by omega)
    simp only [execute, ← prev, valid i (by omega), Option.getD_some]

/-- No peer is scheduled, so its entire initialized state persists. -/
theorem execute_peer (cfg : Config n) (p q : Proc n) (different : q ≠ p) (i : Nat) :
    execute cfg p (initial n) i q = ⟨.idle, dead⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [execute]
    cases h : ordinary cfg p (execute cfg p (initial n) i) <;>
      simp [next, h, setLocal, different, ih]

end EconomicalSolutions.Algorithm2.Solo

#print axioms EconomicalSolutions.Algorithm2.Solo.scan_path
#print axioms EconomicalSolutions.Algorithm2.Solo.level_path
#print axioms EconomicalSolutions.Algorithm2.Solo.initialized_path
#print axioms EconomicalSolutions.Algorithm2.Solo.path_execution
#print axioms EconomicalSolutions.Algorithm2.Solo.path_lts
#print axioms EconomicalSolutions.Algorithm2.Solo.execute_unique
#print axioms EconomicalSolutions.Algorithm2.Solo.execute_peer
