module

public import Peterson.EconomicalSolutions.Algorithm2Tree

@[expose] public section

namespace EconomicalSolutions.Algorithm2

def scanPC : Continuation → Node.PC
  | .first => .read1
  | .second => .read2
  | .wait => .waitPeer

/-- Concrete continuation before any speculative historical scan observation.
The first branch keeps every passed lower node through all higher operations. -/
def basePC {n : Nat} (k : Nat) (l : Local n) : Node.PC :=
  if k ≤ passedLevel l then .held else
    match l.pc with
    | .scan c _ _ => scanPC c
    | .write1 _ v => .write1 (Node.projectValue k v)
    | .self2 _ => .self2
    | .write2 _ v => .write2 (Node.projectValue k v)
    | .waitSelf _ v => .waitSelf (Node.projectValue k v)
    | _ => .read1

/-- A current concrete scan admits either its unsampled continuation or any
continuation backed by a historical observation in that very invocation. -/
def LocalPC {n : Nat} (cfg : Config n) (trace : Nat → State n)
    (commands : Nat → Command n) (p : Proc n) (k time : Nat) (pc : Node.PC) : Prop :=
  pc = basePC k (trace time p) ∨
    ∃ c remaining v, (trace time p).pc = .scan c k remaining ∧
      ObservationSupport cfg trace commands p c k time v ∧ pc = Node.sampled (bit p.val k) c v

def RolePC {n : Nat} (cfg : Config n) (trace : Nat → State n)
    (commands : Nat → Command n) (node k time : Nat) (role : Bool) (pc : Node.PC) : Prop :=
  match owner (trace time) node k role with
  | none => pc = .read1
  | some p => LocalPC cfg trace commands p k time pc

/-- Every independent pair of supported continuations is a real node-reachable
state. This product property lets each returning scan choose its own historical
sample without invalidating the other role's still-open choices. -/
def ProductReachable {n : Nat} (cfg : Config n) (trace : Nat → State n)
    (commands : Nat → Command n) (node k time : Nat) : Prop :=
  ∀ pc0 pc1, RolePC cfg trace commands node k time false pc0 →
    RolePC cfg trace commands node k time true pc1 →
    Node.Reachable ⟨⟨pc0, roleValue (trace time) node k false⟩,
      ⟨pc1, roleValue (trace time) node k true⟩⟩

theorem basePC_scan {n : Nat} {l : Local n} {k : Nat} {c : Continuation}
    {remaining : List (Leaf n)} (positive : 0 < k) (pc : l.pc = .scan c k remaining) :
    basePC k l = scanPC c := by
  simp [basePC, passedLevel, pc, show ¬ k ≤ k - 1 by omega]

theorem localPC_held {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {p : Proc n} {k time : Nat}
    (held : k ≤ passedLevel (trace time p)) :
    LocalPC cfg trace commands p k time .held := Or.inl (by simp [basePC, held])

theorem localPC_base {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} (p : Proc n) (k time : Nat) :
    LocalPC cfg trace commands p k time (basePC k (trace time p)) := Or.inl rfl

theorem rolePC_owner {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {node k time : Nat} {role : Bool} {p : Proc n} {pc : Node.PC}
    (selected : owner (trace time) node k role = some p)
    (localPC : LocalPC cfg trace commands p k time pc) :
    RolePC cfg trace commands node k time role pc := by
  simpa [RolePC, selected] using localPC

def SampleExtension (role : Bool) (peer : Node.Value) (choices : Node.PC → Prop)
    (pc : Node.PC) : Prop :=
  choices pc ∨ ∃ c, choices (scanPC c) ∧ pc = Node.sampled role c peer

/-- Sampling changes private control only. Hence independent choices of
observation at the same boundary can be placed in either role order. -/
theorem product_sample_extension (q0 q1 : Node.Value) (choices0 choices1 : Node.PC → Prop)
    (reachable : ∀ a b, choices0 a → choices1 b → Node.Reachable ⟨⟨a, q0⟩, ⟨b, q1⟩⟩)
    (a b : Node.PC) (ha : SampleExtension false q1 choices0 a)
    (hb : SampleExtension true q0 choices1 b) :
    Node.Reachable ⟨⟨a, q0⟩, ⟨b, q1⟩⟩ := by
  rcases ha with ha | ⟨c, ha, rfl⟩ <;> rcases hb with hb | ⟨d, hb, rfl⟩
  · exact reachable a b ha hb
  · have h := Node.Reachable.step (.run true) (reachable a (scanPC d) ha hb)
    cases d <;> simpa [Node.next, Node.State.local, Node.State.setLocal, Node.ordinary, scanPC] using h
  · have h := Node.Reachable.step (.run false) (reachable (scanPC c) b ha hb)
    cases c <;> simpa [Node.next, Node.State.local, Node.State.setLocal, Node.ordinary, scanPC] using h
  · have h := Node.Reachable.step (.run true)
      (Node.Reachable.step (.run false) (reachable (scanPC c) (scanPC d) ha hb))
    cases c <;> cases d <;>
      simpa [Node.next, Node.State.local, Node.State.setLocal, Node.ordinary, scanPC] using h

/-- Candidate continuations immediately after the concrete step, before adding
new observations at the next boundary. Old samples must survive that step. -/
def PriorLocalPC {n : Nat} (cfg : Config n) (trace : Nat → State n)
    (commands : Nat → Command n) (p : Proc n) (k time : Nat) (pc : Node.PC) : Prop :=
  pc = basePC k (trace (time + 1) p) ∨
    ∃ c remaining v, (trace (time + 1) p).pc = .scan c k remaining ∧
      ObservationSupport cfg trace commands p c k time v ∧
      scanReturn (trace time) (commands time) p = none ∧ commands time ≠ .fail p ∧
      pc = Node.sampled (bit p.val k) c v

def PriorRolePC {n : Nat} (cfg : Config n) (trace : Nat → State n)
    (commands : Nat → Command n) (node k time : Nat) (role : Bool) (pc : Node.PC) : Prop :=
  match owner (trace (time + 1)) node k role with
  | none => pc = .read1
  | some p => PriorLocalPC cfg trace commands p k time pc

theorem rolePC_sample_extension {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {node k time : Nat} {role : Bool} {pc : Node.PC}
    (positive : 0 < k) (wf : WellFormed (trace (time + 1)))
    (unique : TreeUnique (k - 1) (trace (time + 1)))
    (choice : RolePC cfg trace commands node k (time + 1) role pc) :
    SampleExtension role (roleValue (trace (time + 1)) node k (!role))
      (PriorRolePC cfg trace commands node k time role) pc := by
  unfold RolePC at choice
  cases selected : owner (trace (time + 1)) node k role with
  | none =>
    left
    simpa [PriorRolePC, selected] using choice
  | some p =>
    simp only [selected] at choice
    have qualified := owner_some selected
    have roleEq := ((child_iff node k p.val role positive).mp qualified.1).2
    rcases choice with base | ⟨c, rest, v, current, supported, continuation⟩
    · left
      simp only [PriorRolePC, selected]
      exact Or.inl base
    · rcases support_succ_cases supported with ⟨old, nr, nf⟩ | ⟨rest', x, _, seen, projected⟩
      · left
        simp only [PriorRolePC, selected]
        exact Or.inr ⟨c, rest, v, current, old, nr, nf, continuation⟩
      · right
        refine ⟨c, ?_, ?_⟩
        · simp only [PriorRolePC, selected]
          exact Or.inl (basePC_scan positive current).symm
        · have value := observation_roleValue positive wf unique qualified.1 seen
          rw [projected] at value
          simpa [roleEq, value] using continuation

theorem initial_rolePC {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {node k : Nat} {role : Bool} {pc : Node.PC}
    (positive : 0 < k) (start : trace 0 = initial n)
    (choice : RolePC cfg trace commands node k 0 role pc) : pc = .read1 := by
  unfold RolePC at choice
  cases selected : owner (trace 0) node k role with
  | none => simpa [selected] using choice
  | some p =>
    simp only [selected, LocalPC] at choice
    rcases choice with base | ⟨_, _, _, impossible, _⟩
    · simpa [start, initial, basePC, passedLevel, Nat.not_le_of_gt positive] using base
    · simp [start, initial] at impossible

theorem initial_roleValue {n : Nat} (node k : Nat) (role : Bool) (positive : 0 < k) :
    roleValue (initial n) node k role = .O := by
  unfold roleValue
  cases owner (initial n) node k role <;>
    simp [initial, Node.projectValue, dead, ScanBridge.dead, positive]

theorem product_initial {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} (node k : Nat) (positive : 0 < k)
    (start : trace 0 = initial n) : ProductReachable cfg trace commands node k 0 := by
  intro a b ha hb
  have aEq := initial_rolePC positive start ha
  have bEq := initial_rolePC positive start hb
  rw [aEq, bEq, start, initial_roleValue node k false positive, initial_roleValue node k true positive]
  exact .initial

inductive LocalAction where
  | stay | run | reset
  deriving DecidableEq

def LocalAction.effect (action : LocalAction) (role : Bool) (peer : Node.Value)
    (l : Node.Local) : Node.Local :=
  match action with
  | .stay => l
  | .run => Node.ordinary role l peer
  | .reset => ⟨.read1, .O⟩

def ordinaryAction {n : Nat} (k : Nat) (l : Local n) : LocalAction :=
  if k - 1 ≤ passedLevel l then
    match l.pc with
    | .write1 _ _ | .write2 _ _ => .run
    | .self2 m | .waitSelf m _ => if m = k then .run else .stay
    | .release => .reset
    | _ => .stay
  else .stay

def viewPC {n : Nat} (k : Nat) (l : Local n) : Node.PC :=
  if k - 1 ≤ passedLevel l then basePC k l else .read1

def viewBase {n : Nat} (k : Nat) (l : Local n) : Node.Local :=
  ⟨viewPC k l, Node.projectValue k l.q⟩

def ViewPC {n : Nat} (cfg : Config n) (trace : Nat → State n)
    (commands : Nat → Command n) (p : Proc n) (k time : Nat) (pc : Node.PC) : Prop :=
  if k - 1 ≤ passedLevel (trace time p) then LocalPC cfg trace commands p k time pc else pc = .read1

theorem viewPC_base {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} (p : Proc n) (k time : Nat) :
    ViewPC cfg trace commands p k time (viewPC k (trace time p)) := by
  unfold ViewPC viewPC
  split
  · exact localPC_base p k time
  · rfl

theorem viewPC_resume {n : Nat} (cfg : Config n) (p : Proc n) (c : Continuation)
    (k : Nat) (q x : Value) (positive : 0 < k) :
    viewPC k (⟨resume cfg p c k x, q⟩ : Local n) = Node.sampled (bit p.val k) c (Node.projectValue k x) := by
  rw [← Node.resume_projection cfg p c k x]
  have notHeld : ¬ k ≤ k - 1 := by omega
  cases c <;> simp only [resume]
  · simp [viewPC, basePC, passedLevel, Node.projectPC, notHeld]
  · split <;> simp [viewPC, basePC, passedLevel, Node.projectPC, notHeld]
  · split
    · simp [viewPC, basePC, passedLevel, Node.projectPC, scanPC, scan, notHeld]
    · split <;> simp [viewPC, basePC, passedLevel, Node.projectPC, notHeld]

theorem viewPC_resume_other {n : Nat} (cfg : Config n) (p : Proc n) (c : Continuation)
    (k m : Nat) (q x : Value) (positive : 0 < k) (levelPositive : 0 < m) (different : m ≠ k) :
    viewPC k (⟨resume cfg p c m x, q⟩ : Local n) =
      viewPC k (⟨.scan c m [], q⟩ : Local n) := by
  by_cases above : k < m
  · have held : k ≤ m - 1 := by omega
    have qualified : k - 1 ≤ m - 1 := by omega
    have passed : k ≤ m := by omega
    cases c <;> simp only [resume]
    · simp [viewPC, basePC, passedLevel, held, qualified]
    · split <;> simp [viewPC, basePC, passedLevel, held, qualified]
    · split
      · simp [viewPC, basePC, passedLevel, scan, held, qualified]
      · split <;> simp [viewPC, basePC, passedLevel, held, qualified, passed]; omega
  · have below : m < k := by omega
    have notHeld : ¬ k ≤ m := by omega
    have notQualified : ¬ k - 1 ≤ m - 1 := by omega
    cases c <;> simp only [resume]
    · simp [viewPC, passedLevel, notQualified]
    · split <;> simp [viewPC, passedLevel, notQualified]
    · split
      · simp [viewPC, passedLevel, scan, notQualified]
      · split <;> simp [viewPC, basePC, passedLevel, notQualified, notHeld]


/-- Every ordinary concrete instruction either has its direct local node
step, or returns the sample whose node step already occurred historically. -/
theorem ordinary_projection {n : Nat} (cfg : Config n) (p : Proc n) (s : State n)
    (l : Local n) (k : Nat) (peer : Node.Value) (positive : 0 < k) (within : k ≤ height n)
    (wf : LocalWF (s p)) (step : ordinary cfg p s = some l) :
    LocalAction.effect (ordinaryAction k (s p)) (bit p.val k) peer (viewBase k (s p)) = viewBase k l ∨
    ∃ c remaining x, (s p).pc = .scan c k remaining ∧ scanReturn s (.run p) p = some x ∧
      ordinaryAction k (s p) = .stay ∧
      viewBase k l = ⟨Node.sampled (bit p.val k) c (Node.projectValue k x), Node.projectValue k (s p).q⟩ := by
  have stage := wf.2.2
  have resume_case (c : Continuation) (m : Nat) (rest : List (Leaf n)) (x : Value)
      (pc : (s p).pc = .scan c m rest)
      (ret : scanReturn s (.run p) p = some x)
      (after : l = ⟨resume cfg p c m x, (s p).q⟩) :
      LocalAction.effect (ordinaryAction k (s p)) (bit p.val k) peer (viewBase k (s p)) = viewBase k l ∨
      ∃ c remaining x, (s p).pc = .scan c k remaining ∧ scanReturn s (.run p) p = some x ∧
        ordinaryAction k (s p) = .stay ∧
        viewBase k l = ⟨Node.sampled (bit p.val k) c (Node.projectValue k x), Node.projectValue k (s p).q⟩ := by
    have pos : 0 < m := by cases c <;> simp only [StageWF, pc] at stage <;> exact stage.1
    have action : ordinaryAction k (s p) = .stay := by simp [ordinaryAction, pc]
    by_cases eq : m = k
    · subst m
      right
      exact ⟨c, rest, x, pc, ret, action, by simp [after, viewBase, viewPC_resume cfg p c k _ x positive]⟩
    · left
      rw [action]
      simp only [LocalAction.effect, after, viewBase]
      congr 1
      have h := viewPC_resume_other cfg p c k m (s p).q x positive pos eq
      convert h.symm using 1; simp [viewPC, basePC, passedLevel, pc]; rfl
  cases pc : (s p).pc with
  | down => simp [ordinary, pc] at step
  | scan c m rest =>
    cases rest with
    | nil =>
      simp only [ordinary, pc, Option.some.injEq] at step
      simpa only [pc] using resume_case c m [] dead pc (by simp [scanReturn, pc]) step.symm
    | cons j rest =>
      by_cases high : m ≤ (visible s j).level
      · simp only [ordinary, pc, high, ite_true, Option.some.injEq] at step
        simpa only [pc] using resume_case c m (j :: rest) (visible s j) pc (by simp [scanReturn, pc, high]) step.symm
      · simp only [ordinary, pc, high, ite_false, Option.some.injEq] at step
        subst l
        left
        simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, LocalAction.effect]; rfl
  | idle =>
    have hpos : height n ≠ 0 := by omega
    simp only [ordinary, pc, hpos, ite_false, Option.some.injEq] at step
    subst l
    left
    simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, LocalAction.effect, scan, scanPC,
      Nat.not_le_of_gt positive]
  | write1 m v =>
    have st : 0 < m ∧ m ≤ height n ∧ (s p).q.level + 1 = m ∧ v.level = m := by
      simpa [StageWF, pc] using stage
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    left
    rcases Nat.lt_trichotomy m k with low | eq | high
    · have nq : ¬ k - 1 ≤ m - 1 := by omega
      have qlow : (s p).q.level < k := by omega
      simp [ordinaryAction, viewBase, viewPC, passedLevel, pc, nq, LocalAction.effect, scan,
        Node.projectValue, qlow, st.2.2.2, low]
    · subst m
      have nh : ¬ k ≤ k - 1 := by omega
      simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, nh, LocalAction.effect,
        Node.ordinary, scan, scanPC]
    · have held : k ≤ m - 1 := by omega
      have qual : k - 1 ≤ m - 1 := by omega
      simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, held, qual, LocalAction.effect,
        Node.ordinary, scan, Node.projectValue, st.2.2.2, high, show ¬ m < k by omega]
  | write2 m v =>
    have st : 0 < m ∧ m ≤ height n ∧ (s p).q.level = m ∧ v.level = m := by
      simpa [StageWF, pc] using stage
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    left
    rcases Nat.lt_trichotomy m k with low | eq | high
    · have nq : ¬ k - 1 ≤ m - 1 := by omega
      simp [ordinaryAction, viewBase, viewPC, passedLevel, pc, nq, LocalAction.effect, scan,
        Node.projectValue, st.2.2.1, st.2.2.2, low]
    · subst m
      have nh : ¬ k ≤ k - 1 := by omega
      simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, nh, LocalAction.effect,
        Node.ordinary, scan, scanPC]
    · have held : k ≤ m - 1 := by omega
      have qual : k - 1 ≤ m - 1 := by omega
      simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, held, qual, LocalAction.effect,
        Node.ordinary, scan, Node.projectValue, st.2.2.2, high, show ¬ m < k by omega]
  | self2 m =>
    have st : 0 < m ∧ m ≤ height n ∧ (s p).q.level = m := by
      simpa [StageWF, pc] using stage
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    left
    rcases Nat.lt_trichotomy m k with low | eq | high
    · have nq : ¬ k - 1 ≤ m - 1 := by omega
      simp [ordinaryAction, viewBase, viewPC, passedLevel, pc, nq, LocalAction.effect]
    · subst m
      have nh : ¬ k ≤ k - 1 := by omega
      simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, nh, LocalAction.effect, Node.ordinary]
    · have held : k ≤ m - 1 := by omega
      have qual : k - 1 ≤ m - 1 := by omega
      simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, held, qual, LocalAction.effect,
        show m ≠ k by omega]
  | waitSelf m x =>
    have st : 0 < m ∧ m ≤ height n ∧ (s p).q.level = m ∧ x.level = m := by
      simpa [StageWF, pc] using stage
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    left
    rcases Nat.lt_trichotomy m k with low | eq | high
    · have nq : ¬ k - 1 ≤ m - 1 := by omega
      have nh : ¬ k ≤ m := by omega
      by_cases waiting : (Bool.xor (bit p.val m) (x == (s p).q)) = true <;>
        simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, nq, nh, LocalAction.effect,
          waiting, scan]
    · subst m
      have nh : ¬ k ≤ k - 1 := by omega
      have qual : k - 1 ≤ k := by omega
      have same := Node.waitSelf_projection (bit p.val k) k x (s p).q st.2.2.2 st.2.2.1
      by_cases waiting : (Bool.xor (bit p.val k) (x == (s p).q)) = true
      · have abstractWait : ¬ ((Node.projectValue k x == Node.projectValue k (s p).q) == bit p.val k) = true := by
          intro h
          have := same.mpr h
          rw [waiting] at this
          contradiction
        simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, nh, LocalAction.effect,
          waiting, abstractWait, scan, scanPC, Node.ordinary]
      · have abstractPass := same.mp (Bool.eq_false_iff.mpr waiting)
        simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, nh, qual, LocalAction.effect,
          waiting, abstractPass, Node.ordinary]
    · have held : k ≤ m - 1 := by omega
      have qual : k - 1 ≤ m - 1 := by omega
      have held' : k ≤ m := by omega
      have qual' : k - 1 ≤ m := by omega
      by_cases waiting : (Bool.xor (bit p.val m) (x == (s p).q)) = true <;>
        simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, held, qual, held', qual',
          LocalAction.effect, waiting, scan, show m ≠ k by omega]
  | pass m =>
    have st : 0 < m ∧ m ≤ height n ∧ (s p).q.level = m := by
      simpa [StageWF, pc] using stage
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    left
    by_cases more : m < height n
    · simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, LocalAction.effect, more, scan, scanPC]
    · have eq : m = height n := by omega
      simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, LocalAction.effect, eq,
        within, show k - 1 ≤ height n by omega]
  | enter =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    left
    simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, LocalAction.effect]; rfl
  | cs =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    left
    simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, LocalAction.effect]; rfl
  | release =>
    simp only [ordinary, pc, Option.some.injEq] at step
    subst l
    left
    simp [ordinaryAction, viewBase, viewPC, basePC, passedLevel, pc, LocalAction.effect,
      show k - 1 ≤ height n by omega, Nat.not_le_of_gt positive, Node.projectValue, dead, ScanBridge.dead, positive]

def commandAction {n : Nat} (s : State n) (command : Command n) (p : Proc n) (k : Nat) : LocalAction :=
  match command with
  | .run actor => if actor = p then ordinaryAction k (s p) else .stay
  | .fail actor => if actor = p ∧ k - 1 ≤ passedLevel (s p) then .reset else .stay
  | _ => .stay

def PriorViewPC {n : Nat} (cfg : Config n) (trace : Nat → State n)
    (commands : Nat → Command n) (p : Proc n) (k time : Nat) (pc : Node.PC) : Prop :=
  if k - 1 ≤ passedLevel (trace (time + 1) p) then PriorLocalPC cfg trace commands p k time pc
  else pc = .read1

theorem viewBase_unqualified {n : Nat} {l : Local n} {k : Nat} (wf : LocalWF l)
    (unqualified : ¬ k - 1 ≤ passedLevel l) : viewBase k l = ⟨.read1, .O⟩ := by
  have low : l.q.level < k := by have := (localWF_levels wf).2; omega
  simp [viewBase, viewPC, unqualified, Node.projectValue, low]

theorem priorView_cases {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {p : Proc n} {k time : Nat} {pc : Node.PC}
    (h : PriorViewPC cfg trace commands p k time pc) :
    pc = viewPC k (trace (time + 1) p) ∨
      ∃ c rest v, (trace (time + 1) p).pc = .scan c k rest ∧
        ObservationSupport cfg trace commands p c k time v ∧
        scanReturn (trace time) (commands time) p = none ∧ commands time ≠ .fail p ∧
        pc = Node.sampled (bit p.val k) c v := by
  unfold PriorViewPC at h
  split at h
  · rename_i qual
    rcases h with base | other
    · exact Or.inl (by simpa [viewPC, qual] using base)
    · exact Or.inr other
  · rename_i nq
    exact Or.inl (by simpa [viewPC, nq] using h)

theorem current_scan_qualified {n : Nat} {l : Local n} {k : Nat} {c : Continuation}
    {rest : List (Leaf n)} (pc : l.pc = .scan c k rest) : k - 1 ≤ passedLevel l := by
  simp [passedLevel, pc]

/-- Lift the pure instruction correspondence to real historical choices.
The return branch obtains its supporting observation from the actual initial
execution; no support or abstract-trace witness is supplied by the caller. -/
theorem concrete_view_projection {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {time : Nat}
    (initially : trace 0 = initial n) (valid : ValidPrefix cfg trace commands (time + 1))
    (k : Nat) (positive : 0 < k) (within : k ≤ height n)
    (lower : ∀ t, t ≤ time → TreeUnique (k - 1) (trace t))
    (p : Proc n) (peer : Node.Value) (pc : Node.PC)
    (choice : PriorViewPC cfg trace commands p k time pc) :
    ∃ before, ViewPC cfg trace commands p k time before ∧
      LocalAction.effect (commandAction (trace time) (commands time) p k) (bit p.val k) peer
        ⟨before, Node.projectValue k (trace time p).q⟩ =
          ⟨pc, Node.projectValue k (trace (time + 1) p).q⟩ := by
  have wf : WellFormed (trace time) := reachable_wellFormed (prefix_reachable initially valid time (by omega))
  have step := valid time (by omega)
  rcases priorView_cases choice with base | ⟨c, rest, v, _, support, nr, nf, pcEq⟩
  · subst pc
    cases cmd : commands time with
    | stutter =>
      have same : trace (time + 1) = trace time := Option.some.inj (by simpa [cmd, next] using step.symm)
      refine ⟨viewPC k (trace time p), viewPC_base p k time, ?_⟩
      simp [commandAction, LocalAction.effect, same]
    | run actor =>
      by_cases own : actor = p
      · subst actor
        have run : ordinary cfg p (trace time) = some (trace (time + 1) p) := by
          simp only [cmd, next] at step
          cases h : ordinary cfg p (trace time) with
          | none => simp [h] at step
          | some l =>
            have same : trace (time + 1) = setLocal (trace time) p l := by simpa [h] using step.symm
            simp [same, setLocal]
        rcases ordinary_projection cfg p (trace time) (trace (time + 1) p) k peer positive within (wf p) run with normal | returned
        · exact ⟨viewPC k (trace time p), viewPC_base p k time, by simpa [cmd, commandAction, viewBase] using normal⟩
        · obtain ⟨c, rest, x, beforePC, ret, action, after⟩ := returned
          have supported := concrete_return_supported initially valid p c k rest beforePC x (by simpa [cmd] using ret)
            (fun t ht => scan_unique_of_treeUnique k positive
              (reachable_wellFormed (prefix_reachable initially valid t (by omega))) (lower t ht) p)
          refine ⟨Node.sampled (bit p.val k) c (Node.projectValue k x), ?_, ?_⟩
          · simp only [ViewPC, current_scan_qualified beforePC, ite_true]
            exact Or.inr ⟨c, rest, _, beforePC, supported, rfl⟩
          · simpa [cmd, commandAction, action, LocalAction.effect, viewBase] using after.symm
      · have same : trace (time + 1) p = trace time p :=
          next_other_local p step (by simp [cmd, own]) (by simp [cmd]) (by simp [cmd])
        exact ⟨viewPC k (trace time p), viewPC_base p k time,
          by simp [commandAction, own, LocalAction.effect, same]⟩
    | fail actor =>
      by_cases own : actor = p
      · subst actor
        have same : trace (time + 1) p = ⟨.down, dead⟩ := by
          simp only [cmd, next] at step
          split at step
          · simp at step
          · simp [← Option.some.inj step, setLocal]
        refine ⟨viewPC k (trace time p), viewPC_base p k time, ?_⟩
        by_cases qual : k - 1 ≤ passedLevel (trace time p)
        · simp only [commandAction, eq_self, true_and, qual, ite_true, LocalAction.effect]
          simp [same, viewPC, basePC, passedLevel, Nat.not_le_of_gt positive, Node.projectValue, dead, ScanBridge.dead, positive]
        · have before := viewBase_unqualified (wf p) qual
          simp only [commandAction, eq_self, true_and, qual, ite_false, LocalAction.effect]
          change viewBase k (trace time p) = _
          rw [before]
          simp [same, viewPC, basePC, passedLevel, Nat.not_le_of_gt positive, Node.projectValue, dead, ScanBridge.dead, positive]
      · have same : trace (time + 1) p = trace time p :=
          next_other_local p step (by simp [cmd]) (by simp [cmd, own]) (by simp [cmd])
        exact ⟨viewPC k (trace time p), viewPC_base p k time,
          by simp [commandAction, own, LocalAction.effect, same]⟩
    | restart actor =>
      by_cases own : actor = p
      · subst actor
        have before : (trace time p).pc = .down := by
          simp only [cmd, next] at step
          split at step
          · assumption
          · simp at step
        have same : trace (time + 1) p = ⟨.idle, dead⟩ := by
          simpa [cmd, next, before, setLocal, funext_iff] using (congrArg (fun o => o.map (fun s => s p)) step).symm
        have deadBefore : (trace time p).q = dead := by simpa [StageWF, before] using (wf p).2.2
        exact ⟨viewPC k (trace time p), viewPC_base p k time, by
          simp [commandAction, LocalAction.effect, same, before, deadBefore, viewPC, basePC, passedLevel,
            Nat.not_le_of_gt positive]⟩
      · have same : trace (time + 1) p = trace time p :=
          next_other_local p step (by simp [cmd]) (by simp [cmd]) (by simp [cmd, own])
        exact ⟨viewPC k (trace time p), viewPC_base p k time,
          by simp [commandAction, LocalAction.effect, same]⟩
  · obtain ⟨beforeRest, beforePC⟩ := support_control (fun t ht => valid t (by omega)) support
    have same := (open_scan_step step beforePC nr nf).2
    have action : commandAction (trace time) (commands time) p k = .stay := by
      cases cmd : commands time with
      | run actor => by_cases own : actor = p <;> simp [commandAction, own, ordinaryAction, beforePC]
      | fail actor =>
        have ne : actor ≠ p := by intro eq; subst actor; simp [cmd] at nf
        simp [commandAction, ne]
      | restart | stutter => rfl
    refine ⟨pc, ?_, ?_⟩
    · simp only [ViewPC, current_scan_qualified beforePC, ite_true]
      exact Or.inr ⟨c, beforeRest, v, beforePC, support, pcEq⟩
    · simp [action, LocalAction.effect, same]

theorem owner_no_swap {n : Nat} {cfg : Config n} {s t : State n} {command : Command n}
    {node k : Nat} {role : Bool} {p q : Proc n}
    (beforeUnique : TreeUnique (k - 1) s) (afterUnique : TreeUnique (k - 1) t)
    (step : next cfg s command = some t)
    (before : owner s node k role = some p) (after : owner t node k role = some q) : p = q := by
  have hp := owner_some before
  have hq := owner_some after
  obtain same | ⟨actor, replacement, rfl⟩ := next_locality step
  · subst t; exact qualified_unique beforeUnique hp hq
  · by_cases pActor : p = actor
    · by_cases qActor : q = actor
      · exact pActor.trans qActor.symm
      · have qBefore : Qualified s node k role q := by simpa [Qualified, setLocal, qActor] using hq
        exact qualified_unique beforeUnique hp qBefore
    · have pAfter : Qualified (setLocal s actor replacement) node k role p := by
        simpa [Qualified, setLocal, pActor] using hp
      exact qualified_unique afterUnique pAfter hq

theorem no_owner_unqualified {n : Nat} {s : State n} {node k : Nat} {role : Bool} {p : Proc n}
    (noOwner : owner s node k role = none) (child : Child node k role p.val) :
    ¬ k - 1 ≤ passedLevel (s p) := by
  intro qualified
  exact owner_none noOwner ⟨p, child, qualified⟩

theorem role_view_equiv {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {node k time : Nat} {role : Bool} {p : Proc n} {pc : Node.PC}
    (child : Child node k role p.val)
    (selected : owner (trace time) node k role = none ∨ owner (trace time) node k role = some p) :
    RolePC cfg trace commands node k time role pc ↔ ViewPC cfg trace commands p k time pc := by
  rcases selected with absent | present
  · simp [RolePC, ViewPC, absent, no_owner_unqualified absent child]
  · simp [RolePC, ViewPC, present, (owner_some present).2]

theorem prior_role_view_equiv {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {node k time : Nat} {role : Bool} {p : Proc n} {pc : Node.PC}
    (child : Child node k role p.val)
    (selected : owner (trace (time + 1)) node k role = none ∨ owner (trace (time + 1)) node k role = some p) :
    PriorRolePC cfg trace commands node k time role pc ↔ PriorViewPC cfg trace commands p k time pc := by
  rcases selected with absent | present
  · simp [PriorRolePC, PriorViewPC, absent, no_owner_unqualified absent child]
  · simp [PriorRolePC, PriorViewPC, present, (owner_some present).2]

theorem role_value_proxy {n : Nat} {s : State n} {node k : Nat} {role : Bool} {p : Proc n}
    (wf : WellFormed s) (child : Child node k role p.val)
    (selected : owner s node k role = none ∨ owner s node k role = some p) :
    roleValue s node k role = Node.projectValue k (s p).q := by
  rcases selected with absent | present
  · have same := viewBase_unqualified (wf p) (no_owner_unqualified absent child)
    have value := congrArg Node.Local.q same
    simpa [roleValue, absent, viewBase] using value.symm
  · simp [roleValue, present]

noncomputable def roleAction {n : Nat} (s : State n) (command : Command n) (node k : Nat) (role : Bool) : LocalAction :=
  match owner s node k role with
  | none => .stay
  | some p => commandAction s command p k

theorem role_action_proxy {n : Nat} {s : State n} {command : Command n} {node k : Nat}
    {role : Bool} {p : Proc n} (child : Child node k role p.val)
    (selected : owner s node k role = none ∨ owner s node k role = some p) :
    roleAction s command node k role = commandAction s command p k := by
  rcases selected with absent | present
  · have notQualified := no_owner_unqualified absent child
    cases command <;> simp [roleAction, absent, commandAction, ordinaryAction, notQualified]
  · simp [roleAction, present]

/-- A concrete step cannot exchange two physical representatives atomically.
The proxy is whichever actual owner exists on either side; when absent, its
unqualified local state projects to the empty role. -/
theorem concrete_role_projection {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {time : Nat}
    (initially : trace 0 = initial n) (valid : ValidPrefix cfg trace commands (time + 1))
    (node k : Nat) (positive : 0 < k) (within : k ≤ height n)
    (lower : ∀ t, t ≤ time + 1 → TreeUnique (k - 1) (trace t))
    (role : Bool) (pc : Node.PC) (choice : PriorRolePC cfg trace commands node k time role pc) :
    ∃ before, RolePC cfg trace commands node k time role before ∧
      LocalAction.effect (roleAction (trace time) (commands time) node k role) role
        (roleValue (trace time) node k (!role)) ⟨before, roleValue (trace time) node k role⟩ =
          ⟨pc, roleValue (trace (time + 1)) node k role⟩ := by
  have wf : WellFormed (trace time) := reachable_wellFormed (prefix_reachable initially valid time (by omega))
  have postWF : WellFormed (trace (time + 1)) := reachable_wellFormed (prefix_reachable initially valid (time + 1) (by omega))
  have lift (p : Proc n) (child : Child node k role p.val)
      (before : owner (trace time) node k role = none ∨ owner (trace time) node k role = some p)
      (after : owner (trace (time + 1)) node k role = none ∨ owner (trace (time + 1)) node k role = some p) :
      ∃ old, RolePC cfg trace commands node k time role old ∧
        LocalAction.effect (roleAction (trace time) (commands time) node k role) role
          (roleValue (trace time) node k (!role)) ⟨old, roleValue (trace time) node k role⟩ =
            ⟨pc, roleValue (trace (time + 1)) node k role⟩ := by
    have viewChoice := (prior_role_view_equiv child after).mp choice
    obtain ⟨old, hOld, effect⟩ := concrete_view_projection initially valid k positive within
      (fun t ht => lower t (by omega)) p (roleValue (trace time) node k (!role)) pc viewChoice
    refine ⟨old, (role_view_equiv child before).mpr hOld, ?_⟩
    have roleEq := ((child_iff node k p.val role positive).mp child).2
    simpa only [role_action_proxy child before, role_value_proxy wf child before,
      role_value_proxy postWF child after, roleEq] using effect
  cases before : owner (trace time) node k role with
  | some p =>
    apply lift p (owner_some before).1 (Or.inr before)
    cases after : owner (trace (time + 1)) node k role with
    | none => exact Or.inl rfl
    | some q =>
      have eq := owner_no_swap (lower time (by omega)) (lower (time + 1) (by omega))
        (valid time (by omega)) before after
      exact Or.inr (congrArg some eq.symm)
  | none =>
    cases after : owner (trace (time + 1)) node k role with
    | some p => exact lift p (owner_some after).1 (Or.inl before) (Or.inr after)
    | none =>
      have pcEq : pc = .read1 := by simpa [PriorRolePC, after] using choice
      refine ⟨.read1, by simp [RolePC, before], ?_⟩
      simp [roleAction, before, LocalAction.effect, roleValue, after, pcEq]

theorem role_actions_exclusive {n : Nat} (s : State n) (command : Command n) (node k : Nat) :
    roleAction s command node k false = .stay ∨ roleAction s command node k true = .stay := by
  cases left : owner s node k false with
  | none => exact Or.inl (by simp [roleAction, left])
  | some p =>
    cases right : owner s node k true with
    | none => exact Or.inr (by simp [roleAction, right])
    | some q =>
      have hp := (owner_some left).1
      have hq := (owner_some right).1
      have different : p ≠ q := by
        intro eq
        subst q
        simp only [Child, Bool.false_eq_true, ite_false, Nat.add_zero, ite_true] at hp hq
        omega
      cases command with
      | run actor =>
        by_cases eq : actor = p
        · exact Or.inr (by simp [roleAction, right, commandAction, eq, different])
        · exact Or.inl (by simp [roleAction, left, commandAction, eq])
      | fail actor =>
        by_cases eq : actor = p
        · exact Or.inr (by simp [roleAction, right, commandAction, eq, different])
        · exact Or.inl (by simp [roleAction, left, commandAction, eq])
      | restart | stutter => exact Or.inl (by simp [roleAction, left, commandAction])

theorem product_action (left right : LocalAction) (l0 l1 : Node.Local)
    (exclusive : left = .stay ∨ right = .stay) (reach : Node.Reachable ⟨l0, l1⟩) :
    Node.Reachable ⟨left.effect false l1.q l0, right.effect true l0.q l1⟩ := by
  cases left <;> cases right <;> simp_all [LocalAction.effect]
  all_goals first
    | exact reach
    | simpa [Node.next, Node.State.local, Node.State.setLocal] using Node.Reachable.step (.run false) reach
    | simpa [Node.next, Node.State.local, Node.State.setLocal] using Node.Reachable.step (.run true) reach
    | simpa [Node.next, Node.State.local, Node.State.setLocal] using Node.Reachable.step (.reset false) reach
    | simpa [Node.next, Node.State.local, Node.State.setLocal] using Node.Reachable.step (.reset true) reach

theorem product_step {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {time : Nat}
    (initially : trace 0 = initial n) (valid : ValidPrefix cfg trace commands (time + 1))
    (node k : Nat) (positive : 0 < k) (within : k ≤ height n)
    (lower : ∀ t, t ≤ time + 1 → TreeUnique (k - 1) (trace t))
    (before : ProductReachable cfg trace commands node k time) :
    ProductReachable cfg trace commands node k (time + 1) := by
  have prior : ∀ a b, PriorRolePC cfg trace commands node k time false a →
      PriorRolePC cfg trace commands node k time true b →
      Node.Reachable ⟨⟨a, roleValue (trace (time + 1)) node k false⟩,
        ⟨b, roleValue (trace (time + 1)) node k true⟩⟩ := by
    intro a b ha hb
    obtain ⟨old0, hc0, effect0⟩ := concrete_role_projection initially valid node k positive within lower false a ha
    obtain ⟨old1, hc1, effect1⟩ := concrete_role_projection initially valid node k positive within lower true b hb
    have h := product_action _ _ _ _ (role_actions_exclusive (trace time) (commands time) node k)
      (before old0 old1 hc0 hc1)
    simp only [Bool.not_false, Bool.not_true] at effect0 effect1
    rw [effect0, effect1] at h
    exact h
  intro a b ha hb
  have wf := reachable_wellFormed (prefix_reachable initially valid (time + 1) (by omega))
  have qa := rolePC_sample_extension positive wf (lower (time + 1) (by omega)) ha
  have qb := rolePC_sample_extension positive wf (lower (time + 1) (by omega)) hb
  exact product_sample_extension _ _ _ _ prior a b qa qb

theorem prefix_products {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish : Nat}
    (initially : trace 0 = initial n) (valid : ValidPrefix cfg trace commands finish)
    (k : Nat) (positive : 0 < k) (within : k ≤ height n)
    (lower : ∀ t, t ≤ finish → TreeUnique (k - 1) (trace t)) :
    ∀ time, time ≤ finish → ∀ node, ProductReachable cfg trace commands node k time := by
  intro time
  induction time with
  | zero => intro _ node; exact product_initial node k positive initially
  | succ time ih =>
    intro bound node
    exact product_step initially (fun t ht => valid t (by omega)) node k positive within
      (fun t ht => lower t (by omega)) (ih (by omega) node)

theorem treeUnique_of_products {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {k time : Nat} (positive : 0 < k)
    (lower : TreeUnique (k - 1) (trace time))
    (products : ∀ node, ProductReachable cfg trace commands node k time) :
    TreeUnique k (trace time) := by
  intro p q same hp hq
  let node := p.val / 2 ^ k
  have pChild : Child node k (bit p.val k) p.val :=
    (child_iff _ _ _ _ positive).mpr ⟨rfl, rfl⟩
  have qChild : Child node k (bit q.val k) q.val :=
    (child_iff _ _ _ _ positive).mpr ⟨same.symm, rfl⟩
  have pq : Qualified (trace time) node k (bit p.val k) p := ⟨pChild, by omega⟩
  have qq : Qualified (trace time) node k (bit q.val k) q := ⟨qChild, by omega⟩
  by_cases roles : bit p.val k = bit q.val k
  · exact qualified_unique lower pq (roles ▸ qq)
  · have pPC := rolePC_owner (cfg := cfg) (commands := commands) (owner_eq_some lower pq) (localPC_held hp)
    have qPC := rolePC_owner (cfg := cfg) (commands := commands) (owner_eq_some lower qq) (localPC_held hq)
    have contradiction : False := by
      cases pr : bit p.val k <;> cases qr : bit q.val k <;> simp only [pr, qr] at roles pPC qPC
      · exact roles trivial
      · exact Node.retained_winner_exclusion (products node .held .held pPC qPC) ⟨rfl, rfl⟩
      · exact Node.retained_winner_exclusion (products node .held .held qPC pPC) ⟨rfl, rfl⟩
      · exact roles trivial
    exact contradiction.elim

/-- The lower-tree premise is discharged by increasing-level induction over
the actual finite initial prefix. Representative identity and scan order remain
unrestricted parts of that concrete execution. -/
theorem concrete_treeUnique {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish : Nat}
    (initially : trace 0 = initial n) (valid : ValidPrefix cfg trace commands finish) :
    ∀ k, k ≤ height n → ∀ time, time ≤ finish → TreeUnique k (trace time) := by
  intro k
  induction k with
  | zero => intro _ time _; exact treeUnique_zero (trace time)
  | succ k ih =>
    intro within time bound
    have lower : ∀ t, t ≤ finish → TreeUnique ((k + 1) - 1) (trace t) := by
      simpa using ih (by omega)
    exact treeUnique_of_products (by omega) (lower time bound)
      (prefix_products initially valid (k + 1) (by omega) within lower time bound)

theorem Node.reachable_commands {s : Node.State} (reach : Node.Reachable s) :
    ∃ commands : List Node.Command, commands.foldl Node.next Node.initial = s := by
  induction reach with
  | initial => exact ⟨[], rfl⟩
  | step command _ ih =>
    obtain ⟨commands, same⟩ := ih
    exact ⟨commands ++ [command], by simp [List.foldl_append, same]⟩

/-- Explicit finite node-command extraction from an actual concrete prefix.
The final private continuations may be any supported choices; every pair has
a valid finite node trace. Tree uniqueness is proved internally, not assumed.
Several node sample steps may correspond to one concrete state boundary. -/
theorem concrete_node_trace {n : Nat} {cfg : Config n} {trace : Nat → State n}
    {commands : Nat → Command n} {finish : Nat}
    (initially : trace 0 = initial n) (valid : ValidPrefix cfg trace commands finish)
    (node k : Nat) (positive : 0 < k) (within : k ≤ height n)
    (a b : Node.PC) (left : RolePC cfg trace commands node k finish false a)
    (right : RolePC cfg trace commands node k finish true b) :
    ∃ nodeCommands : List Node.Command,
      nodeCommands.foldl Node.next Node.initial =
        ⟨⟨a, roleValue (trace finish) node k false⟩, ⟨b, roleValue (trace finish) node k true⟩⟩ := by
  have lower := concrete_treeUnique initially valid (k - 1) (by omega)
  exact Node.reachable_commands (prefix_products initially valid k positive within lower
    finish (le_refl _) node a b left right)

/-- Every inductively reachable LTS state has a concrete finite command prefix.
The tail outside the prefix is irrelevant; no fairness is needed. -/
theorem reachable_has_prefix {n : Nat} {cfg : Config n} {s : State n}
    (reach : Reachable cfg s) :
    ∃ (finish : Nat) (trace : Nat → State n) (commands : Nat → Command n),
      trace 0 = initial n ∧ ValidPrefix cfg trace commands finish ∧ trace finish = s := by
  induction reach with
  | initial =>
    exact ⟨0, fun _ => initial n, fun _ => .stutter, rfl, by intro time bound; omega, rfl⟩
  | @step s t a _ edge ih =>
    obtain ⟨command, hc, _⟩ := edge
    obtain ⟨finish, trace, commands, initially, valid, last⟩ := ih
    let trace' : Nat → State n := fun time => if time ≤ finish then trace time else t
    let commands' : Nat → Command n := fun time => if time < finish then commands time else command
    refine ⟨finish + 1, trace', commands', ?_, ?_, ?_⟩
    · simpa [trace'] using initially
    · intro time bound
      by_cases earlier : time < finish
      · simpa [trace', commands', earlier, show time ≤ finish by omega,
          show time + 1 ≤ finish by omega] using valid time earlier
      · have eq : time = finish := by omega
        subst time
        simpa [trace', commands', last, show ¬ finish + 1 ≤ finish by omega] using hc
    · simp [trace']

/-- Algorithm 2 mutual exclusion for every positive population and every fixed
complete scan enumeration, with arbitrary repeated passages, failure and
restart, and no fairness or representative-uniqueness assumption. -/
theorem safety : SafetyTarget := by
  intro n cfg s reach
  obtain ⟨finish, trace, commands, initially, valid, last⟩ := reachable_has_prefix reach
  apply root_exclusion_of_treeUnique reach
  rw [← last]
  exact concrete_treeUnique initially valid (height n) (le_refl _) finish (le_refl _)

end EconomicalSolutions.Algorithm2

#print axioms EconomicalSolutions.Algorithm2.safety
#print axioms EconomicalSolutions.Algorithm2.concrete_treeUnique
#print axioms EconomicalSolutions.Algorithm2.concrete_view_projection
#print axioms EconomicalSolutions.Algorithm2.product_step

#print axioms EconomicalSolutions.Algorithm2.concrete_node_trace
