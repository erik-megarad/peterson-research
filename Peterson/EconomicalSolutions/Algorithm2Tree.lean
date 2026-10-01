import Peterson.EconomicalSolutions.Algorithm2Observations

namespace EconomicalSolutions.Algorithm2

/-- At level k, each block of 2^k leaves has at most one retained concrete
winner. This is the induction conclusion, never a transition premise. -/
def TreeUnique {n : Nat} (k : Nat) (s : State n) : Prop :=
  ∀ p q, p.val / 2 ^ k = q.val / 2 ^ k →
    k ≤ passedLevel (s p) → k ≤ passedLevel (s q) → p = q

theorem treeUnique_zero {n : Nat} (s : State n) : TreeUnique 0 s := by
  intro p q same _ _
  apply Fin.ext
  simpa using same

theorem child_number (i k : Nat) (positive : 0 < k) :
    i / 2 ^ (k - 1) = 2 * (i / 2 ^ k) + (if bit i k then 1 else 0) := by
  have pow : 2 ^ k = 2 ^ (k - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  have div : (i / 2 ^ (k - 1)) / 2 = i / 2 ^ k := by rw [Nat.div_div_eq_div_mul, ← pow]
  have modlt := Nat.mod_lt (i / 2 ^ (k - 1)) (by decide : 0 < 2)
  simp only [bit, beq_iff_eq]
  split <;> omega

def Child (node k : Nat) (role : Bool) (i : Nat) : Prop :=
  i / 2 ^ (k - 1) = 2 * node + (if role then 1 else 0)

theorem child_iff (node k i : Nat) (role : Bool) (positive : 0 < k) :
    Child node k role i ↔ i / 2 ^ k = node ∧ bit i k = role := by
  have number := child_number i k positive
  cases role <;> cases hb : bit i k <;> simp [Child, hb] at * <;> omega

theorem opponent_child {node k i j : Nat} {role : Bool} (positive : 0 < k)
    (own : Child node k role i) : Opponent i j k ↔ Child node k (!role) j := by
  have own' := (child_iff node k i role positive).mp own
  rw [child_iff node k j (!role) positive]
  simp only [Opponent, own'.1, own'.2]
  cases role <;> cases bit j k <;> simp

/-- Qualification includes a winner still delayed before publishing level k.
At k=1 every real leaf qualifies for its own one-leaf child. -/
def Qualified {n : Nat} (s : State n) (node k : Nat) (role : Bool) (p : Proc n) : Prop :=
  Child node k role p.val ∧ k - 1 ≤ passedLevel (s p)

theorem qualified_unique {n : Nat} {s : State n} {node k : Nat} {role : Bool}
    (unique : TreeUnique (k - 1) s) {p q : Proc n}
    (hp : Qualified s node k role p) (hq : Qualified s node k role q) : p = q :=
  unique p q (hp.1.trans hq.1.symm) hp.2 hq.2

noncomputable def owner {n : Nat} (s : State n) (node k : Nat) (role : Bool) : Option (Proc n) := by
  classical
  exact if h : ∃ p, Qualified s node k role p then some (Classical.choose h) else none

theorem owner_some {n : Nat} {s : State n} {node k : Nat} {role : Bool} {p : Proc n}
    (h : owner s node k role = some p) : Qualified s node k role p := by
  classical
  unfold owner at h
  split at h
  · rename_i present
    have same := Option.some.inj h
    exact same ▸ Classical.choose_spec present
  · contradiction

theorem owner_eq_some {n : Nat} {s : State n} {node k : Nat} {role : Bool} {p : Proc n}
    (unique : TreeUnique (k - 1) s) (h : Qualified s node k role p) :
    owner s node k role = some p := by
  classical
  unfold owner
  split
  · rename_i present
    exact congrArg some (qualified_unique unique (Classical.choose_spec present) h)
  · rename_i no
    exact (no ⟨p, h⟩).elim

theorem owner_none {n : Nat} {s : State n} {node k : Nat} {role : Bool}
    (h : owner s node k role = none) : ¬ ∃ p, Qualified s node k role p := by
  classical
  unfold owner at h
  split at h
  · contradiction
  · assumption

theorem active_qualified {n : Nat} {s : State n} {node k : Nat} {role : Bool} {p : Proc n}
    (wf : WellFormed s) (child : Child node k role p.val) (active : k ≤ (s p).q.level) :
    Qualified s node k role p := by
  refine ⟨child, ?_⟩
  have := (localWF_levels (wf p)).2
  omega

noncomputable def roleValue {n : Nat} (s : State n) (node k : Nat) (role : Bool) : Node.Value :=
  match owner s node k role with
  | none => .O
  | some p => Node.projectValue k (s p).q

theorem real_visible {n : Nat} (s : State n) (p : Proc n) :
    visible s (⟨p.val, Nat.lt_of_lt_of_le p.isLt (real_fits_padding n)⟩ : Leaf n) = (s p).q := by
  simp [visible, p.isLt]

/-- Lower-tree uniqueness makes every historical observation agree with the
opposite role's visible abstract value at that very boundary. -/
theorem observation_roleValue {n : Nat} {cfg : Config n} {s : State n}
    {node k : Nat} {role : Bool} {p : Proc n} {x : Value}
    (positive : 0 < k) (wf : WellFormed s) (unique : TreeUnique (k - 1) s)
    (own : Child node k role p.val)
    (observed : ScanBridge.Represents (cfg.order p k) k (visible s) x) :
    Node.projectValue k x = roleValue s node k (!role) := by
  rcases observed with ⟨deadEq, absent⟩ | ⟨j, member, high, value⟩
  · subst x
    have projectDead : Node.projectValue k dead = .O := by
      simp [Node.projectValue, dead, ScanBridge.dead, positive]
    rw [projectDead]
    unfold roleValue
    cases selected : owner s node k (!role) with
    | none => rfl
    | some q =>
      have qChild := (owner_some selected).1
      let j : Leaf n := ⟨q.val, Nat.lt_of_lt_of_le q.isLt (real_fits_padding n)⟩
      have opp : Opponent p.val j.val k := (opponent_child positive own).mpr qChild
      have low := absent j ((cfg.complete p k j).mpr opp)
      have visibleQ : visible s j = (s q).q := real_visible s q
      rw [visibleQ] at low
      simp [Node.projectValue, low]
  · have real : j.val < n := by
      by_contra dummy
      rw [dummy_dead s j (by omega)] at high
      simp only [dead, ScanBridge.dead] at high
      omega
    let q : Proc n := ⟨j.val, real⟩
    have visibleQ : visible s j = (s q).q := by simp [visible, real, q]
    have qChild : Child node k (!role) q.val :=
      (opponent_child positive own).mp ((cfg.complete p k j).mp member)
    have selected : owner s node k (!role) = some q :=
      owner_eq_some unique (active_qualified wf qChild (visibleQ ▸ high))
    simp only [roleValue, selected]
    rw [value, visibleQ]

/-- The scan bridge's uniqueness premise is a consequence of the lower-node
induction conclusion and actual reachable register levels. -/
theorem scan_unique_of_treeUnique {n : Nat} {cfg : Config n} {s : State n}
    (k : Nat) (positive : 0 < k) (wf : WellFormed s)
    (unique : TreeUnique (k - 1) s) (p : Proc n) :
    ScanBridge.Unique (cfg.order p k) k (visible s) := by
  intro i hi j hj ai aj
  have real (a : Leaf n) (active : k ≤ (visible s a).level) : a.val < n := by
    by_contra h
    rw [dummy_dead s a (by omega)] at active
    simp only [dead, ScanBridge.dead] at active
    omega
  let pi : Proc n := ⟨i.val, real i ai⟩
  let pj : Proc n := ⟨j.val, real j aj⟩
  have vi : visible s i = (s pi).q := by simp [visible, pi, real i ai]
  have vj : visible s j = (s pj).q := by simp [visible, pj, real j aj]
  have own : Child (p.val / 2 ^ k) k (bit p.val k) p.val :=
    (child_iff _ _ _ _ positive).mpr ⟨rfl, rfl⟩
  have qi := active_qualified wf ((opponent_child positive own).mp ((cfg.complete p k i).mp hi))
    (vi ▸ ai)
  have qj := active_qualified wf ((opponent_child positive own).mp ((cfg.complete p k j).mp hj))
    (vj ▸ aj)
  have eq : pi = pj := qualified_unique unique qi qj
  exact Fin.ext (congrArg (fun a : Proc n => a.val) eq)

theorem next_other_local {n : Nat} {cfg : Config n} {s t : State n} {command : Command n}
    (p : Proc n) (step : next cfg s command = some t)
    (nr : command ≠ .run p) (nf : command ≠ .fail p) (ns : command ≠ .restart p) :
    t p = s p := by
  cases command with
  | stutter => exact congrFun (Option.some.inj step.symm) p
  | run actor =>
    have ne : p ≠ actor := by intro eq; subst actor; exact nr rfl
    simp only [next] at step
    cases h : ordinary cfg actor s with
    | none => simp [h] at step
    | some l =>
      have ht : t = setLocal s actor l := by simpa [h] using step.symm
      simp [ht, setLocal, ne]
  | fail actor =>
    have ne : p ≠ actor := by intro eq; subst actor; exact nf rfl
    simp only [next] at step
    split at step
    · simp at step
    · simp [← Option.some.inj step, setLocal, ne]
  | restart actor =>
    have ne : p ≠ actor := by intro eq; subst actor; exact ns rfl
    simp only [next] at step
    split at step
    · simp [← Option.some.inj step, setLocal, ne]
    · simp at step

/-- A qualified representative survives until its own concrete reset; other
actors and its higher-level instructions cannot silently replace it. -/
theorem qualified_retains {n : Nat} {cfg : Config n} {s t : State n} {command : Command n}
    {node k : Nat} {role : Bool} {p : Proc n}
    (wf : WellFormed s) (step : next cfg s command = some t)
    (qualified : Qualified s node k role p) (noReset : ¬ Resets s command p) :
    Qualified t node k role p :=
  ⟨qualified.1, qualified.2.trans (next_retains_levels p wf step noReset).2⟩

theorem root_exclusion_of_treeUnique {n : Nat} {s : State n} {cfg : Config n}
    (reach : Reachable cfg s) (unique : TreeUnique (height n) s) : MutualExclusion s := by
  intro p q hp hq
  have pRoot := critical_root_passed reach p hp
  have qRoot := critical_root_passed reach q hq
  apply unique p q _ (by omega) (by omega)
  have pSmall : p.val < 2 ^ height n := Nat.lt_of_lt_of_le p.isLt (real_fits_padding n)
  have qSmall : q.val < 2 ^ height n := Nat.lt_of_lt_of_le q.isLt (real_fits_padding n)
  simp [Nat.div_eq_of_lt pSmall, Nat.div_eq_of_lt qSmall]

end EconomicalSolutions.Algorithm2

#print axioms EconomicalSolutions.Algorithm2.treeUnique_zero

#print axioms EconomicalSolutions.Algorithm2.opponent_child

#print axioms EconomicalSolutions.Algorithm2.observation_roleValue

#print axioms EconomicalSolutions.Algorithm2.scan_unique_of_treeUnique

#print axioms EconomicalSolutions.Algorithm2.qualified_retains

#print axioms EconomicalSolutions.Algorithm2.root_exclusion_of_treeUnique
