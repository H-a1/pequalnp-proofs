import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4451

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Wire lists, gate by gate, as in the root model.
def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl stepW w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs ++ [g]) w = stepW (run gs w) g := by
  simp [run, List.foldl_append]

theorem length_run (gs : List Gate) : ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [run]
  | cons g gs ih =>
    intro w
    have h := ih (stepW w g)
    show (run gs (stepW w g)).length = _
    rw [h]; simp [stepW]; omega

theorem gd_lt {α : Type} (L : List α) (a d : α) (i : ℕ) (h : i < L.length) :
    (L ++ [a]).getD i d = L.getD i d := List.getD_append _ _ _ _ h

theorem gd_eq {α : Type} (L : List α) (a d : α) : (L ++ [a]).getD L.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem gd_ge {α : Type} (L : List α) (d : α) (i : ℕ) (h : L.length ≤ i) : L.getD i d = d :=
  List.getD_eq_default _ _ h

theorem gd_gt {α : Type} (L : List α) (a d : α) (i : ℕ) (h : L.length < i) :
    (L ++ [a]).getD i d = d := gd_ge _ _ _ (by simp; omega)

theorem run_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (run gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have h1 := ih (stepW w g) i (by simp [stepW]; omega)
    show (run gs (stepW w g)).getD i false = _
    rw [h1]; simp only [stepW]; exact gd_lt _ _ _ _ hi

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  by_cases h : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [h]

theorem eval2 (op : GateOp) (h : op = GateOp.and ∨ op = GateOp.or) (p q : Bool) :
    op.eval [p, q] = (bif op.eval [false, true] then (p || q) else (p && q)) := by
  rcases h with h | h <;> subst h <;> cases p <;> cases q <;> rfl

-- Substituting false for one input wire and propagating the constant.
-- A status is none for a wire that is constantly false, some j for new wire j.
def look (st : List (Option ℕ)) (i : ℕ) : Option ℕ := st.getD i none

def stepT (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate) :
    List (Option ℕ) × List Gate :=
  match g.inputs with
  | [a, b] =>
    match look acc.1 a, look acc.1 b with
    | some a', some b' => (acc.1 ++ [some (n + acc.2.length)], acc.2 ++ [⟨g.op, [a', b']⟩])
    | some a', none => (acc.1 ++ [bif g.op.eval [false, true] then some a' else none], acc.2)
    | none, some b' => (acc.1 ++ [bif g.op.eval [false, true] then some b' else none], acc.2)
    | none, none => (acc.1 ++ [none], acc.2)
  | _ => (acc.1 ++ [none], acc.2)

def init (n u : ℕ) : List (Option ℕ) × List Gate :=
  ((List.range n).map (fun i => if i = u then none else some i), [])

structure Inv (n : ℕ) (X Y : List Bool) (pre : List Gate)
    (acc : List (Option ℕ) × List Gate) : Prop where
  len : acc.1.length = n + pre.length
  bnd : ∀ i j, look acc.1 i = some j → j < n + acc.2.length
  val : ∀ i j, look acc.1 i = some j → (run acc.2 X).getD j false = (run pre Y).getD i false
  zer : ∀ i, look acc.1 i = none → (run pre Y).getD i false = false
  rb : ∀ k < acc.2.length, ∀ i ∈ (acc.2.getD k ⟨GateOp.or, []⟩).inputs, i < n + k
  ao : ∀ h ∈ acc.2, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length = 2

theorem inv_of (n : ℕ) (X Y : List Bool) (hY : Y.length = n)
    (pre : List Gate) (st : List (Option ℕ)) (ng : List Gate) (g : Gate)
    (I : Inv n X Y pre (st, ng)) (s : Option ℕ) (ng' : List Gate)
    (hng : ∀ j < n + ng.length, (run ng' X).getD j false = (run ng X).getD j false)
    (hlen : ng.length ≤ ng'.length)
    (hsome : ∀ j, s = some j → j < n + ng'.length ∧
        (run ng' X).getD j false = (run (pre ++ [g]) Y).getD (n + pre.length) false)
    (hnone : s = none → (run (pre ++ [g]) Y).getD (n + pre.length) false = false)
    (hrb : ∀ k < ng'.length, ∀ i ∈ (ng'.getD k ⟨GateOp.or, []⟩).inputs, i < n + k)
    (hao : ∀ h ∈ ng', (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length = 2) :
    Inv n X Y (pre ++ [g]) (st ++ [s], ng') := by
  have hYlen : (run pre Y).length = n + pre.length := by rw [length_run, hY]
  have hlenst : st.length = n + pre.length := I.len
  have hrun : ∀ i < n + pre.length,
      (run (pre ++ [g]) Y).getD i false = (run pre Y).getD i false := by
    intro i hi; rw [run_snoc]; simp only [stepW]; exact gd_lt _ _ _ _ (by omega)
  have hbeyond : ∀ i, n + pre.length < i → (run (pre ++ [g]) Y).getD i false = false := by
    intro i hi; rw [run_snoc]; simp only [stepW]; exact gd_gt _ _ _ _ (by omega)
  have hlook : ∀ i, i < n + pre.length → look (st ++ [s]) i = look st i := by
    intro i hi; simp only [look]; exact gd_lt _ _ _ _ (by omega)
  have hlook_eq : look (st ++ [s]) (n + pre.length) = s := by
    simp only [look]; rw [← hlenst]; exact gd_eq _ _ _
  have hlook_gt : ∀ i, n + pre.length < i → look (st ++ [s]) i = none := by
    intro i hi; simp only [look]; exact gd_gt _ _ _ _ (by omega)
  refine ⟨by simp only [List.length_append, List.length_singleton, hlenst]; omega,
    ?_, ?_, ?_, hrb, hao⟩
  · intro i j hij
    show j < n + ng'.length
    rcases lt_trichotomy i (n + pre.length) with h | h | h
    · rw [hlook i h] at hij; have := I.bnd i j hij; simp only at this; omega
    · subst h; rw [hlook_eq] at hij; exact (hsome j hij).1
    · rw [hlook_gt i h] at hij; exact absurd hij (by simp)
  · intro i j hij
    show (run ng' X).getD j false = (run (pre ++ [g]) Y).getD i false
    rcases lt_trichotomy i (n + pre.length) with h | h | h
    · rw [hlook i h] at hij
      rw [hrun i h, hng j (I.bnd i j hij)]; exact I.val i j hij
    · subst h; rw [hlook_eq] at hij; exact (hsome j hij).2
    · rw [hlook_gt i h] at hij; exact absurd hij (by simp)
  · intro i hi
    rcases lt_trichotomy i (n + pre.length) with h | h | h
    · rw [hlook i h] at hi; rw [hrun i h]; exact I.zer i hi
    · subst h; rw [hlook_eq] at hi; exact hnone hi
    · exact hbeyond i h

theorem inv_step (n : ℕ) (X Y : List Bool) (hX : X.length = n) (hY : Y.length = n)
    (pre : List Gate) (acc : List (Option ℕ) × List Gate) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (I : Inv n X Y pre acc) : Inv n X Y (pre ++ [g]) (stepT n acc g) := by
  obtain ⟨hop, hlen⟩ := hg
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  obtain ⟨st, ng⟩ := acc
  have hXlen : (run ng X).length = n + ng.length := by rw [length_run, hX]
  have hYlen : (run pre Y).length = n + pre.length := by rw [length_run, hY]
  have hv : (run (pre ++ [g]) Y).getD (n + pre.length) false =
      g.op.eval [(run pre Y).getD a false, (run pre Y).getD b false] := by
    rw [run_snoc]; simp only [stepW, hab, List.map_cons, List.map_nil]
    rw [← hYlen]; exact gd_eq _ _ _
  have hev := eval2 g.op hop
  cases ha : look st a with
  | some a' =>
    cases hb : look st b with
    | some b' =>
      have hst : stepT n (st, ng) g =
          (st ++ [some (n + ng.length)], ng ++ [⟨g.op, [a', b']⟩]) := by
        simp only [stepT, hab, ha, hb]
      rw [hst]
      apply inv_of n X Y hY pre st ng g I
      · intro j hj; rw [run_snoc]; simp only [stepW]; exact gd_lt _ _ _ _ (by omega)
      · simp
      · intro j hj
        simp only [Option.some.injEq] at hj; subst hj
        refine ⟨by simp, ?_⟩
        rw [run_snoc]; simp only [stepW, List.map_cons, List.map_nil]
        rw [← hXlen, gd_eq, hv, I.val a a' ha, I.val b b' hb]
      · intro h; exact absurd h (by simp)
      · intro k hk i hi
        simp only [List.length_append, List.length_singleton] at hk
        rcases Nat.lt_or_ge k ng.length with hk' | hk'
        · rw [gd_lt _ _ _ _ hk'] at hi; exact I.rb k hk' i hi
        · have hk2 : k = ng.length := by omega
          subst hk2
          rw [gd_eq] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h | h
          · rw [h]; exact I.bnd a a' ha
          · rw [h]; exact I.bnd b b' hb
      · intro h hh
        simp only [List.mem_append, List.mem_singleton] at hh
        rcases hh with hh | hh
        · exact I.ao h hh
        · subst hh; exact ⟨hop, by simp⟩
    | none =>
      have hst : stepT n (st, ng) g =
          (st ++ [bif g.op.eval [false, true] then some a' else none], ng) := by
        simp only [stepT, hab, ha, hb]
      rw [hst]
      have hbz := I.zer b hb
      apply inv_of n X Y hY pre st ng g I _ ng (fun _ _ => rfl) (le_refl _)
      · intro j hj
        cases hor : g.op.eval [false, true] <;> simp only [hor, Bool.cond_true, Bool.cond_false] at hj
        · exact absurd hj (by simp)
        · simp only [Option.some.injEq] at hj; subst hj
          refine ⟨I.bnd a a' ha, ?_⟩
          rw [hv, hev, hor, hbz, I.val a a' ha]; simp
      · intro hj
        cases hor : g.op.eval [false, true] <;> simp only [hor, Bool.cond_true, Bool.cond_false] at hj
        · rw [hv, hev, hor, hbz]; simp
        · exact absurd hj (by simp)
      · exact I.rb
      · exact I.ao
  | none =>
    have haz := I.zer a ha
    cases hb : look st b with
    | some b' =>
      have hst : stepT n (st, ng) g =
          (st ++ [bif g.op.eval [false, true] then some b' else none], ng) := by
        simp only [stepT, hab, ha, hb]
      rw [hst]
      apply inv_of n X Y hY pre st ng g I _ ng (fun _ _ => rfl) (le_refl _)
      · intro j hj
        cases hor : g.op.eval [false, true] <;> simp only [hor, Bool.cond_true, Bool.cond_false] at hj
        · exact absurd hj (by simp)
        · simp only [Option.some.injEq] at hj; subst hj
          refine ⟨I.bnd b b' hb, ?_⟩
          rw [hv, hev, hor, haz, I.val b b' hb]; simp
      · intro hj
        cases hor : g.op.eval [false, true] <;> simp only [hor, Bool.cond_true, Bool.cond_false] at hj
        · rw [hv, hev, hor, haz]; simp
        · exact absurd hj (by simp)
      · exact I.rb
      · exact I.ao
    | none =>
      have hbz := I.zer b hb
      have hst : stepT n (st, ng) g = (st ++ [none], ng) := by
        simp only [stepT, hab, ha, hb]
      rw [hst]
      apply inv_of n X Y hY pre st ng g I _ ng (fun _ _ => rfl) (le_refl _)
      · intro j hj; exact absurd hj (by simp)
      · intro _
        rw [hv, hev, haz, hbz]; cases g.op.eval [false, true] <;> rfl
      · exact I.rb
      · exact I.ao

theorem inv_fold (n : ℕ) (X Y : List Bool) (hX : X.length = n) (hY : Y.length = n)
    (acc0 : List (Option ℕ) × List Gate) (I0 : Inv n X Y [] acc0) :
    ∀ gs : List Gate, (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
      Inv n X Y gs (gs.foldl (stepT n) acc0) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _; exact I0
  | append_singleton pre g ih =>
    intro hgs
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact inv_step n X Y hX hY pre _ g (hgs g (by simp))
      (ih (fun g' hg' => hgs g' (List.mem_append_left _ hg')))

theorem look_init (n u i : ℕ) :
    look (init n u).1 i = if i < n ∧ i ≠ u then some i else none := by
  unfold look init
  by_cases h : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp only [List.getElem_map, List.getElem_range]
    by_cases h' : i = u <;> simp [h, h']
  · rw [List.getD_eq_default _ _ (by simpa using h)]; simp [h]

theorem inv_init (n u : ℕ) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i.val ≠ u → y i = x i) (hyu : ∀ i : Fin n, i.val = u → y i = false) :
    Inv n (List.ofFn x) (List.ofFn y) [] (init n u) := by
  refine ⟨by simp [init], ?_, ?_, ?_, ?_, ?_⟩
  · intro i j h
    rw [look_init] at h
    split_ifs at h with hc
    · simp only [Option.some.injEq] at h; subst h; simp [init]; exact hc.1
  · intro i j h
    rw [look_init] at h
    split_ifs at h with hc
    simp only [Option.some.injEq] at h; subst h
    simp only [init, run, List.foldl_nil, getD_ofFn, hc.1, dite_true]
    exact (hxy ⟨i, hc.1⟩ hc.2).symm
  · intro i h
    rw [look_init] at h
    split_ifs at h with hc
    simp only [run, List.foldl_nil, getD_ofFn]
    split_ifs with hi
    · exact hyu ⟨i, hi⟩ (by by_contra hne; exact hc ⟨hi, hne⟩)
    · rfl
  · intro k hk; simp [init] at hk
  · intro h hh; simp [init] at hh

-- Length bookkeeping of the substitution pass.
theorem stepT_fst (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate) :
    ∃ s, (stepT n acc g).1 = acc.1 ++ [s] := by
  unfold stepT
  split
  · split <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem stepT_snd (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate) :
    (stepT n acc g).2.length ≤ acc.2.length + 1 := by
  unfold stepT
  split
  · split <;> simp
  · simp

theorem stepT_drop (n u : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate)
    (hu : u ∈ g.inputs) (hl : look acc.1 u = none) : (stepT n acc g).2 = acc.2 := by
  unfold stepT
  split
  · rename_i a b hab
    rw [hab] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with h | h
    · subst h; rw [hl]; cases look acc.1 b <;> rfl
    · subst h; rw [hl]; cases look acc.1 a <;> rfl
  · rfl

theorem fold_len (n u : ℕ) : ∀ (gs : List Gate) (acc : List (Option ℕ) × List Gate),
    look acc.1 u = none → u < acc.1.length →
    (gs.foldl (stepT n) acc).2.length ≤ acc.2.length + gs.length ∧
    ((∃ g ∈ gs, u ∈ g.inputs) → (gs.foldl (stepT n) acc).2.length < acc.2.length + gs.length) := by
  intro gs
  induction gs with
  | nil => intro acc _ _; simp
  | cons g gs ih =>
    intro acc hl hu
    obtain ⟨s, hs⟩ := stepT_fst n acc g
    have hl' : look (stepT n acc g).1 u = none := by
      rw [hs]; simp only [look]; rw [gd_lt _ _ _ _ hu]; exact hl
    have hu' : u < (stepT n acc g).1.length := by rw [hs]; simp; omega
    obtain ⟨h1, h2⟩ := ih (stepT n acc g) hl' hu'
    have hstep := stepT_snd n acc g
    simp only [List.foldl_cons, List.length_cons]
    refine ⟨by omega, ?_⟩
    rintro ⟨g', hg', hug'⟩
    simp only [List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · have := stepT_drop n u acc g' hug' hl
      rw [this] at h1; omega
    · have := h2 ⟨g', hg', hug'⟩; omega

-- A circuit that never reads wire u does not see input u.
theorem run_agree (u : ℕ) : ∀ (gs : List Gate), (∀ g ∈ gs, u ∉ g.inputs) →
    ∀ w w' : List Bool, w.length = w'.length → (∀ i, i ≠ u → w.getD i false = w'.getD i false) →
    ∀ i, i ≠ u → (run gs w).getD i false = (run gs w').getD i false := by
  intro gs
  induction gs with
  | nil => intro _ w w' _ h; exact h
  | cons g gs ih =>
    intro hgs w w' hl h
    show ∀ i, i ≠ u → (run gs (stepW w g)).getD i false = (run gs (stepW w' g)).getD i false
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [stepW, hl]
    · intro i hi
      have hmap : (g.inputs.map fun j => w.getD j false) = g.inputs.map fun j => w'.getD j false := by
        apply List.map_congr_left
        intro j hj
        exact h j (fun e => hgs g (List.mem_cons_self ..) (e ▸ hj))
      simp only [stepW]
      rcases lt_trichotomy i w.length with hi' | hi' | hi'
      · rw [gd_lt _ _ _ _ hi', gd_lt _ _ _ _ (hl ▸ hi')]; exact h i hi
      · subst hi'; rw [gd_eq, hl, gd_eq, hmap]
      · rw [gd_gt _ _ _ _ hi', gd_gt _ _ _ _ (hl ▸ hi')]

-- Monotonicity of AND/OR circuits.
def Le (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, w.getD i false = true → w'.getD i false = true

theorem op_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true)
    (hv : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg
  · rw [hg] at hv ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hv ⊢
    rintro x ⟨i, hi, rfl⟩
    exact h i (hv _ ⟨i, hi, rfl⟩)
  · rw [hg] at hv ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hv ⊢
    obtain ⟨x, ⟨i, hi, rfl⟩, hx⟩ := hv
    exact ⟨_, ⟨i, hi, rfl⟩, h i hx⟩

theorem append_le (w w' : List Bool) (a a' : Bool) (h : Le w w') (ha : a = true → a' = true) :
    Le (w ++ [a]) (w' ++ [a']) := by
  obtain ⟨hl, h⟩ := h
  refine ⟨by simp [hl], fun i hi => ?_⟩
  rcases lt_trichotomy i w.length with hlt | heq | hgt
  · rw [gd_lt _ _ _ _ hlt] at hi; rw [gd_lt _ _ _ _ (hl ▸ hlt)]; exact h i hi
  · subst heq; rw [gd_eq] at hi; rw [hl, gd_eq]; exact ha hi
  · rw [gd_gt _ _ _ _ hgt] at hi; exact absurd hi (by simp)

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, Le w w' → Le (run gs w) (run gs w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    show Le (run gs (stepW w g)) (run gs (stepW w' g))
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    exact append_le _ _ _ _ h (op_mono g (hgs g (List.mem_cons_self ..)) w w' h.2)

theorem ofFn_le (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    Le (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, fun i hi => ?_⟩
  rw [getD_ofFn] at hi ⊢
  split_ifs at hi ⊢ with h
  exact hxy _ hi

end PEqualNP.Outside.L_meta_4451

open PEqualNP.Outside.L_meta_4451 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_4451 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → x3 ≠ x4 → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x7 : Fin x1) => Decidable.decide (x7 = x3)) = Bool.false → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x8 : Fin x1) => Decidable.decide (x8 = x4)) = Bool.false → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x9 : Fin x1) => Decidable.decide (x9 = x3 ∨ x9 = x4)) = Bool.true → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x10 ∧ x10.size < x2.size ∧ (∀ (x11 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x10 x11 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x11 = Bool.true) ∧ ∀ (x11 : Fin x1 → Bool), x11 x3 = Bool.false → PEqualNP.MetaComplexity.circuitFun x1 x10 x11 = PEqualNP.MetaComplexity.circuitFun x1 x2 x11 := by
  intro n C u v hC huv h1 h2 h3
  obtain ⟨hao, hrb, hfan⟩ := hC
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hao g hg, hfan g hg⟩
  -- the substitution x_u := false, by input
  let yOf : (Fin n → Bool) → Fin n → Bool := fun x i => if i = u then false else x i
  have Iof : ∀ x : Fin n → Bool, Inv n (List.ofFn x) (List.ofFn (yOf x)) C.gates
      (C.gates.foldl (stepT n) (init n u.val)) := by
    intro x
    apply inv_fold n _ _ (by simp) (by simp) _ _ C.gates hg
    apply inv_init n u.val x (yOf x)
    · intro i hi
      have : i ≠ u := fun e => hi (e ▸ rfl)
      simp [yOf, this]
    · intro i hi
      have : i = u := Fin.ext hi
      simp [yOf, this]
  let R := C.gates.foldl (stepT n) (init n u.val)
  let D : Circuit := ⟨R.2, (look R.1 C.output).getD (n + R.2.length)⟩
  have key : ∀ x : Fin n → Bool, circuitFun n D x = circuitFun n C (yOf x) := by
    intro x
    have I := Iof x
    simp only [circuitFun, Circuit.eval, wires_eq]
    show (run R.2 (List.ofFn x)).getD ((look R.1 C.output).getD (n + R.2.length)) false = _
    cases hl : look R.1 C.output with
    | some j => simp only [Option.getD_some]; exact I.val _ _ hl
    | none =>
      simp only [Option.getD_none]
      rw [I.zer _ hl]
      apply gd_ge
      rw [length_run]; simp
  -- some gate reads input u
  have hread : ∃ g ∈ C.gates, u.val ∈ g.inputs := by
    by_contra hno
    push Not at hno
    have hkeep : ∀ x : Fin n → Bool, circuitFun n C x = (run C.gates (List.ofFn x)).getD C.output false :=
      fun x => rfl
    by_cases ho : C.output = u.val
    · have := h1
      rw [hkeep, ho, run_keep _ _ _ (by simp), getD_ofFn] at this
      simp at this
    · have hag := run_agree u.val C.gates hno
        (List.ofFn fun x9 : Fin n => decide (x9 = u ∨ x9 = v))
        (List.ofFn fun x8 : Fin n => decide (x8 = v)) (by simp)
        (by
          intro i hi
          rw [getD_ofFn, getD_ofFn]
          split_ifs with h
          · have : (⟨i, h⟩ : Fin n) ≠ u := fun e => hi (by rw [← e])
            simp [this]
          · rfl)
        C.output ho
      rw [hkeep, hag, ← hkeep, h2] at h3
      exact absurd h3 (by simp)
  have hsize : D.size < C.size := by
    have hlu : look (init n u.val).1 u.val = none := by rw [look_init]; simp
    have hul : u.val < (init n u.val).1.length := by simp [init]
    have := (fold_len n u.val C.gates (init n u.val) hlu hul).2 hread
    simp only [init, List.length_nil, zero_add] at this
    exact this
  refine ⟨D, ⟨?_, ?_, ?_⟩, hsize, ?_, ?_⟩
  · intro h hh; exact ((Iof (fun _ => false)).ao h hh).1
  · intro j hj i hi; exact (Iof (fun _ => false)).rb j hj i hi
  · intro h hh; exact ((Iof (fun _ => false)).ao h hh).2
  · intro x hx
    rw [key] at hx
    have hle := fold_le C.gates hao _ _ (ofFn_le n (yOf x) x (by
      intro i hi
      by_cases h : i = u
      · simp [yOf, h] at hi
      · simpa [yOf, h] using hi))
    exact hle.2 _ hx
  · intro x hx
    rw [key]
    congr 1
    funext i
    by_cases h : i = u
    · simp [yOf, h, hx]
    · simp [yOf, h]
