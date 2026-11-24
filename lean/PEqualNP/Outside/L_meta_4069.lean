import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4069

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- One gate step of the wire computation.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- Wire lists of equal length, the second at least the first at every index.
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
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
    exact h i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega), ← hl]
    rcases Nat.eq_zero_or_pos (i - w.length) with h0 | h0
    · rw [h0] at hi ⊢
      simpa using ha (by simpa using hi)
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      exact absurd hi (by simp)

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, Le w w' → Le (gs.foldl step w) (gs.foldl step w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    exact append_le _ _ _ _ h
      (op_mono g (hgs g (List.mem_cons_self ..)) w w' h.2)

theorem ofFn_le (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    Le (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, fun i hi => ?_⟩
  by_cases hn : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hn)] at hi ⊢
    simp only [List.getElem_ofFn] at hi ⊢
    exact hxy _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact absurd hi (by simp)

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

end PEqualNP.Outside.L_meta_4069

theorem PEqualNP.Outside.L_meta_4069 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 x5 : Fin x1 → Bool), (∀ (x6 : Fin x1), x4 x6 = Bool.true → x5 x6 = Bool.true) → PEqualNP.MetaComplexity.circuitFun x1 x2 x4 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x5 = Bool.true := by
  intro n C hC x y hxy hx
  have hops : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  have hle := PEqualNP.Outside.L_meta_4069.fold_le C.gates hops _ _
    (PEqualNP.Outside.L_meta_4069.ofFn_le n x y hxy)
  simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
    PEqualNP.Outside.L_meta_4069.wires_eq] at hx ⊢
  exact hle.2 _ hx
