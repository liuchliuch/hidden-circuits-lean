import HiddenCircuits.Approximation.FiniteChains.SwitchKernel
import HiddenCircuits.Approximation.CanonicalPaths.LocalRouteSupport
namespace HiddenCircuits.Approximation.FiniteChains.MonotoneSwitch
open HiddenCircuits.Approximation.CanonicalPaths
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (E : MonotoneEndpoints n)
abbrev ColumnState := LocalRoutes.State (fun col row => Allowed E row col)
def inverseEquiv : ColumnState E ≃ E.Permutations where
  toFun p := ⟨p.val.symm,fun row => by
    have h := p.property (p.val.symm row)
    simpa only [Equiv.apply_symm_apply] using h⟩
  invFun p := ⟨p.val.symm,fun col => by
    have h := p.property (p.val.symm col)
    simpa only [Equiv.apply_symm_apply] using h⟩
  left_inv p := by apply Subtype.ext; exact p.val.symm_symm
  right_inv p := by apply Subtype.ext; exact p.val.symm_symm
@[simp] theorem inverseEquiv_val (p : ColumnState E) : (inverseEquiv E p).val=p.val.symm := rfl
@[simp] theorem inverseEquiv_symm_val (p : E.Permutations) :
    ((inverseEquiv E).symm p).val=p.val.symm := rfl
theorem inverse_transpose (p q : ColumnState E) (i j : Fin n)
    (h : q.val=(Equiv.swap i j).trans p.val) :
    (inverseEquiv E q).val =
      (Equiv.swap (p.val i) (p.val j)).trans (inverseEquiv E p).val := by
  simp only [inverseEquiv_val]
  rw [h]
  apply Equiv.ext
  intro row
  simp only [Equiv.symm_trans_apply,Equiv.symm_swap,Equiv.trans_apply]
  apply p.val.injective
  simp only [Equiv.apply_symm_apply]
  simpa only [Equiv.apply_symm_apply] using
    (p.val.injective.swap_apply i j (p.val.symm row)).symm
theorem move_switch {S : Finset (Fin n)} {p q : ColumnState E}
    (h : LocalRoutes.Move S p q) :
    ∃ i∈S, ∃ j∈S, E.switch (p.val i) (p.val j) (inverseEquiv E p)=inverseEquiv E q := by
  rcases h with ⟨i,hi,j,hj,h⟩
  exact ⟨i,hi,j,hj,switch_eq_of_transpose E _ _ _ _ (inverse_transpose E p q i j h)⟩
def columnStep (m : ℕ) (p : ColumnState E) (r : CoinTape (1+(m+m))) : ColumnState E :=
  (inverseEquiv E).symm (step E m (inverseEquiv E p) r)
theorem columnStep_involutive (m : ℕ) (r : CoinTape (1+(m+m))) :
    Function.Involutive (fun p => columnStep E m p r) := by
  intro p
  dsimp [columnStep]
  rw [(inverseEquiv E).apply_symm_apply]
  have h := step_involutive E m r (inverseEquiv E p)
  change step E m (step E m (inverseEquiv E p) r) r = inverseEquiv E p at h
  rw [h,(inverseEquiv E).symm_apply_apply]
theorem columnStep_transition (m : ℕ) (p q : ColumnState E) :
    transitionProbability (1+(m+m)) (columnStep E m) p q =
      transitionProbability (1+(m+m)) (step E m) (inverseEquiv E p) (inverseEquiv E q) := by
  apply coinProbability_congr
  intro r
  exact (inverseEquiv E).symm_apply_eq
theorem columnStep_lazy (m : ℕ) (p : ColumnState E) :
    (1:ℚ)/2 ≤ transitionProbability (1+(m+m)) (columnStep E m) p p := by
  rw [columnStep_transition]
  exact step_lazy E m _
noncomputable def columnChain (m : ℕ) : LazyChain (ColumnState E) :=
  LazyChain.ofCoinStep (1+(m+m)) (columnStep E m)
    (columnStep_involutive E m) (columnStep_lazy E m)
@[simp] theorem columnChain_weight (m : ℕ) (p q : ColumnState E) :
    (columnChain E m).weight p q = (chain E m).weight (inverseEquiv E p) (inverseEquiv E q) := by
  change (transitionProbability _ (columnStep E m) p q : ℝ) = _
  rw [columnStep_transition]
  rfl
theorem move_chain_lower {S : Finset (Fin n)} {p q : ColumnState E}
    (h : LocalRoutes.Move S p q) :
    (1:ℝ)/(8*(n+1)^2 : ℕ) ≤ (columnChain E (Nat.size n)).weight p q := by
  obtain ⟨i,hi,j,hj,hs⟩ := move_switch E h
  rw [columnChain_weight,← hs]
  exact chain_switch_polynomial_lower_all E _ _ _
theorem move_chain_lower_sharp (hn : 0<n) {S : Finset (Fin n)} {p q : ColumnState E}
    (h : LocalRoutes.Move S p q) :
    (1:ℝ)/(8*n^2 : ℕ) ≤ (columnChain E (Nat.size n)).weight p q := by
  obtain ⟨i,hi,j,hj,hs⟩ := move_switch E h
  rw [columnChain_weight,← hs]
  exact chain_switch_polynomial_lower E hn _ _ _
theorem card_columnStates_le : Fintype.card (ColumnState E) ≤ 2^(n^2) := by
  rw [Fintype.card_congr (inverseEquiv E)]
  exact card_states_le E
end HiddenCircuits.Approximation.FiniteChains.MonotoneSwitch
