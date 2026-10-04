import HiddenCircuits.Approximation.Quasimonotone.CutMoves
import HiddenCircuits.Approximation.CanonicalPaths.MonotoneFlow
namespace HiddenCircuits.Approximation.QuasimonotoneProof
open GraphReduction CanonicalPaths FiniteChains.MonotoneSwitch
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V}
  (P Q : PerfectPartner G) (base : V) (hG : Quasimonotone G)
noncomputable def cutStateEquiv : ColumnState (cutEndpoints P Q base hG) ≃ ComponentCut P Q base :=
  (inverseEquiv _).trans ((cutOrdering P Q base hG).cutBijectionEquiv (sides_balanced P Q base)).symm
noncomputable abbrev cutRows := (cutOrdering P Q base hG).rows
noncomputable abbrev cutColumns := (cutOrdering P Q base hG).balancedColumns (sides_balanced P Q base)
theorem cutStateEquiv_apply (s : ColumnState (cutEndpoints P Q base hG)) (x : LeftSide P Q base) :
    (cutStateEquiv P Q base hG s).val x =
      cutColumns P Q base hG (s.val.symm ((cutRows P Q base hG).symm x)) := rfl
theorem cutStateEquiv_symm_apply (s : ColumnState (cutEndpoints P Q base hG)) (y : RightSide P Q base) :
    (cutStateEquiv P Q base hG s).val.symm y =
      cutRows P Q base hG (s.val ((cutColumns P Q base hG).symm y)) := rfl
theorem cutStateEquiv_transpose {s t : ColumnState (cutEndpoints P Q base hG)}
    (i j : Fin (Fintype.card (LeftSide P Q base))) (ht : t.val=(Equiv.swap i j).trans s.val) :
    (cutStateEquiv P Q base hG t).val = (cutStateEquiv P Q base hG s).val.trans
      (Equiv.swap (cutColumns P Q base hG i) (cutColumns P Q base hG j)) := by
  apply Equiv.ext
  intro x
  rw [cutStateEquiv_apply]
  simp only [Equiv.trans_apply,cutStateEquiv_apply,ht,Equiv.symm_trans_apply,Equiv.symm_swap]
  exact ((cutColumns P Q base hG).injective.swap_apply i j _).symm
noncomputable def cutMatching (s : ColumnState (cutEndpoints P Q base hG)) : PerfectPartner G :=
  extendCut P Q base (cutStateEquiv P Q base hG s)
theorem cutMatching_move {s t : ColumnState (cutEndpoints P Q base hG)}
    (hm : LocalRoutes.Move Finset.univ s t) :
    PartnerMove (cutMatching P Q base hG s) (cutMatching P Q base hG t) := by
  obtain ⟨i,_,j,_,h⟩ := hm
  exact extendCut_move P Q base _ _ _ _ (cutStateEquiv_transpose P Q base hG i j h)
noncomputable def sourceState : ColumnState (cutEndpoints P Q base hG) :=
  (cutStateEquiv P Q base hG).symm (sourceCut P Q base)
noncomputable def targetState : ColumnState (cutEndpoints P Q base hG) :=
  (cutStateEquiv P Q base hG).symm (targetCut P Q base)
@[simp] theorem cutMatching_source : cutMatching P Q base hG (sourceState P Q base hG)=P := by
  simp [cutMatching,sourceState]
@[simp] theorem cutMatching_target : cutMatching P Q base hG (targetState P Q base hG)=
    extendCut P Q base (targetCut P Q base) := by
  simp [cutMatching,targetState]
end HiddenCircuits.Approximation.QuasimonotoneProof
