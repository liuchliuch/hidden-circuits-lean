import HiddenCircuits.Approximation.Quasimonotone.AlternatingComponents
import HiddenCircuits.Approximation.MonotoneDeletion
import HiddenCircuits.GraphReduction.MonotoneEndpointBridge
namespace HiddenCircuits.Approximation.QuasimonotoneProof
open GraphReduction
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V}
  (P Q : PerfectPartner G) (base : V)
abbrev LeftSide := leftOrbit (partnerPerm P) (partnerPerm Q) base
abbrev RightSide := rightOrbit (partnerPerm P) (partnerPerm Q) base
theorem sides_disjoint : Disjoint (LeftSide P Q base) (RightSide P Q base) :=
  orbits_disjoint _ _ (partnerPerm_involutive P) (partnerPerm_involutive Q)
    (partnerPerm_free P) (partnerPerm_free Q) base
noncomputable def sourceCut : CutBijection (fun x : LeftSide P Q base => fun y : RightSide P Q base => G.Adj x.val y.val) :=
  ⟨sourceCutEquiv (partnerPerm P) (partnerPerm Q) (partnerPerm_involutive P) base,
    fun x => P.property.2 x.val⟩
noncomputable def targetCut : CutBijection (fun x : LeftSide P Q base => fun y : RightSide P Q base => G.Adj x.val y.val) :=
  ⟨targetCutEquiv (partnerPerm P) (partnerPerm Q) (partnerPerm_involutive P) (partnerPerm_involutive Q) base,
    fun x => Q.property.2 x.val⟩
theorem sides_balanced : Fintype.card (RightSide P Q base)=Fintype.card (LeftSide P Q base) :=
  (Fintype.card_congr (sourceCut P Q base).val).symm
noncomputable def cutOrdering (hG : Quasimonotone G) :
    MonotoneOrdering (fun x : LeftSide P Q base => fun y : RightSide P Q base => G.Adj x.val y.val) := by
  classical
  let L := LeftSide P Q base
  let R := RightSide P Q base
  letI : Fintype L := @Subtype.fintype V (fun v => v∈L) (fun _ => Classical.propDecidable _) _
  letI : Fintype R := @Subtype.fintype V (fun v => v∈R) (fun _ => Classical.propDecidable _) _
  let f : R → {v : V // v∉L} := fun y => ⟨y.val,by
    intro hy
    exact Set.disjoint_left.mp (sides_disjoint P Q base) hy y.property⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : {v : V // v∉L} => z.val) h)
  let O := Classical.choice (hG L)
  exact MonotoneRestriction.ordering O id f Function.injective_id hf
noncomputable def cutEndpoints (hG : Quasimonotone G) : MonotoneEndpoints (Fintype.card (LeftSide P Q base)) :=
  (cutOrdering P Q base hG).endpoints (sides_balanced P Q base)
noncomputable def sourceEndpoint (hG : Quasimonotone G) : (cutEndpoints P Q base hG).Permutations :=
  (cutOrdering P Q base hG).cutBijectionEquiv (sides_balanced P Q base) (sourceCut P Q base)
noncomputable def targetEndpoint (hG : Quasimonotone G) : (cutEndpoints P Q base hG).Permutations :=
  (cutOrdering P Q base hG).cutBijectionEquiv (sides_balanced P Q base) (targetCut P Q base)
end HiddenCircuits.Approximation.QuasimonotoneProof
