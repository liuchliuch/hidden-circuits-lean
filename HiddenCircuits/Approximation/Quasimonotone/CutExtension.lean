import HiddenCircuits.Approximation.Quasimonotone.MonotoneCut
namespace HiddenCircuits.Approximation.QuasimonotoneProof
open GraphReduction
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V}
  (P Q : PerfectPartner G) (base : V)
abbrev ComponentCut := CutBijection
  (fun x : LeftSide P Q base => fun y : RightSide P Q base => G.Adj x.val y.val)
noncomputable def extendCutFun (f : ComponentCut P Q base) (x : V) : V :=
  if hx : x∈LeftSide P Q base then (f.val ⟨x,hx⟩).val
  else if hx : x∈RightSide P Q base then (f.val.symm ⟨x,hx⟩).val
  else P.val x
theorem extendCut_left (f : ComponentCut P Q base) (x : LeftSide P Q base) :
    extendCutFun P Q base f x.val=(f.val x).val := by
  simp [extendCutFun,x.property]
theorem extendCut_right (f : ComponentCut P Q base) (x : RightSide P Q base) :
    extendCutFun P Q base f x.val=(f.val.symm x).val := by
  have hx : x.val∉LeftSide P Q base := fun h =>
    Set.disjoint_left.mp (sides_disjoint P Q base) h x.property
  simp [extendCutFun,hx,x.property]
theorem extendCut_outside (f : ComponentCut P Q base) {x : V}
    (hl : x∉LeftSide P Q base) (hr : x∉RightSide P Q base) :
    extendCutFun P Q base f x=P.val x := by
  simp [extendCutFun,hl,hr]
theorem source_outside {x : V}
    (hl : x∉LeftSide P Q base) (hr : x∉RightSide P Q base) :
    P.val x∉LeftSide P Q base ∧ P.val x∉RightSide P Q base := by
  constructor
  · intro h
    have hh := p_left_to_right (partnerPerm P) (partnerPerm Q) base h
    exact hr (by simpa only [partnerPerm,Equiv.coe_fn_mk,P.property.1 x] using hh)
  · intro h
    have hh := p_right_to_left (partnerPerm P) (partnerPerm Q) (partnerPerm_involutive P) base h
    exact hl (by simpa only [partnerPerm,Equiv.coe_fn_mk,P.property.1 x] using hh)
noncomputable def extendCut (f : ComponentCut P Q base) : PerfectPartner G := by
  refine ⟨extendCutFun P Q base f,?_,?_⟩
  · intro x
    by_cases hl : x∈LeftSide P Q base
    · let y : LeftSide P Q base := ⟨x,hl⟩
      change extendCutFun P Q base f (extendCutFun P Q base f y.val)=y.val
      rw [extendCut_left,extendCut_right,f.val.symm_apply_apply]
    by_cases hr : x∈RightSide P Q base
    · let y : RightSide P Q base := ⟨x,hr⟩
      change extendCutFun P Q base f (extendCutFun P Q base f y.val)=y.val
      rw [extendCut_right,extendCut_left,f.val.apply_symm_apply]
    · have h := source_outside P Q base hl hr
      rw [extendCut_outside P Q base f hl hr,
        extendCut_outside P Q base f h.1 h.2,P.property.1 x]
  · intro x
    by_cases hl : x∈LeftSide P Q base
    · rw [extendCut_left P Q base f ⟨x,hl⟩]
      exact f.property ⟨x,hl⟩
    by_cases hr : x∈RightSide P Q base
    · rw [extendCut_right P Q base f ⟨x,hr⟩]
      have h := f.property (f.val.symm ⟨x,hr⟩)
      simpa only [f.val.apply_symm_apply] using h.symm
    · rw [extendCut_outside P Q base f hl hr]
      exact P.property.2 x
@[simp] theorem extendCut_source : extendCut P Q base (sourceCut P Q base)=P := by
  apply Subtype.ext
  funext x
  change extendCutFun P Q base (sourceCut P Q base) x=P.val x
  by_cases hl : x∈LeftSide P Q base
  · rw [extendCut_left P Q base _ ⟨x,hl⟩]; rfl
  by_cases hr : x∈RightSide P Q base
  · rw [extendCut_right P Q base _ ⟨x,hr⟩]; rfl
  · exact extendCut_outside P Q base _ hl hr
theorem extendCut_target_inside {x : V}
    (hx : x∈LeftSide P Q base ∪ RightSide P Q base) :
    (extendCut P Q base (targetCut P Q base)).val x=Q.val x := by
  change extendCutFun P Q base (targetCut P Q base) x=Q.val x
  rcases hx with h|h
  · rw [extendCut_left P Q base _ ⟨x,h⟩]; rfl
  · rw [extendCut_right P Q base _ ⟨x,h⟩]; rfl
end HiddenCircuits.Approximation.QuasimonotoneProof
