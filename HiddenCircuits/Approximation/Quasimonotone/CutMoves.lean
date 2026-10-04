import HiddenCircuits.Approximation.Quasimonotone.CutExtension
namespace HiddenCircuits.Approximation.QuasimonotoneProof
open GraphReduction
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V}
def PartnerMove (M N : PerfectPartner G) : Prop :=
  ∃ a b : V, N.val=fun x => Equiv.swap a b (M.val (Equiv.swap a b x))
variable (P Q : PerfectPartner G) (base : V)
theorem swap_right_left (a b : RightSide P Q base) (x : LeftSide P Q base) :
    Equiv.swap a.val b.val x.val=x.val := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact Set.disjoint_left.mp (sides_disjoint P Q base) x.property (h.symm ▸ a.property)
  · intro h
    exact Set.disjoint_left.mp (sides_disjoint P Q base) x.property (h.symm ▸ b.property)
theorem swap_right_outside (a b : RightSide P Q base) {x : V} (hx : x∉RightSide P Q base) :
    Equiv.swap a.val b.val x=x := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h; exact hx (h.symm ▸ a.property)
  · intro h; exact hx (h.symm ▸ b.property)
theorem extendCut_conjugate (f g : ComponentCut P Q base) (a b : RightSide P Q base)
    (hg : g.val=f.val.trans (Equiv.swap a b)) :
    (extendCut P Q base g).val = fun x =>
      Equiv.swap a.val b.val ((extendCut P Q base f).val (Equiv.swap a.val b.val x)) := by
  funext x
  change extendCutFun P Q base g x=Equiv.swap a.val b.val
    (extendCutFun P Q base f (Equiv.swap a.val b.val x))
  by_cases hl : x∈LeftSide P Q base
  · let z : LeftSide P Q base := ⟨x,hl⟩
    change extendCutFun P Q base g z.val=_
    rw [swap_right_left P Q base a b z,extendCut_left,extendCut_left,hg]
    exact (Subtype.val_injective.swap_apply a b (f.val z)).symm
  by_cases hr : x∈RightSide P Q base
  · let z : RightSide P Q base := ⟨x,hr⟩
    change extendCutFun P Q base g z.val=_
    rw [Subtype.val_injective.swap_apply a b z,extendCut_right,extendCut_right,
      swap_right_left,hg]
    rfl
  · have h := source_outside P Q base hl hr
    rw [swap_right_outside P Q base a b hr,extendCut_outside P Q base f hl hr,
      swap_right_outside P Q base a b h.2,extendCut_outside P Q base g hl hr]
theorem extendCut_move (f g : ComponentCut P Q base) (a b : RightSide P Q base)
    (hg : g.val=f.val.trans (Equiv.swap a b)) :
    PartnerMove (extendCut P Q base f) (extendCut P Q base g) :=
  ⟨a.val,b.val,extendCut_conjugate P Q base f g a b hg⟩
end HiddenCircuits.Approximation.QuasimonotoneProof
