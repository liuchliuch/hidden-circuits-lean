import HiddenCircuits.CutMatching

/-! Restricting a genuine cut matching to disjoint color fibers. -/
namespace HiddenCircuits.GraphReduction

variable {X Y I : Type*}

/-- A cut bijection that respects independently supplied vertex colors. -/
def ColoredCutBijection (R : X → Y → Prop) (c : X → I) (d : Y → I) :=
  {e : CutBijection R // ∀ x, d (e.val x) = c x}

namespace ColoredCutBijection
variable {R : X → Y → Prop} {c : X → I} {d : Y → I}

def restrict (e : ColoredCutBijection R c d) (i : I) :
    CutBijection (fun (x : {x // c x = i}) (y : {y // d y = i}) => R x.val y.val) :=
  ⟨{ toFun x := ⟨e.val.val x.val,(e.property x.val).trans x.property⟩
     invFun y := ⟨e.val.val.symm y.val, by
       rw [← e.property (e.val.val.symm y.val),Equiv.apply_symm_apply]
       exact y.property⟩
     left_inv x := Subtype.ext (e.val.val.symm_apply_apply x.val)
     right_inv y := Subtype.ext (e.val.val.apply_symm_apply y.val) },
    fun x => e.val.property x.val⟩

/-- Glue independent fiber matchings; the color index is retained by every edge. -/
def glue
    (e : ∀ i, CutBijection
      (fun (x : {x // c x = i}) (y : {y // d y = i}) => R x.val y.val)) :
    ColoredCutBijection R c d := by
  let f : X ≃ Y := (Equiv.sigmaFiberEquiv c).symm.trans
    ((Equiv.sigmaCongrRight (fun i => (e i).val)).trans (Equiv.sigmaFiberEquiv d))
  refine ⟨⟨f,?_⟩,?_⟩
  · intro x
    exact (e (c x)).property ⟨x,rfl⟩
  · intro x
    exact ((e (c x)).val ⟨x,rfl⟩).property

 theorem glue_restrict (e : ColoredCutBijection R c d) : glue e.restrict = e := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rfl

 theorem restrict_glue
    (e : ∀ i, CutBijection
      (fun (x : {x // c x = i}) (y : {y // d y = i}) => R x.val y.val)) :
    (glue e).restrict = e := by
  funext i
  apply Subtype.ext
  apply Equiv.ext
  rintro ⟨x,hx⟩
  subst i
  rfl
end ColoredCutBijection

/-- Exact, two-sided decomposition into independent matching fibers. -/
def coloredCutBijectionEquiv (R : X → Y → Prop) (c : X → I) (d : Y → I) :
    ColoredCutBijection R c d ≃
      (∀ i, CutBijection
        (fun (x : {x // c x = i}) (y : {y // d y = i}) => R x.val y.val)) where
  toFun := ColoredCutBijection.restrict
  invFun := ColoredCutBijection.glue
  left_inv := ColoredCutBijection.glue_restrict
  right_inv := ColoredCutBijection.restrict_glue

end HiddenCircuits.GraphReduction
