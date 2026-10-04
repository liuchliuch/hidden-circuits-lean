import HiddenCircuits.GraphReduction.ProbeCount

/-! The original matching expansion with a separate edge color for every probe.
The original endpoint is used once, even if several probe neighborhoods contain it. -/
namespace HiddenCircuits.GraphReduction
variable {X Y I : Type*}

def coloredEdge (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (c : X → Option I) (x : X) (y : Y) : Prop :=
  match c x with
  | none => R x y
  | some i => A i x ∧ B i y

/-- A full original bijection whose edges independently choose an original or probe color. -/
def EdgeColoredMatching (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) :=
  Σ e : X ≃ Y, {c : X → Option I // ∀ x, coloredEdge R A B c x (e x)}

/-- Vertex-color fibers are independently chosen; the matching preserves them. -/
def OriginalColorData (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) :=
  Σ cd : Assignments A B, ColoredCutBijection (coloredEdge R A B cd.val.1) cd.val.1 cd.val.2

namespace OriginalColorData
variable {R : X → Y → Prop} {A : I → X → Prop} {B : I → Y → Prop}

def forget (d : OriginalColorData R A B) : EdgeColoredMatching R A B :=
  ⟨d.2.val.val,⟨d.1.val.1,d.2.val.property⟩⟩

 theorem rightColor_forget (d : OriginalColorData R A B) (y : Y) :
    d.1.val.2 y = d.1.val.1 (d.2.val.val.symm y) := by
  simpa only [Equiv.apply_symm_apply] using d.2.property (d.2.val.val.symm y)
end OriginalColorData

/-- Transporting a left edge color across its actual bijection uniquely colors the right endpoint. -/
def edgeColorsToData {R : X → Y → Prop} {A : I → X → Prop} {B : I → Y → Prop}
    (d : EdgeColoredMatching R A B) : OriginalColorData R A B := by
  refine ⟨⟨(d.2.val,fun y => d.2.val (d.1.symm y)),?_,?_⟩,⟨⟨d.1,d.2.property⟩,?_⟩⟩
  · intro x i h
    dsimp only at h
    have he := d.2.property x
    change coloredEdge R A B d.2.val x (d.1 x) at he
    rw [coloredEdge,h] at he
    exact he.1
  · intro y i h
    dsimp only at h
    have he := d.2.property (d.1.symm y)
    rw [coloredEdge,h,Equiv.apply_symm_apply] at he
    exact he.2
  · intro x
    exact congrArg d.2.val (d.1.symm_apply_apply x)

 theorem edgeColorsToData_forget {R : X → Y → Prop} {A : I → X → Prop} {B : I → Y → Prop}
    (d : OriginalColorData R A B) : edgeColorsToData d.forget = d := by
  rcases d with ⟨⟨⟨c,d⟩,hv⟩,e⟩
  have hd : (fun y => c (e.val.val.symm y))=d := by
    funext y
    exact (OriginalColorData.rightColor_forget ⟨⟨(c,d),hv⟩,e⟩ y).symm
  have hcd : (edgeColorsToData (OriginalColorData.forget ⟨⟨(c,d),hv⟩,e⟩)).1=⟨(c,d),hv⟩ := by
    apply Subtype.ext
    exact Prod.ext rfl hd
  apply Sigma.ext hcd
  apply (Subtype.heq_iff_coe_eq ?_).mpr
  · rfl
  · intro f
    change (∀ x, c (e.val.val.symm (f.val x)) = c x) ↔ (∀ x, d (f.val x)=c x)
    constructor
    · intro h x; exact (congrFun hd (f.val x)).symm.trans (h x)
    · intro h x; exact (congrFun hd (f.val x)).trans (h x)

/-- This equivalence counts choices separately even for overlapping probe neighborhoods. -/
def originalColorDataEquiv (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) :
    EdgeColoredMatching R A B ≃ OriginalColorData R A B where
  toFun := edgeColorsToData
  invFun := OriginalColorData.forget
  left_inv d := rfl
  right_inv := edgeColorsToData_forget

/-- Complete cut bijections impose no extra data beyond their underlying bijection. -/
def trueCutBijectionEquiv (X Y : Type*) : CutBijection (fun (_ : X) (_ : Y) => True) ≃ (X ≃ Y) where
  toFun e := e.val
  invFun e := ⟨e,fun _ => trivial⟩
  left_inv e := rfl
  right_inv e := rfl

/-- A none-colored edge is an actual original graph edge. -/
def originalNoneEquiv (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (cd : Assignments A B) :
    CutBijection (fun (x : OriginalFiber cd.val.1 none) (y : OriginalFiber cd.val.2 none) =>
      coloredEdge R A B cd.val.1 x.val y.val) ≃ OriginalResidual R cd.val :=
  cutBijectionCongr _ _ (Equiv.refl _) (Equiv.refl _) (by intro x y; simp [coloredEdge,x.property])

/-- A probe-colored block allows every bijection between its prescribed endpoint sets. -/
def originalSomeEquiv (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (cd : Assignments A B) (i : I) :
    CutBijection (fun (x : OriginalFiber cd.val.1 (some i)) (y : OriginalFiber cd.val.2 (some i)) =>
      coloredEdge R A B cd.val.1 x.val y.val) ≃
      (OriginalFiber cd.val.1 (some i) ≃ OriginalFiber cd.val.2 (some i)) :=
  (cutBijectionCongr _ (fun _ _ => True) (Equiv.refl _) (Equiv.refl _) (by
    intro x y
    simp [coloredEdge,x.property,cd.property.1 x.val i x.property,cd.property.2 y.val i y.property])).trans
      (trueCutBijectionEquiv _ _)

def OriginalColorBlocks (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (cd : Assignments A B) :=
  OriginalResidual R cd.val ×
    ∀ i, OriginalFiber cd.val.1 (some i) ≃ OriginalFiber cd.val.2 (some i)

def originalColorBlocksEquiv (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (cd : Assignments A B) :
    ColoredCutBijection (coloredEdge R A B cd.val.1) cd.val.1 cd.val.2 ≃ OriginalColorBlocks R A B cd :=
  (coloredCutBijectionEquiv _ _ _).trans
    (Equiv.piOptionEquivProd.trans
      (Equiv.prodCongr (originalNoneEquiv R A B cd)
        (Equiv.piCongrRight (originalSomeEquiv R A B cd))))

variable [Fintype X] [Fintype Y] [Fintype I]

noncomputable instance originalColorBlocksFintype (R : X → Y → Prop) (A : I → X → Prop)
    (B : I → Y → Prop) (cd : Assignments A B) : Fintype (OriginalColorBlocks R A B cd) := by
  classical
  unfold OriginalColorBlocks
  infer_instance

 theorem originalColorBlocks_balance {R : X → Y → Prop} {A : I → X → Prop} {B : I → Y → Prop}
    {cd : Assignments A B} (b : OriginalColorBlocks R A B cd) : BalancedAssignments cd.val :=
  fun i => Fintype.card_congr (b.2 i)

def balancedOriginalBlocksEquiv (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) :
    (Σ cd : Assignments A B, OriginalColorBlocks R A B cd) ≃
      Σ cd : BalancedColors A B, OriginalColorBlocks R A B cd.val where
  toFun d := ⟨⟨d.1,originalColorBlocks_balance d.2⟩,d.2⟩
  invFun d := ⟨d.1.val,d.2⟩
  left_inv d := rfl
  right_inv d := rfl

/-- Expanding each weighted original edge is exactly the same independent-block sum. -/
def edgeColoredBlocksEquiv (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) :
    EdgeColoredMatching R A B ≃ Σ cd : BalancedColors A B, OriginalColorBlocks R A B cd.val :=
  (originalColorDataEquiv R A B).trans
    ((Equiv.sigmaCongrRight (originalColorBlocksEquiv R A B)).trans
      (balancedOriginalBlocksEquiv R A B))

end HiddenCircuits.GraphReduction
