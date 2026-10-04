import HiddenCircuits.GraphReduction.ProbeGraph

/-! A canonical decomposition of actual probe matchings. The original color functions
partition original vertices even when several neighborhoods overlap. -/
namespace HiddenCircuits.GraphReduction
variable {X Y I : Type*}

/-- Original-to-original edges belong only to the uncolored residual matching. -/
def residualCondition (c : X → Option I) {s : ℕ} :
    ProbePart X I s → ProbePart Y I s → Prop
  | .inl x, .inl _ => c x=none
  | _, _ => True

def refinedProbeRelation (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (s : ℕ) (c : X → Option I) (v : ProbePart X I s) (w : ProbePart Y I s) : Prop :=
  probeRelation R A B s v w ∧ residualCondition c v w

/-- An independent choice of original color classes and matching inside those classes. -/
def ProbeDecomposition (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (s : ℕ) :=
  Σ cd : (X → Option I) × (Y → Option I),
    ColoredCutBijection (refinedProbeRelation R A B s cd.1)
      (extendColor cd.1 s) (extendColor cd.2 s)

namespace ProbeDecomposition
variable {R : X → Y → Prop} {A : I → X → Prop} {B : I → Y → Prop} {s : ℕ}

def forget (d : ProbeDecomposition R A B s) : CutBijection (probeRelation R A B s) :=
  ⟨d.2.val.val,fun v => (d.2.val.property v).1⟩

 theorem leftAssignment_forget (d : ProbeDecomposition R A B s) :
    leftAssignment d.forget.val = d.1.1 := by
  funext x
  have hp := d.2.property (.inl x)
  have hv := (d.2.val.property (.inl x)).2
  change extendColor d.1.2 s (d.forget.val (.inl x)) = d.1.1 x at hp
  change residualCondition d.1.1 (.inl x) (d.forget.val (.inl x)) at hv
  unfold leftAssignment
  cases he : d.forget.val (.inl x) with
  | inl y =>
    rw [he] at hv
    exact hv.symm
  | inr z =>
    rw [he] at hp
    exact hp

 theorem rightAssignment_forget (d : ProbeDecomposition R A B s) :
    rightAssignment d.forget.val = d.1.2 := by
  funext y
  have hp := d.2.property (d.forget.val.symm (.inl y))
  change extendColor d.1.2 s (d.forget.val (d.forget.val.symm (.inl y))) =
    extendColor d.1.1 s (d.forget.val.symm (.inl y)) at hp
  rw [Equiv.apply_symm_apply] at hp
  unfold rightAssignment
  cases he : d.forget.val.symm (.inl y) with
  | inl x =>
    have hi : d.forget.val (.inl x) = .inl y := by rw [← he,Equiv.apply_symm_apply]
    have hv := (d.2.val.property (.inl x)).2
    change residualCondition d.1.1 (.inl x) (d.forget.val (.inl x)) at hv
    rw [hi] at hv
    change d.1.1 x=none at hv
    rw [he] at hp
    change d.1.2 y=d.1.1 x at hp
    exact (hp.trans hv).symm
  | inr z =>
    rw [he] at hp
    exact hp.symm

 theorem forget_injective : Function.Injective (forget (R:=R) (A:=A) (B:=B) (s:=s)) := by
  rintro ⟨⟨c,d⟩,e⟩ ⟨⟨c',d'⟩,e'⟩ he
  have hc := congrArg (fun e : CutBijection (probeRelation R A B s) => leftAssignment e.val) he
  have hd := congrArg (fun e : CutBijection (probeRelation R A B s) => rightAssignment e.val) he
  dsimp only at hc hd
  rw [leftAssignment_forget,leftAssignment_forget] at hc
  rw [rightAssignment_forget,rightAssignment_forget] at hd
  dsimp at hc hd
  subst c'
  subst d'
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun t : CutBijection (probeRelation R A B s) => t.val) he
end ProbeDecomposition

/-- Extract the canonical decomposition by reading the actual matching partners. -/
def decomposeProbe {R : X → Y → Prop} {A : I → X → Prop} {B : I → Y → Prop} {s : ℕ}
    (e : CutBijection (probeRelation R A B s)) : ProbeDecomposition R A B s := by
  refine ⟨(leftAssignment e.val,rightAssignment e.val),⟨⟨e.val,?_⟩,assignment_preserved e⟩⟩
  intro v
  refine ⟨e.property v,?_⟩
  cases v with
  | inl x =>
    cases he : e.val (.inl x) with
    | inl y => simp [residualCondition,leftAssignment,he]
    | inr y => trivial
  | inr x => cases e.val (.inr x) <;> trivial

/-- Every simple unweighted probe matching is recovered uniquely from its decomposition. -/
def probeDecompositionEquiv (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (s : ℕ) : CutBijection (probeRelation R A B s) ≃ ProbeDecomposition R A B s where
  toFun := decomposeProbe
  invFun := ProbeDecomposition.forget
  left_inv e := by rfl
  right_inv d := by apply ProbeDecomposition.forget_injective; rfl

noncomputable def probePerfectDecompositionEquiv (R : X → Y → Prop)
    (A : I → X → Prop) (B : I → Y → Prop) (s : ℕ) :
    PerfectMatching (probeGraph R A B s) ≃ ProbeDecomposition R A B s :=
  (probePerfectMatchingEquiv R A B s).trans (probeDecompositionEquiv R A B s)

end HiddenCircuits.GraphReduction
