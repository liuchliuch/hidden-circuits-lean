import HiddenCircuits.GraphReduction.ProbeFibers

/-! The canonical matching fibers are the residual original matching and one independent
complete probe extension per color. No attachment sets are assumed disjoint. -/
namespace HiddenCircuits.GraphReduction
variable {X Y I : Type*}

def ValidAssignments (A : I → X → Prop) (B : I → Y → Prop)
    (cd : (X → Option I) × (Y → Option I)) : Prop :=
  (∀ x i, cd.1 x=some i → A i x) ∧ (∀ y i, cd.2 y=some i → B i y)

def Assignments (A : I → X → Prop) (B : I → Y → Prop) :=
  {cd : (X → Option I) × (Y → Option I) // ValidAssignments A B cd}

abbrev OriginalFiber (c : X → Option I) (i : Option I) := {x // c x=i}

def OriginalResidual (R : X → Y → Prop) (cd : (X → Option I) × (Y → Option I)) :=
  CutBijection (fun (x : OriginalFiber cd.1 none) (y : OriginalFiber cd.2 none) => R x.val y.val)

def ProbeFiberCut (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (s : ℕ) (cd : (X → Option I) × (Y → Option I)) (i : Option I) :=
  CutBijection (fun (v : {v // extendColor cd.1 s v=i})
    (w : {w // extendColor cd.2 s w=i}) => refinedProbeRelation R A B s cd.1 v.val w.val)

/-- Exact reindexing of the residual fiber to the actual original cut edges. -/
def probeNoneCutEquiv (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (s : ℕ) (cd : (X → Option I) × (Y → Option I)) :
    OriginalResidual R cd ≃ ProbeFiberCut R A B s cd none :=
  cutBijectionCongr _ _ (probeNoneFiberEquiv cd.1 s).symm
    (probeNoneFiberEquiv cd.2 s).symm (by
      intro x y
      change R x.val y.val ↔ R x.val y.val ∧ cd.1 x.val=none
      exact ⟨fun h => ⟨h,x.property⟩,fun h => h.1⟩)

/-- Exact reindexing of a probe fiber to its independently counted local extension. -/
def probeSomeCutEquiv (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (s : ℕ) (cd : Assignments A B) (i : I) :
    ProbePairBijection (OriginalFiber cd.val.1 (some i))
      (OriginalFiber cd.val.2 (some i)) (Fin s) ≃ ProbeFiberCut R A B s cd.val (some i) :=
  (noOriginalCutEquiv _ _ _).symm.trans
    (cutBijectionCongr _ _ (probeSomeFiberEquiv cd.val.1 s i).symm
      (probeSomeFiberEquiv cd.val.2 s i).symm (by
        intro x y
        cases x with
        | inl x =>
          cases y with
          | inl y =>
            change False ↔ R x.val y.val ∧ cd.val.1 x.val=none
            simp [x.property]
          | inr j =>
            change True ↔ A i x.val ∧ True
            simp [cd.property.1 x.val i x.property]
        | inr j =>
          cases y with
          | inl y =>
            change True ↔ B i y.val ∧ True
            simp [cd.property.2 y.val i y.property]
          | inr k => change True ↔ i=i ∧ True; simp))

/-- Explicit independent data for a valid original assignment. -/
def ProbeBlocks (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (s : ℕ) (cd : Assignments A B) :=
  OriginalResidual R cd.val ×
    ∀ i, ProbePairBijection (OriginalFiber cd.val.1 (some i))
      (OriginalFiber cd.val.2 (some i)) (Fin s)

noncomputable def probeBlocksEquiv (R : X → Y → Prop) (A : I → X → Prop)
    (B : I → Y → Prop) (s : ℕ) (cd : Assignments A B) :
    ColoredCutBijection (refinedProbeRelation R A B s cd.val.1)
      (extendColor cd.val.1 s) (extendColor cd.val.2 s) ≃ ProbeBlocks R A B s cd :=
  (coloredCutBijectionEquiv _ _ _).trans
    (Equiv.piOptionEquivProd.trans
      (Equiv.prodCongr (probeNoneCutEquiv R A B s cd.val).symm
        (Equiv.piCongrRight (fun i => (probeSomeCutEquiv R A B s cd i).symm))))

 theorem decomposition_valid {R : X → Y → Prop} {A : I → X → Prop} {B : I → Y → Prop}
    {s : ℕ} (d : ProbeDecomposition R A B s) : ValidAssignments A B d.1 := by
  constructor
  · intro x i h
    apply leftAssignment_allowed d.forget x i
    rw [d.leftAssignment_forget]
    exact h
  · intro y i h
    apply rightAssignment_allowed d.forget y i
    rw [d.rightAssignment_forget]
    exact h

/-- Validity is extracted from actual edges, rather than supplied as an oracle premise. -/
def validDecompositionEquiv (R : X → Y → Prop) (A : I → X → Prop)
    (B : I → Y → Prop) (s : ℕ) :
    ProbeDecomposition R A B s ≃
      Σ cd : Assignments A B, ColoredCutBijection (refinedProbeRelation R A B s cd.val.1)
        (extendColor cd.val.1 s) (extendColor cd.val.2 s) where
  toFun d := ⟨⟨d.1,decomposition_valid d⟩,d.2⟩
  invFun d := ⟨d.1.val,d.2⟩
  left_inv d := rfl
  right_inv d := rfl

/-- The complete combinatorial decomposition of the actual simple probe graph. -/
noncomputable def probePerfectBlocksEquiv (R : X → Y → Prop) (A : I → X → Prop)
    (B : I → Y → Prop) (s : ℕ) :
    PerfectMatching (probeGraph R A B s) ≃ Σ cd : Assignments A B, ProbeBlocks R A B s cd :=
  (probePerfectDecompositionEquiv R A B s).trans
    ((validDecompositionEquiv R A B s).trans
      (Equiv.sigmaCongrRight (probeBlocksEquiv R A B s)))

end HiddenCircuits.GraphReduction
