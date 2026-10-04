import HiddenCircuits.GraphReduction.ProbeDecomposition
import HiddenCircuits.GraphReduction.ProbePairBijection

/-! Literal descriptions of the residual-original and single-probe matching fibers. -/
namespace HiddenCircuits.GraphReduction
variable {X Y X' Y' I : Type*}

/-- Reindex an actual allowed cut bijection along genuine equivalences. -/
def cutBijectionCongr (R : X → Y → Prop) (R' : X' → Y' → Prop)
    (ex : X ≃ X') (ey : Y ≃ Y') (h : ∀ x y, R x y ↔ R' (ex x) (ey y)) :
    CutBijection R ≃ CutBijection R' where
  toFun e := ⟨ex.symm.trans (e.val.trans ey),fun x => by
    simpa only [Equiv.apply_symm_apply] using (h (ex.symm x) (e.val (ex.symm x))).mp (e.property _)⟩
  invFun e := ⟨ex.trans (e.val.trans ey.symm),fun x => by
    apply (h x _).mpr
    simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using e.property (ex x)⟩
  left_inv e := by apply Subtype.ext; ext x; simp
  right_inv e := by apply Subtype.ext; ext x; simp

/-- The none fiber consists exactly of unassigned original vertices. -/
def probeNoneFiberEquiv (c : X → Option I) (s : ℕ) :
    {v : ProbePart X I s // extendColor c s v=none} ≃ {x // c x=none} where
  toFun v := by
    rcases v with ⟨x|⟨i,j⟩,h⟩
    · exact ⟨x,h⟩
    · cases h
  invFun x := ⟨.inl x.val,x.property⟩
  left_inv v := by rcases v with ⟨x|⟨i,j⟩,h⟩; rfl; cases h
  right_inv x := rfl

/-- A colored fiber consists exactly of assigned originals and that pair's probe labels. -/
def probeSomeFiberEquiv (c : X → Option I) (s : ℕ) (i : I) :
    {v : ProbePart X I s // extendColor c s v=some i} ≃
      ({x // c x=some i} ⊕ Fin s) where
  toFun v := by
    rcases v with ⟨x|⟨j,k⟩,h⟩
    · exact .inl ⟨x,h⟩
    · exact .inr k
  invFun v := match v with
    | .inl x => ⟨.inl x.val,x.property⟩
    | .inr k => ⟨.inr (i,k),rfl⟩
  left_inv v := by
    rcases v with ⟨x|⟨j,k⟩,h⟩
    · rfl
    · have hi : j=i := Option.some.inj h
      subst j
      rfl
  right_inv v := by cases v <;> rfl

/-- The same relation with an arbitrary probe-label type. -/
def noOriginalRelation {P : Type*} : X ⊕ P → Y ⊕ P → Prop
  | .inl _, .inl _ => False
  | _, _ => True

/-- The no-original-edge relation is exactly the locally counted probe extension type. -/
def noOriginalCutEquiv (X Y P : Type*) :
    CutBijection (noOriginalRelation (X:=X) (Y:=Y) (P:=P)) ≃ ProbePairBijection X Y P where
  toFun e := ⟨e.val,by
    intro x
    have h := e.property (.inl x)
    cases he : e.val (.inl x) with
    | inl y => rw [he] at h; exact h.elim
    | inr p => exact ⟨p,rfl⟩⟩
  invFun e := ⟨e.val,by
    intro v
    cases v with
    | inl x => obtain ⟨p,hp⟩ := e.property x; rw [hp]; trivial
    | inr p => cases e.val (.inr p) <;> trivial⟩
  left_inv e := rfl
  right_inv e := rfl

end HiddenCircuits.GraphReduction
