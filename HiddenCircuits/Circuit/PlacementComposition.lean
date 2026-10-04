import HiddenCircuits.Circuit.Placement

/-! Exact coherence of nested concrete logical interval placements. -/
namespace HiddenCircuits.Circuit
open scoped Kronecker
variable {n r d : ℕ}

def Placement.compose (p : Placement n r) (q : Placement r d) : Placement n d where
  before := p.before+q.before
  after := q.after+p.after
  size := by have hp := p.size; have hq := q.size; omega

lemma placement_raw_hasTrack (p : Placement n d)
    (x : CodeBits p.before × (CodeBits d × CodeBits p.after)) (t : ℕ) :
    (rawCode n (p.equiv x)).HasTrack t ↔
      (rawCode p.before x.1).HasTrack t ∨ blockWidth p.before≤t ∧
        ((rawCode d x.2.1).HasTrack (t-blockWidth p.before) ∨
          blockWidth d≤t-blockWidth p.before ∧
            (rawCode p.after x.2.2).HasTrack ((t-blockWidth p.before)-blockWidth d)) := by
  change (rawCode n (cast (congrArg CodeBits p.size)
    (codeConcat p.before (d+p.after) x.1 (codeConcat d p.after x.2.1 x.2.2)))).HasTrack t ↔ _
  rw [rawCode_cast_hasTrack p.size]
  simp_rw [rawCode_concat_hasTrack]

/-- The nested and composed coordinate maps agree on every actual logical bit tuple. -/
theorem Placement.equiv_compose (p : Placement n r) (q : Placement r d)
    (a : CodeBits p.before) (b : CodeBits q.before) (x : CodeBits d)
    (c : CodeBits q.after) (e : CodeBits p.after) :
    p.equiv (a,(q.equiv (b,(x,c)),e)) =
      (p.compose q).equiv (codeConcat p.before q.before a b,(x,codeConcat q.after p.after c e)) := by
  apply rawCode_injective n
  apply State.ext_hasTrack
  intro t
  simp_rw [placement_raw_hasTrack]
  simp only [Placement.compose]
  simp_rw [rawCode_concat_hasTrack]
  have hr : blockWidth r = blockWidth q.before+(blockWidth d+blockWidth q.after) := by
    simpa only [blockWidth_add] using (congrArg blockWidth q.size).symm
  rw [hr]
  simp only [blockWidth_add,Nat.sub_sub,Nat.add_assoc]
  have h1 : blockWidth p.before≤t ∧ blockWidth q.before≤t-blockWidth p.before ↔
      blockWidth p.before+blockWidth q.before≤t := by omega
  have h2 : blockWidth p.before≤t ∧
      blockWidth q.before+(blockWidth d+blockWidth q.after)≤t-blockWidth p.before ↔
      blockWidth p.before+blockWidth q.before≤t ∧
        blockWidth d≤t-(blockWidth p.before+blockWidth q.before) ∧
        blockWidth q.after≤t-(blockWidth p.before+(blockWidth q.before+blockWidth d)) := by omega
  tauto

lemma codeConcat_eq_iff (a b : ℕ) (x x' : CodeBits a) (y y' : CodeBits b) :
    codeConcat a b x y = codeConcat a b x' y' ↔ x=x' ∧ y=y' := by
  change codeConcatEquiv a b (x,y) = codeConcatEquiv a b (x',y') ↔ _
  rw [(codeConcatEquiv a b).injective.eq_iff,Prod.mk.injEq]

lemma Placement.lift_equiv_entry {R : Type*} [Semiring R]
    (p : Placement n d) (A : Matrix (CodeBits d) (CodeBits d) R)
    (x y : CodeBits p.before × (CodeBits d × CodeBits p.after)) :
    p.lift A (p.equiv x) (p.equiv y) =
      (if x.1=y.1 then 1 else 0) * (A x.2.1 y.2.1 * (if x.2.2=y.2.2 then 1 else 0)) := by
  simp only [Placement.lift,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    Matrix.kroneckerMap_apply,Matrix.one_apply]

/-- Placing a tensor-local gate inside another actual interval is its direct placement. -/
theorem Placement.lift_compose {R : Type*} [Semiring R]
    (p : Placement n r) (q : Placement r d) (A : Matrix (CodeBits d) (CodeBits d) R) :
    p.lift (q.lift A) = (p.compose q).lift A := by
  ext s t
  obtain ⟨⟨a,⟨u,e⟩⟩,rfl⟩ := p.equiv.surjective s
  obtain ⟨⟨b,⟨x,c⟩⟩,rfl⟩ := q.equiv.surjective u
  obtain ⟨⟨a',⟨u',e'⟩⟩,rfl⟩ := p.equiv.surjective t
  obtain ⟨⟨b',⟨x',c'⟩⟩,rfl⟩ := q.equiv.surjective u'
  have hs := p.equiv_compose q a b x c e
  have ht := p.equiv_compose q a' b' x' c' e'
  rw [Placement.lift_equiv_entry,Placement.lift_equiv_entry]
  conv_rhs => rw [hs,ht,Placement.lift_equiv_entry]
  simp only [Prod.fst,Prod.snd]
  have hpre : codeConcat p.before q.before a b = codeConcat p.before q.before a' b' ↔ a=a' ∧ b=b' :=
    codeConcat_eq_iff _ _ _ _ _ _
  have hpost : codeConcat q.after p.after c e = codeConcat q.after p.after c' e' ↔ c=c' ∧ e=e' :=
    codeConcat_eq_iff _ _ _ _ _ _
  simp only [hpre,hpost]
  by_cases ha : a=a' <;> by_cases hb : b=b' <;> by_cases hc : c=c' <;> by_cases he : e=e' <;>
    simp [ha,hb,hc,he,codeConcat_eq_iff]

end HiddenCircuits.Circuit
