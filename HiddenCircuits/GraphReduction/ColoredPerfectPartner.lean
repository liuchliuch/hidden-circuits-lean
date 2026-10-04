import HiddenCircuits.PerfectPartners

/-! Actual undirected perfect matchings restrict and glue across vertex-color fibers. -/
namespace HiddenCircuits.GraphReduction
variable {V I : Type*}

def ColoredPerfectPartner (G : SimpleGraph V) (c : V → I) :=
  {p : PerfectPartner G // ∀ v, c (p.val v)=c v}

namespace ColoredPerfectPartner
variable {G : SimpleGraph V} {c : V → I}

def restrict (p : ColoredPerfectPartner G c) (i : I) :
    PerfectPartner (G.induce {v | c v=i}) := by
  refine ⟨fun v => ⟨p.val.val v.val,(p.property v.val).trans v.property⟩,?_,?_⟩
  · intro v
    exact Subtype.ext (p.val.property.1 v.val)
  · intro v
    exact p.val.property.2 v.val

/-- Assemble an involution independently on each genuine graph fiber. -/
def glue (p : ∀ i, PerfectPartner (G.induce {v | c v=i})) : ColoredPerfectPartner G c := by
  let q : (Σ i, {v // c v=i}) → (Σ i, {v // c v=i}) := fun x => ⟨x.1,(p x.1).val x.2⟩
  have hq : Function.Involutive q := by
    rintro ⟨i,v⟩
    change (⟨i, (p i).val ((p i).val v)⟩ : Σ i, {v // c v=i}) = ⟨i,v⟩
    rw [(p i).property.1 v]
  let e := Equiv.sigmaFiberEquiv c
  let f : V → V := fun v => e (q (e.symm v))
  refine ⟨⟨f,?_,?_⟩,?_⟩
  · intro v
    change e (q (e.symm (e (q (e.symm v)))))=v
    rw [e.symm_apply_apply,hq,e.apply_symm_apply]
  · intro v
    exact (p (c v)).property.2 ⟨v,rfl⟩
  · intro v
    exact ((p (c v)).val ⟨v,rfl⟩).property

 theorem glue_restrict (p : ColoredPerfectPartner G c) : glue p.restrict=p := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  rfl

 theorem restrict_glue (p : ∀ i, PerfectPartner (G.induce {v | c v=i})) :
    (glue p).restrict=p := by
  funext i
  apply Subtype.ext
  funext v
  rcases v with ⟨v,hv⟩
  subst i
  rfl
end ColoredPerfectPartner

/-- Complete two-sided undirected matching decomposition, not merely a counting assumption. -/
def coloredPerfectPartnerEquiv (G : SimpleGraph V) (c : V → I) :
    ColoredPerfectPartner G c ≃ ∀ i, PerfectPartner (G.induce {v | c v=i}) where
  toFun := ColoredPerfectPartner.restrict
  invFun := ColoredPerfectPartner.glue
  left_inv := ColoredPerfectPartner.glue_restrict
  right_inv := ColoredPerfectPartner.restrict_glue

/-- Relabeling vertices transports actual partner involutions and all their graph edges. -/
def perfectPartnerCongr {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (e : V ≃ W)
    (he : ∀ v w, G.Adj v w ↔ H.Adj (e v) (e w)) : PerfectPartner G ≃ PerfectPartner H where
  toFun p := ⟨fun w => e (p.val (e.symm w)),by
    intro w
    simp only [e.symm_apply_apply]
    rw [p.property.1 (e.symm w),e.apply_symm_apply],by
    intro w
    simpa only [e.apply_symm_apply] using (he _ _).mp (p.property.2 (e.symm w))⟩
  invFun p := ⟨fun v => e.symm (p.val (e v)),by
    intro v
    simp only [e.apply_symm_apply]
    rw [p.property.1 (e v),e.symm_apply_apply],by
    intro v
    apply (he _ _).mpr
    simpa only [e.apply_symm_apply] using p.property.2 (e v)⟩
  left_inv p := by apply Subtype.ext; funext v; simp
  right_inv p := by apply Subtype.ext; funext v; simp

end HiddenCircuits.GraphReduction
