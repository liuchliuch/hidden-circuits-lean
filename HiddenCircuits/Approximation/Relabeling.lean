import HiddenCircuits.Approximation.MonotoneDeletion
import HiddenCircuits.PerfectPartners
namespace HiddenCircuits.Approximation
attribute [local instance] Classical.propDecidable
theorem Quasimonotone.comap {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V}
    (hG : Quasimonotone G) (f : W → V) (hf : Function.Injective f) : Quasimonotone (G.comap f) := by
  classical
  intro S
  let A : Set V := f '' S
  letI : Fintype S := @Subtype.fintype W (fun w => w∈S) _ _
  letI : Fintype A := @Subtype.fintype V (fun v => v∈A) _ _
  let l : S → A := fun x => ⟨f x.val,⟨x.val,x.property,rfl⟩⟩
  let r : {w : W // w∉S} → {v : V // v∉A} := fun x => ⟨f x.val,by
    rintro ⟨y,hy,he⟩
    exact x.property (hf he ▸ hy)⟩
  have hl : Function.Injective l := by
    intro x y h
    exact Subtype.ext (hf (congrArg (fun z : A => z.val) h))
  have hr : Function.Injective r := by
    intro x y h
    exact Subtype.ext (hf (congrArg (fun z : {v : V // v∉A} => z.val) h))
  obtain ⟨O⟩ := hG A
  exact ⟨MonotoneRestriction.ordering O l r hl hr⟩
def relabelPartner {V W : Type*} (G : SimpleGraph V) (e : W ≃ V) :
    PerfectPartner G ≃ PerfectPartner (G.comap e) where
  toFun P := ⟨fun w => e.symm (P.val (e w)),by
    intro w
    simp only [Equiv.apply_symm_apply,P.property.1 (e w),Equiv.symm_apply_apply],by
    intro w
    change G.Adj (e w) (e (e.symm (P.val (e w))))
    simpa only [Equiv.apply_symm_apply] using P.property.2 (e w)⟩
  invFun P := ⟨fun v => e (P.val (e.symm v)),by
    intro v
    simp only [Equiv.symm_apply_apply,P.property.1 (e.symm v),Equiv.apply_symm_apply],by
    intro v
    have h := P.property.2 (e.symm v)
    change G.Adj (e (e.symm v)) (e (P.val (e.symm v))) at h
    simpa only [Equiv.apply_symm_apply] using h⟩
  left_inv P := by apply Subtype.ext; funext v; simp
  right_inv P := by apply Subtype.ext; funext w; simp
theorem relabel_count {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (e : W ≃ V) :
    Fintype.card (PerfectPartner G)=Fintype.card (PerfectPartner (G.comap e)) :=
  Fintype.card_congr (relabelPartner G e)
noncomputable def residualGraph {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V) :
    SimpleGraph (Fin (Fintype.card S)) :=
  (G.induce S).comap (Fintype.equivFin S).symm
noncomputable def residualPartnerEquiv {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V) :
    PerfectPartner (G.induce S) ≃ PerfectPartner (residualGraph G S) :=
  relabelPartner (G.induce S) (Fintype.equivFin S).symm
theorem Quasimonotone.residualGraph {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : Quasimonotone G) (S : Set V) : Quasimonotone (residualGraph G S) :=
  (hG.induce S).comap _ (Fintype.equivFin S).symm.injective
end HiddenCircuits.Approximation
