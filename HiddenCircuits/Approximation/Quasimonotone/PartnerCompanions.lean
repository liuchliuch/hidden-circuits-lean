import HiddenCircuits.Approximation.Quasimonotone.PartnerReconstruction
import Mathlib.Data.Finset.Image
namespace HiddenCircuits.Approximation.QuasimonotoneProof
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
def HasPartnerCompanion (P Q Z : PerfectPartner G) (d : ℕ) : Prop :=
  ∃ W : PerfectPartner G, ∃ S : Finset V, S.card ≤ d ∧
    ∀ x, x∉S → ({Z.val x,W.val x} : Finset V)={P.val x,Q.val x}
private theorem inverse_pair_mem (A C D : PerfectPartner G) (x : V)
    (hx : x∈({C.val (A.val x),D.val (A.val x)} : Finset V)) :
    A.val x∈({C.val x,D.val x} : Finset V) := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢
  rcases hx with h|h
  · left
    have hh := congrArg C.val h
    rw [C.property.1 (A.val x)] at hh
    exact hh.symm
  · right
    have hh := congrArg D.val h
    rw [D.property.1 (A.val x)] at hh
    exact hh.symm
theorem profile_of_neighbor_profiles (P Q Z W : PerfectPartner G) (x : V)
    (hZ : ({Z.val (Z.val x),W.val (Z.val x)} : Finset V)={P.val (Z.val x),Q.val (Z.val x)})
    (hW : ({Z.val (W.val x),W.val (W.val x)} : Finset V)={P.val (W.val x),Q.val (W.val x)})
    (hP : ({Z.val (P.val x),W.val (P.val x)} : Finset V)={P.val (P.val x),Q.val (P.val x)})
    (hQ : ({Z.val (Q.val x),W.val (Q.val x)} : Finset V)={P.val (Q.val x),Q.val (Q.val x)}) :
    ({Z.val x,W.val x} : Finset V)={P.val x,Q.val x} := by
  apply Finset.Subset.antisymm
  · intro y hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl|rfl
    · apply inverse_pair_mem Z P Q x
      rw [← hZ,Z.property.1 x]
      simp
    · apply inverse_pair_mem W P Q x
      rw [← hW,W.property.1 x]
      simp
  · intro y hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl|rfl
    · apply inverse_pair_mem P Z W x
      rw [hP,P.property.1 x]
      simp
    · apply inverse_pair_mem Q Z W x
      rw [hQ,Q.property.1 x]
      simp
noncomputable def profileExceptions (P Q Z W : PerfectPartner G) (S : Finset V) : Finset V :=
  S ∪ S.image P.val ∪ S.image Q.val ∪ S.image Z.val ∪ S.image W.val
theorem profileExceptions_card (P Q Z W : PerfectPartner G) (S : Finset V) :
    (profileExceptions P Q Z W S).card ≤ 5*S.card := by
  unfold profileExceptions
  calc
    _ ≤ (((S.card+(S.image P.val).card)+(S.image Q.val).card)+(S.image Z.val).card)+(S.image W.val).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
          ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _)) _)
    _ ≤ 5*S.card := by
      have hp := Finset.card_image_le (s := S) (f := P.val)
      have hq := Finset.card_image_le (s := S) (f := Q.val)
      have hz := Finset.card_image_le (s := S) (f := Z.val)
      have hw := Finset.card_image_le (s := S) (f := W.val)
      omega
theorem outside_profileExceptions (P Q Z W : PerfectPartner G) (S : Finset V) {x : V}
    (hx : x∉profileExceptions P Q Z W S) :
    x∉S ∧ P.val x∉S ∧ Q.val x∉S ∧ Z.val x∉S ∧ W.val x∉S := by
  simp only [profileExceptions,Finset.mem_union,not_or] at hx
  refine ⟨hx.1.1.1.1,?_,?_,?_,?_⟩
  · intro h
    exact hx.1.1.1.2 (Finset.mem_image.mpr ⟨P.val x,h,P.property.1 x⟩)
  · intro h
    exact hx.1.1.2 (Finset.mem_image.mpr ⟨Q.val x,h,Q.property.1 x⟩)
  · intro h
    exact hx.1.2 (Finset.mem_image.mpr ⟨Z.val x,h,Z.property.1 x⟩)
  · intro h
    exact hx.2 (Finset.mem_image.mpr ⟨W.val x,h,W.property.1 x⟩)
end HiddenCircuits.Approximation.QuasimonotoneProof
