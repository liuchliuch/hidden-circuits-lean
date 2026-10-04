import HiddenCircuits.LayerCutBoundary

namespace HiddenCircuits

/-- Relabel both selected sides of a genuine allowed-edge bijection. -/
def CutBijection.reindex {α β γ δ : Type*} (R : α → β → Prop) (ea : γ ≃ α) (eb : δ ≃ β) :
    CutBijection R ≃ CutBijection (fun x y => R (ea x) (eb y)) where
  toFun e := ⟨ea.trans (e.val.trans eb.symm),by
    intro x
    simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using e.property (ea x)⟩
  invFun e := ⟨ea.symm.trans (e.val.trans eb),by
    intro x
    simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using e.property (ea.symm x)⟩
  left_inv e := by apply Subtype.ext; apply Equiv.ext; intro x; simp
  right_inv e := by apply Subtype.ext; apply Equiv.ext; intro x; simp

namespace Layered
open HiddenCircuits.DH
namespace CutStep
variable {p : ℕ} {R : UnweightedCut p} {S U : State (2*p) p}

noncomputable def toBijection (e : CutStep R S U) :
    CutBijection (fun x : S.val => fun y : U.halfComplement.val => R x.val y.val = true) := by
  let l : S.val ≃ e.val.leftDomain :=
    Equiv.subtypeEquivRight (fun x => by rw [e.property.1])
  let r : e.val.rightDomain ≃ U.halfComplement.val :=
    Equiv.subtypeEquivRight (fun x => by rw [e.property.2.1])
  refine ⟨l.trans (e.val.domainEquiv.trans r),?_⟩
  intro x
  exact e.property.2.2 x.val _ (e.val.left_leftValue (l x))

 theorem toBijection_spec (e : CutStep R S U) (x : S.val) :
    e.val.left x.val = some (e.toBijection.val x).val :=
  e.val.left_leftValue
    ((Equiv.subtypeEquivRight (fun z => by rw [e.property.1]) : S.val ≃ e.val.leftDomain) x)

noncomputable def ofBijection
    (e : CutBijection (fun x : S.val => fun y : U.halfComplement.val => R x.val y.val = true)) :
    CutStep R S U := by
  refine ⟨PartialPairs.ofEquiv S.val U.halfComplement.val e.val,
    PartialPairs.ofEquiv_leftDomain ..,PartialPairs.ofEquiv_rightDomain ..,?_⟩
  intro x y h
  change (if hx : x ∈ S.val then some (e.val ⟨x,hx⟩).val else none) = some y at h
  split_ifs at h with hx
  have he := Option.some.inj h
  rw [← he]
  exact e.property ⟨x,hx⟩

 theorem of_toBijection (e : CutStep R S U) : ofBijection e.toBijection = e := by
  apply Subtype.ext
  apply PartialPairs.ext_left
  funext x
  change (if hx : x ∈ S.val then some (e.toBijection.val ⟨x,hx⟩).val else none) = e.val.left x
  split_ifs with hx
  · exact (e.toBijection_spec ⟨x,hx⟩).symm
  · have hn : e.val.left x=none := by
      by_contra hn
      have hm := (pair_mem_leftDomain_ne e.val x).mpr hn
      rw [e.property.1] at hm
      exact hx hm
    exact hn.symm

 theorem to_ofBijection
    (e : CutBijection (fun x : S.val => fun y : U.halfComplement.val => R x.val y.val = true)) :
    (ofBijection e).toBijection = e := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  have hh := (ofBijection e).toBijection_spec x
  change (if hx : x.val ∈ S.val then some (e.val ⟨x.val,hx⟩).val else none) = _ at hh
  rw [dif_pos x.property] at hh
  exact (Option.some.inj hh).symm

noncomputable def bijectionEquiv (R : UnweightedCut p) (S U : State (2*p) p) :
    CutStep R S U ≃
      CutBijection (fun x : S.val => fun y : U.halfComplement.val => R x.val y.val = true) where
  toFun := toBijection
  invFun := ofBijection
  left_inv := of_toBijection
  right_inv := to_ofBijection

/-- The graph-level crossing pairs correspond exactly to the permanent's selected permutation. -/
noncomputable def permutationEquiv (R : UnweightedCut p) (S U : State (2*p) p) :
    CutStep R S U ≃ CutPermutation R S U :=
  (bijectionEquiv R S U).trans
    ((CutBijection.reindex (fun x : S.val => fun y : U.halfComplement.val => R x.val y.val = true)
      (S.val.orderIsoOfFin S.property).toEquiv
      (U.halfComplement.val.orderIsoOfFin U.halfComplement.property).toEquiv).trans
        (cutPermutationEquiv (fun i j => R (S.track i) (U.halfComplement.track j) = true)).symm)

 theorem card (R : UnweightedCut p) (S U : State (2*p) p) :
    (Fintype.card (CutStep R S U) : ℚ) = layerTransfer (cutMatrix R) S U := by
  rw [Fintype.card_congr (permutationEquiv R S U)]
  exact cutPermutation_card R S U
end CutStep
end Layered
end HiddenCircuits
