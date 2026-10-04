import HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
namespace HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
structure RepairCode (n d : ℕ) where
  column : Fin d → Option (Fin n)
  first : Fin d → Fin n
  second : Fin d → Fin n
  deriving DecidableEq, Fintype
noncomputable def RepairCode.decode {n d : ℕ} (code : RepairCode n d)
    (z w : Equiv.Perm (Fin n)) (i : Fin n) : Set (Fin n) := by
  classical
  exact if h : ∃ j, code.column j=some i then
    {code.first h.choose,code.second h.choose}
  else {z i,w i}
theorem RepairCode.card (n d : ℕ) :
    Fintype.card (RepairCode n d)=(n+1)^d*n^d*n^d := by
  rw [Fintype.card_congr (show RepairCode n d ≃
      (Fin d → Option (Fin n)) × (Fin d → Fin n) × (Fin d → Fin n) from
    { toFun := fun c => (c.column,c.first,c.second)
      invFun := fun c => ⟨c.1,c.2.1,c.2.2⟩
      left_inv := by intro c; cases c; rfl
      right_inv := by intro c; rfl })]
  simp [mul_assoc]
noncomputable def encodeRepair {n d : ℕ} (fallback : Fin n)
    (p q : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (hS : S.card ≤ d) : RepairCode n d where
  column j := if h : j.val<S.card then some (S.orderIsoOfFin rfl ⟨j.val,h⟩).val else none
  first j := if h : j.val<S.card then p (S.orderIsoOfFin rfl ⟨j.val,h⟩).val else fallback
  second j := if h : j.val<S.card then q (S.orderIsoOfFin rfl ⟨j.val,h⟩).val else fallback
private theorem encodeRepair_slot {n d : ℕ} (fallback : Fin n)
    (p q : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (hS : S.card ≤ d)
    (j : Fin d) (i : Fin n) (h : (encodeRepair fallback p q S hS).column j=some i) :
    i∈S ∧ (encodeRepair fallback p q S hS).first j=p i ∧
      (encodeRepair fallback p q S hS).second j=q i := by
  unfold encodeRepair at h ⊢
  dsimp only at h ⊢
  split_ifs at h with hj
  · have he := Option.some.inj h
    refine ⟨he ▸ (S.orderIsoOfFin rfl ⟨j.val,hj⟩).property,?_,?_⟩ <;> simp [hj,he]
private theorem encodeRepair_present {n d : ℕ} (fallback : Fin n)
    (p q : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (hS : S.card ≤ d)
    (i : Fin n) (hi : i∈S) : ∃ j, (encodeRepair fallback p q S hS).column j=some i := by
  let t := (S.orderIsoOfFin rfl).symm ⟨i,hi⟩
  let j : Fin d := ⟨t.val,by have h := t.isLt; omega⟩
  refine ⟨j,?_⟩
  have ht := (S.orderIsoOfFin rfl).apply_symm_apply ⟨i,hi⟩
  simp only [encodeRepair,show j.val<S.card from t.isLt,↓reduceDIte]
  exact congrArg (fun x : S => some x.val) ht
theorem encodeRepair_correct {n d : ℕ} (fallback : Fin n)
    (p q z w : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (hS : S.card ≤ d)
    (hout : ∀ i, i∉S → ({p i,q i} : Set (Fin n))={z i,w i}) :
    ∀ i, (encodeRepair fallback p q S hS).decode z w i=({p i,q i} : Set (Fin n)) := by
  intro i
  unfold RepairCode.decode
  split_ifs with h
  · have hs := encodeRepair_slot fallback p q S hS h.choose i h.choose_spec
    rw [hs.2.1,hs.2.2]
  · have hi : i∉S := by
      intro hi
      exact h (encodeRepair_present fallback p q S hS i hi)
    exact (hout i hi).symm
theorem sameUnion_of_equal_code {n d : ℕ} (fallback : Fin n)
    (p q r s z w : Equiv.Perm (Fin n)) (S T : Finset (Fin n)) (hS : S.card ≤ d) (hT : T.card ≤ d)
    (hpq : ∀ i, i∉S → ({p i,q i} : Set (Fin n))={z i,w i})
    (hrs : ∀ i, i∉T → ({r i,s i} : Set (Fin n))={z i,w i})
    (hcode : encodeRepair fallback p q S hS=encodeRepair fallback r s T hT) : SameUnion p q r s := by
  intro i
  rw [← encodeRepair_correct fallback p q z w S hS hpq i,
    ← encodeRepair_correct fallback r s z w T hT hrs i,hcode]
end HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
