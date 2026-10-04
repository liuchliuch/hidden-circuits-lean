import HiddenCircuits.Approximation.Initialization.MaskEnumeration
import HiddenCircuits.Approximation.Initialization.ResidualTest

/-! The literal mask scan emits exactly the inherited increasing
enumeration used by the residual Tutte experiment. -/
namespace HiddenCircuits.Approximation.Initialization.MaskEnumerationSemantics
open Complexity MaskEnumeration

theorem mem_indices (i j : ℕ) (xs : BitString) :
    j ∈ indices i xs ↔ ∃ k : Fin xs.length, xs[k] = true ∧ j = i+k.val := by
  induction xs generalizing i with
  | nil => simp [indices]
  | cons b bs ih =>
    cases b <;> simp [indices,ih,Fin.exists_fin_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem indices_lower {i j : ℕ} {xs : BitString} (h : j ∈ indices i xs) : i ≤ j := by
  obtain ⟨k,_,rfl⟩ := (mem_indices i j xs).mp h
  omega

theorem indices_sorted (i : ℕ) (xs : BitString) : (indices i xs).Pairwise (· < ·) := by
  induction xs generalizing i with
  | nil => simp [indices]
  | cons b bs ih =>
    cases b with
    | false => exact ih (i+1)
    | true =>
      apply List.pairwise_cons.mpr
      exact ⟨fun j hj => lt_of_lt_of_le (Nat.lt_succ_self i) (indices_lower hj),ih (i+1)⟩

theorem indices_mask {n : ℕ} (U : Finset (Fin n)) :
    indices 0 (mask U) = (U.sort).map Fin.val := by
  apply (indices_sorted 0 (mask U)).eq_of_mem_iff
  · exact U.sortedLT_sort.pairwise.map Fin.val (fun a b h => h)
  · intro j
    rw [mem_indices]
    constructor
    · rintro ⟨k,hk,hj⟩
      have hkn : k.val < n := by simpa using k.isLt
      have hm : (⟨k.val,hkn⟩ : Fin n) ∈ U := by
        change (List.ofFn (fun i : Fin n => decide (i ∈ U)))[k.val] = true at hk
        simpa only [List.getElem_ofFn,decide_eq_true_eq] using hk
      apply List.mem_map.mpr
      exact ⟨⟨k.val,hkn⟩, by simpa using hm, by simpa using hj.symm⟩
    · intro h
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
      refine ⟨⟨v.val,by simpa using v.isLt⟩,?_,by simp⟩
      simpa [mask] using (show v ∈ U by simpa using hv)

theorem words_mask {n : ℕ} (U : Finset (Fin n)) :
    words 0 (mask U) = List.ofFn (fun i : Fin U.card => unary (ResidualTest.vertex U i).val) := by
  rw [words,indices_mask,List.map_map]
  rw [←U.listMap_orderEmbOfFin_finRange rfl]
  simp only [List.map_map]
  rw [←List.ofFn_eq_map]
  rfl

theorem count_mask {n : ℕ} (U : Finset (Fin n)) : (mask U).count true = U.card := by
  have hlen : ∀ i xs, (indices i xs).length = xs.count true := by
    intro i xs
    induction xs generalizing i with
    | nil => rfl
    | cons b bs ih => cases b <;> simp [indices,ih]
  rw [←hlen 0 (mask U),indices_mask]
  simp

theorem program_retained (g : BitString → ℕ) {n : ℕ} (U : Finset (Fin n)) :
    ∃ t, MaskEnumeration.program.Executes g (MaskEnumeration.state (mask U) [] [] [] [] [] [])
      (MaskEnumeration.state (mask U) (unary U.card) [] []
        (encodeBitList (List.ofFn (fun i : Fin U.card => unary (ResidualTest.vertex U i).val))) [] []) t ∧
      t ≤ 55*(n+1)^2 := by
  simpa only [count_mask,words_mask,mask_length] using MaskEnumeration.program_executes g (mask U)

end HiddenCircuits.Approximation.Initialization.MaskEnumerationSemantics
