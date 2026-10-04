import HiddenCircuits.Complexity.GridTermRuntime
import HiddenCircuits.Complexity.SourceAlgorithm

/-! Bit bounds for every actual partial grid sum, not only the final answer.
Repeated indices are allowed in the list lemma, so the runtime invariant does
not rely on silently treating a list as a duplicate-free finite set. -/
namespace HiddenCircuits.Complexity
open BinaryArithmetic BinaryArithmetic.RegisterMachine

lemma int_list_sum_natAbs (zs : List ℤ) : zs.sum.natAbs ≤ (zs.map Int.natAbs).sum := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    simpa using (Int.natAbs_add_le z zs.sum).trans (Nat.add_le_add_left ih z.natAbs)

lemma int_list_sum_envelope (zs : List ℤ) (E : ℕ) (h : ∀ z∈zs, z.natAbs≤2^E) :
    zs.sum.natAbs≤2^(E+zs.length) := by
  have hm : (zs.map Int.natAbs).sum≤zs.length*2^E := by
    induction zs with
    | nil => simp
    | cons z zs ih =>
      have hz := h z (by simp)
      have ht := ih (fun w hw => h w (by simp [hw]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  calc
    _ ≤ zs.length*2^E := (int_list_sum_natAbs zs).trans hm
    _ ≤ 2^zs.length*2^E := Nat.mul_le_mul_right _
      ((Nat.le_succ zs.length).trans (HiddenCircuits.succ_le_two_pow zs.length))
    _ = _ := by rw [←pow_add,Nat.add_comm]

def gridPartialSum (dx dy : ℕ) (values : Fin (dx+1) → Fin (dy+1) → ℤ)
    (indices : List (Fin (dx+1) × Fin (dy+1))) : ℤ :=
  (indices.map (fun ij => gridTerm dx dy ij.1 ij.2 (values ij.1 ij.2))).sum

lemma gridPartialSum_envelope (dx dy B : ℕ) (values : Fin (dx+1) → Fin (dy+1) → ℤ)
    (hv : ∀ i j, (values i j).natAbs≤2^B)
    (indices : List (Fin (dx+1) × Fin (dy+1)))
    (hlen : indices.length≤(dx+1)*(dy+1)) :
    (gridPartialSum dx dy values indices).natAbs≤2^(numeratorExponent dx dy B) := by
  have h := int_list_sum_envelope (indices.map (fun ij => gridTerm dx dy ij.1 ij.2 (values ij.1 ij.2)))
    (B+(dy^2+1)+denominatorExponent dx dy) (by
      intro z hz
      obtain ⟨⟨i,j⟩,hij,rfl⟩ := List.mem_map.mp hz
      exact gridTerm_envelope dx dy B i j (values i j) (hv i j))
  apply h.trans
  apply Nat.pow_le_pow_right (by decide)
  simp only [List.length_map,numeratorExponent]
  omega

namespace CNFInput

def gridRegisterBound (L : ℕ) : ℕ := 8*(L+1)^3

theorem grid_registers_bounded (F : CNFInput) (i : Fin (F.1+1)) (j : Fin (F.2.1+1))
    (indices : List (Fin (F.1+1) × Fin (F.2.1+1)))
    (hlen : indices.length≤(F.1+1)*(F.2.1+1)) :
    Bounded (gridRegisterBound (encode F).length)
      (GridTermRuntime.registers (gridDenominator F.1 F.2.1) (interpolationDenominator F.1 i)
        (interpolationDenominator F.2.1 j) (interpolationNegativeNumerator F.2.1 j)
        (GraphInput.independentSetProblem (F.2.2.encodedCloneQuery i.val j.val))
        (gridPartialSum F.1 F.2.1 (fun a b => (F.2.2.cloneCount a.val b.val : ℤ)) indices) 0) := by
  let L := (encode F).length
  have hL := encode_length_lower F
  have hn : F.1≤L := by dsimp [L];omega
  have hm : F.2.1≤L := by dsimp [L];omega
  have he := interpolation_exponents_in_source_bits F
  have hD := signedBits_length_of_abs_bound (gridDenominator_envelope F.1 F.2.1)
  have hi := (interpolation_weights_bit_bound F.1 i).1
  have hj := interpolation_weights_bit_bound F.2.1 j
  have hval : (F.2.2.cloneCount i.val j.val : ℤ).natAbs≤2^((2*F.1+F.2.1)^2+1) := by
    simpa using F.2.2.cloneCount_grid_envelope i j
  have hv := signedBits_length_of_abs_bound hval
  have ha := signedBits_length_of_abs_bound (gridPartialSum_envelope F.1 F.2.1 ((2*F.1+F.2.1)^2+1)
    (fun a b => (F.2.2.cloneCount a.val b.val : ℤ))
    (fun a b => by simpa using F.2.2.cloneCount_grid_envelope a b) indices hlen)
  have hns : F.1^2≤L^2 := Nat.pow_le_pow_left hn 2
  have hms : F.2.1^2≤L^2 := Nat.pow_le_pow_left hm 2
  have hs : (2*F.1+F.2.1)^2+1≤(L+1)^2 := by
    have ht : 2*F.1+F.2.1+1≤L := hL
    nlinarith
  have h23 : (L+1)^2≤(L+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have h03 : 1≤(L+1)^3 := Nat.one_le_pow _ _ (by omega)
  have h33 : L^3≤(L+1)^3 := Nat.pow_le_pow_left (by omega) 3
  have hdi : (signedBits (interpolationDenominator F.1 i)).length≤F.1^2+2 := by
    simp only [signedBits,List.length_cons,encodeNat_length];omega
  have hdj : (signedBits (interpolationDenominator F.2.1 j)).length≤F.2.1^2+2 := by
    simp only [signedBits,List.length_cons,encodeNat_length];omega
  have hnu : (signedBits (interpolationNegativeNumerator F.2.1 j)).length≤F.2.1^2+2 := by
    simp only [signedBits,List.length_cons,encodeNat_length];omega
  have hz : (signedBits 0).length=1 := rfl
  have hLL : L^2≤(L+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hsmall : L^2+2≤gridRegisterBound L := by
    unfold gridRegisterBound
    nlinarith only [hLL,h23,h03]
  have hsmall' : (L+1)^2+2≤gridRegisterBound L := by
    unfold gridRegisterBound
    nlinarith only [h23,h03]
  have hdmax : denominatorExponent F.1 F.2.1+2≤gridRegisterBound L := by
    have hh : denominatorExponent F.1 F.2.1≤2*L^3 := he.1
    unfold gridRegisterBound
    nlinarith only [hh,h33,h03]
  have hamax : numeratorExponent F.1 F.2.1 ((2*F.1+F.2.1)^2+1)+2≤gridRegisterBound L := by
    have hh : numeratorExponent F.1 F.2.1 ((2*F.1+F.2.1)^2+1)≤5*L^3 := he.2
    unfold gridRegisterBound
    nlinarith only [hh,h33,h03]
  apply GridTermRuntime.registers_bounded
  · exact hD.trans hdmax
  · exact hdi.trans ((Nat.add_le_add_right hns 2).trans hsmall)
  · exact hdj.trans ((Nat.add_le_add_right hms 2).trans hsmall)
  · exact hnu.trans ((Nat.add_le_add_right hms 2).trans hsmall)
  · rw [CNF.encodedCloneQuery_correct]
    exact hv.trans ((Nat.add_le_add_right hs 2).trans hsmall')
  · exact ha.trans hamax
  · rw [hz]
    unfold gridRegisterBound
    nlinarith only [h03]

end CNFInput
end HiddenCircuits.Complexity
