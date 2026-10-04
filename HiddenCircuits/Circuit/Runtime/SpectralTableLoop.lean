import HiddenCircuits.Circuit.Runtime.SpectralTableBody

/-! The actual runtime visits each spectral basis index in source order exactly once. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralTable
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

noncomputable def loop : OracleBlock 32 := whilePop 32 body body

theorem loop_execution (oracle : BitString → ℕ) (g j r : ℕ) (hjr : j+r≤(spectralIndices g).length)
    (count outD outA : BitString) :
    ∃ t, WhileExecution (32:Fin 33) body body oracle
      (state g j count [] [] [] [] outD outA (List.replicate r true))
      (state g (j+r) count [] [] [] []
        ((encodeBitList ((List.range' j r).map (denominatorWord g))).reverse++outD)
        ((encodeBitList ((List.range' j r).map (coefficientWord g))).reverse++outA) []) t ∧
      t≤r*(bodyTime.eval g+2)+1 := by
  induction r generalizing j outD outA with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [encodeBitList] using (WhileExecution.empty (stack:=(32:Fin 33)) (B:=body) (C:=body)
      (g:=oracle) (state g j count [] [] [] [] outD outA []) rfl)
  | succ r ih =>
    obtain ⟨c,hc,hcb⟩ := body_executes oracle g j (by omega) count outD outA (List.replicate r true)
    obtain ⟨t,ht,htb⟩ := ih (j+1) (by omega)
      ((wordChunk (denominatorWord g j)).reverse++outD) ((wordChunk (coefficientWord g j)).reverse++outA)
    have he : Function.update (state g j count [] [] [] [] outD outA (List.replicate (r+1) true)) (32:Fin 33)
        (List.replicate r true)=state g j count [] [] [] [] outD outA (List.replicate r true) := by
      funext i;fin_cases i <;> rfl
    rw [←he] at hc
    have hh := WhileExecution.one
      (show state g j count [] [] [] [] outD outA (List.replicate (r+1) true) 32=true::List.replicate r true from rfl) hc ht
    refine ⟨1+c+1+t,?_,?_⟩
    · have hn : (j+1)+r=j+(r+1) := by omega
      simpa [hn,List.range'_succ,encodeBitList_eq_chunks,List.reverse_append,List.append_assoc] using hh
    · nlinarith

 def denominators (g : ℕ) : List BitString := (spectralIndices g).map (fun i => signedBits (spectralBasisDenominator g i))
 def vectors (g : ℕ) : List BitString := (spectralIndices g).map
  (fun i => encodeBitList ((SpectralBasis.coefficientVector g i).map signedBits))

 theorem denominators_range (g : ℕ) : (List.range (spectralIndices g).length).map (denominatorWord g)=denominators g :=
  range_map_indexAt g (fun i => signedBits (spectralBasisDenominator g i))
 theorem vectors_range (g : ℕ) : (List.range (spectralIndices g).length).map (coefficientWord g)=vectors g :=
  range_map_indexAt g (fun i => encodeBitList ((SpectralBasis.coefficientVector g i).map signedBits))

 theorem loop_executes (oracle : BitString → ℕ) (g : ℕ) (count : BitString) :
    ∃ t, loop.Executes oracle (state g 0 count [] [] [] [] [] [] (List.replicate (spectralIndices g).length true))
      (state g (spectralIndices g).length count [] [] [] []
        (encodeBitList (denominators g)).reverse (encodeBitList (vectors g)).reverse []) t ∧
      t≤(spectralIndices g).length*(bodyTime.eval g+2)+1 := by
  obtain ⟨t,ht,hb⟩ := loop_execution oracle g 0 (spectralIndices g).length (by omega) count [] []
  refine ⟨t,?_,hb⟩
  have hh := whilePop_executes _ _ _ _ ht
  simpa only [Nat.zero_add,←List.range_eq_range',denominators_range,vectors_range,List.append_nil] using hh

noncomputable def tableBound : Polynomial ℕ := (X+1)^2*(2*vectorBound+2)

theorem denominators_length (g : ℕ) : (encodeBitList (denominators g)).length≤vectorBound.eval g := by
  rw [←denominators_range]
  have h := encodedWords_length_le ((List.range (spectralIndices g).length).map (denominatorWord g)) (entryBound.eval g)
    (by intro w hw;obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw;exact denominatorWord_length g j)
  simp only [List.length_map,List.length_range,spectralIndices_length] at h ⊢
  apply h.trans
  simp only [vectorBound,eval_mul,eval_pow,eval_add,eval_X,eval_one,eval_ofNat]
  exact Nat.mul_le_mul_right _ (spectralIndex_card_bound g)

theorem vectors_length (g : ℕ) : (encodeBitList (vectors g)).length≤tableBound.eval g := by
  rw [←vectors_range]
  have h := encodedWords_length_le ((List.range (spectralIndices g).length).map (coefficientWord g)) (vectorBound.eval g)
    (by intro w hw;obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw;exact coefficientWord_length g j)
  simp only [List.length_map,List.length_range,spectralIndices_length] at h ⊢
  apply h.trans
  simp only [tableBound,eval_mul,eval_pow,eval_add,eval_X,eval_one,eval_ofNat]
  exact Nat.mul_le_mul_right _ (spectralIndex_card_bound g)

theorem loop_queryFree : loop.QueryFree := whilePop_queryFree _ _ _ body_queryFree body_queryFree
end HiddenCircuits.Circuit.Runtime.SpectralTable
