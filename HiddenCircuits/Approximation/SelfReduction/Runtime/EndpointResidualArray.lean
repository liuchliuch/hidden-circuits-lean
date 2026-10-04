import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualMap

/-! A real head deletion followed by the threshold/pop map of all retained
boundaries. Original list order is maintained; no retained-mask sorting occurs. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidual
open Complexity OracleBlock SamplerRuntime.EndpointFiber SamplerRuntime.EndpointParser

noncomputable def discardHead : OracleBlock 7 := seq (headOn arrayParseMap) (seq (clear 2) (clear 4))
noncomputable def deleteArray : OracleBlock 7 := seq discardHead arrayMap

lemma discardHead_executes (g : BitString  →  ℕ) (j t : ℕ) (xs : List ℕ) :
    discardHead.Executes g (arrayStore (natBits (t::xs)) (unary j) [] [] [] [] [] [])
      (arrayStore (natBits xs) (unary j) [] [] [] [] [] []) (6*t+12) := by
  have hp := headOn_executes arrayParseMap g
    (arrayStore (natBits (t::xs)) (unary j) [] [] [] [] [] [])
    (arrayStore (natBits xs) (unary j) (unary t) [] [true] [] [] []) (natBits (t::xs))
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp only [natBits,natWords,List.map_cons,encodeBitList,headResult_word] <;> rfl)
    (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim)
  have hc : (clear (2:Fin 8)).Executes g
      (arrayStore (natBits xs) (unary j) (unary t) [] [true] [] [] [])
      (arrayStore (natBits xs) (unary j) [] [] [true] [] [] []) (t+1) := by
    convert clear_executes g (2:Fin 8) (arrayStore (natBits xs) (unary j) (unary t) [] [true] [] [] []) using 1
    · funext i;fin_cases i <;> rfl
    · simp [arrayStore]
  have hf : (clear (4:Fin 8)).Executes g
      (arrayStore (natBits xs) (unary j) [] [] [true] [] [] [])
      (arrayStore (natBits xs) (unary j) [] [] [] [] [] []) 2 := by
    convert clear_executes g (4:Fin 8) (arrayStore (natBits xs) (unary j) [] [] [true] [] [] []) using 1
    funext i;fin_cases i <;> rfl
  convert seq_executes _ _ g hp (seq_executes _ _ g hc hf) using 1
  simp [headCost,natBits,natWords,encodeBitList,GraphVerifier.parse_pair,BinaryArithmetic.pair_parse_cost]
  omega

theorem deleteArray_executes (g : BitString  →  ℕ) (j t : ℕ) (xs : List ℕ) (N : ℕ)
    (hxs : ∀ a∈xs,a ≤ N) :
    ∃cost, deleteArray.Executes g (arrayStore (natBits (t::xs)) (unary j) [] [] [] [] [] [])
      (arrayStore (natBits (xs.map (dropBoundary j))) (unary j) [] [] [] [] [] []) cost ∧
      cost ≤ 6*t+xs.length*(28*N+13*j+52)+18 := by
  obtain ⟨c,hc,hb⟩ := arrayMap_executes g j xs N hxs
  exact ⟨_,seq_executes _ _ g (discardHead_executes g j t xs) hc,by omega⟩
lemma deleteArray_queryFree : deleteArray.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ (headOn_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))
  arrayMap_queryFree
end HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidual
