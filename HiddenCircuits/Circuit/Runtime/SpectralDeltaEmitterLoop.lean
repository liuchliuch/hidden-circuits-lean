import HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitterGates

namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
open Complexity OracleBlock

theorem loop_execution (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n))
    (circuit : BitString) (r s : ℕ) (out left right result : BitString) :
    ∃ cost, WhileExecution (5:Fin 16) body body g
      (store circuit r s n out (encodeBitList (w.map gateBits)) [] [] [] left right result)
      (store circuit r s n ((output w r s).reverse++out) [] [] [] [] left right result) cost ∧
      cost ≤ w.length*(gateTime n r s+6*n+99)+1 := by
  induction w generalizing out with
  | nil=>exact ⟨1,by simpa only [output_nil,List.reverse_nil,List.nil_append] using
      (WhileExecution.empty (stack:=(5:Fin 16)) (B:=body) (C:=body) (g:=g)
        (store circuit r s n out [] [] [] [] left right result) rfl),by simp⟩
  | cons a w ih=>
    obtain ⟨c,hc,hcb⟩ := body_executes g a circuit r s out (encodeBitList (w.map gateBits)) left right result
    obtain ⟨d,hd,hdb⟩ := ih ((gateOutput a r s).reverse++out)
    have hu : Function.update (store circuit r s n out (encodeBitList ((a::w).map gateBits)) [] [] [] left right result)
        (5:Fin 16) (pairBits (gateBits a) (encodeBitList (w.map gateBits)))=
        store circuit r s n out (pairBits (gateBits a) (encodeBitList (w.map gateBits))) [] [] [] left right result := by
      funext i;fin_cases i <;> rfl
    rw [←hu] at hc
    have h := WhileExecution.one (stack:=(5:Fin 16)) (B:=body) (C:=body) (g:=g) rfl hc hd
    refine ⟨1+c+1+d,?_,?_⟩
    · convert h using 1
      simp only [output_cons,List.reverse_append,List.append_assoc]
    · simp only [List.length_cons];nlinarith

theorem setup_executes (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) :
    setup.Executes g (store (circuitBits n w) r s 0 [] [] [] [] [] [] [] [])
      (store (circuitBits n w) r s n [] (encodeBitList (w.map gateBits)) [] [] [] [] [] [])
      (5*(circuitBits n w).length+5*n+11) := by
  have hc : (copyOn (0:Fin 16) 5 14 (by decide) (by decide) (by decide)).Executes g
      (store (circuitBits n w) r s 0 [] [] [] [] [] [] [] [])
      (store (circuitBits n w) r s 0 [] (circuitBits n w) [] [] [] [] [] []) (5*(circuitBits n w).length+2) := by
    convert copyOn_executes g (0:Fin 16) 5 14 (by decide) (by decide) (by decide)
      (store (circuitBits n w) r s 0 [] [] [] [] [] [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [store]
  have hp : (SamplePairParser.on headerParse).Executes g
      (store (circuitBits n w) r s 0 [] (circuitBits n w) [] [] [] [] [] [])
      (store (circuitBits n w) r s n [] (encodeBitList (w.map gateBits)) [] [] [] [] [] []) (5*n+7) := by
    convert SamplePairParser.on_executes headerParse g (List.replicate n true) (encodeBitList (w.map gateBits))
      (store (circuitBits n w) r s 0 [] (circuitBits n w) [] [] [] [] [] [])
      (store (circuitBits n w) r s n [] (encodeBitList (w.map gateBits)) [] [] [] [] [] [])
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | rfl) using 1
    simp
  convert seq_executes _ _ g hc hp using 1 <;> omega

lemma loop_queryFree : loop.QueryFree := whilePop_queryFree _ _ _ body_queryFree body_queryFree
lemma setup_queryFree : setup.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (SamplePairParser.on_queryFree _)
end HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
