import HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitterTag

namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
open Complexity OracleBlock
set_option maxHeartbeats 40000
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

theorem body_executes (g : BitString → ℕ) {n : ℕ} (a : ConstraintGate n)
    (circuit : BitString) (r s : ℕ) (out stream left right result : BitString) :
    ∃ cost, body.Executes g (store circuit r s n out (pairBits (gateBits a) stream) [] [] [] left right result)
      (store circuit r s n ((gateOutput a r s).reverse++out) stream [] [] [] left right result)
      cost ∧ cost ≤ gateTime n r s+6*n+97 := by
  let b:=gatePosition a
  have h1 : (SamplePairParser.on gateParse).Executes g
      (store circuit r s n out (pairBits (gateBits a) stream) [] [] [] left right result)
      (store circuit r s n out stream (gateBits a) [] [] left right result) (5*(b+9)+7) := by
    convert SamplePairParser.on_executes gateParse g (gateBits a) stream
      (store circuit r s n out (pairBits (gateBits a) stream) [] [] [] left right result)
      (store circuit r s n out stream (gateBits a) [] [] left right result)
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by
        intro i hi
        fin_cases i
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact (hi 0 rfl).elim
        · exact (hi 1 rfl).elim
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact (hi 2 rfl).elim
        · exact (hi 3 rfl).elim
        · rfl
        · rfl
      ) using 1
    rw [gateBits_length]
  have h2 : (SamplePairParser.on atomParse).Executes g
      (store circuit r s n out stream (gateBits a) [] [] left right result)
      (store circuit r s n out stream (List.replicate b true) (gateTag a).bits [] left right result) 27 := by
    convert SamplePairParser.on_executes atomParse g (gateTag a).bits (List.replicate b true)
      (store circuit r s n out stream (gateBits a) [] [] left right result)
      (store circuit r s n out stream (List.replicate b true) (gateTag a).bits [] left right result)
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by
        intro i hi
        fin_cases i
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact (hi 0 rfl).elim
        · exact (hi 1 rfl).elim
        · rfl
        · rfl
        · rfl
        · rfl
        · exact (hi 2 rfl).elim
        · exact (hi 3 rfl).elim
        · rfl
        · rfl
      ) using 1
    simp
  obtain ⟨c,h,hb⟩ := tagBody_executes g a circuit r s out stream left right result
  have hd : dispatch.Executes g
      (store circuit r s n out stream (List.replicate b true) (gateTag a).bits [] left right result)
      (store circuit r s n ((gateOutput a r s).reverse++out) stream (List.replicate b true) [] [] left right result) (c+8) := by
    apply SampleGateDispatch.block_executes 7 tagBody g (gateTag a) _ _ c rfl
    convert h using 1
    funext i;fin_cases i <;> rfl
  have hc : (clear (6:Fin 16)).Executes g
      (store circuit r s n ((gateOutput a r s).reverse++out) stream (List.replicate b true) [] [] left right result)
      (store circuit r s n ((gateOutput a r s).reverse++out) stream [] [] [] left right result) (b+1) := by
    convert clear_executes g (6:Fin 16)
      (store circuit r s n ((gateOutput a r s).reverse++out) stream (List.replicate b true) [] [] left right result) using 1
    · funext i;fin_cases i <;> rfl
    · simp [store]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g hd hc)),?_⟩
  have hp : b ≤ n := by have h:=gatePosition_bound a;dsimp only [b];omega
  omega

lemma tagBody_queryFree (a : GateTag) : (tagBody a).QueryFree := by
  cases a with
  | forbid => exact copies_queryFree _ _ _
  | controlledSign => exact copies_queryFree _ _ _
  | reset => exact atom_queryFree _
  | copy => exact atom_queryFree _
  | scale => exact atom_queryFree _
  | signScale => exact atom_queryFree _
  | swap => exact atom_queryFree _
  | hadamard => exact atom_queryFree _
  | mix => exact atom_queryFree _
  | encodedSwap => exact atom_queryFree _
lemma body_queryFree : body.QueryFree := seq_queryFree _ _ (SamplePairParser.on_queryFree _)
  (seq_queryFree _ _ (SamplePairParser.on_queryFree _) (seq_queryFree _ _
    (SampleGateDispatch.block_queryFree _ _ tagBody_queryFree) (clear_queryFree _)))
end HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
