import HiddenCircuits.Circuit.Runtime.SampleEmitterSemantics
import HiddenCircuits.Circuit.Runtime.SampleEmitterCopies
import HiddenCircuits.Circuit.Runtime.SamplePairParser
import HiddenCircuits.Complexity.OracleRepeat

/-! Actual canonical gate parsing and finite dispatch, with no program certificates. -/
namespace HiddenCircuits.Circuit.Runtime.SampleEmitter
open HiddenCircuits.Complexity OracleBlock

def gateParseEmbedding : Fin 4 ↪ Fin 32 where
  toFun i := (![8,9,14,15] : Fin 4 → Fin 32) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def atomParseEmbedding : Fin 4 ↪ Fin 32 where
  toFun i := (![9,10,14,15] : Fin 4 → Fin 32) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def tagBody : GateTag → OracleBlock 31
  | .reset => oneDelta .reset
  | .copy => oneDelta .copy
  | .scale => oneDelta .scale
  | .signScale => oneDelta .signScale
  | .swap => oneDelta .swap
  | .hadamard => oneDelta .hadamard
  | .mix => oneDelta .mix
  | .encodedSwap => oneDelta .encodedSwap
  | .forbid => copies false
  | .controlledSign => copies true
noncomputable def dispatch : OracleBlock 31 := SampleGateDispatch.block 10 tagBody
noncomputable def gateBody : OracleBlock 31 :=
  seq (SamplePairParser.on gateParseEmbedding)
    (seq (SamplePairParser.on atomParseEmbedding)
      (seq (repeatPrepend 9 12 [true,true,true,true]) (seq dispatch (clear 12))))
noncomputable def gateTime (n r s u : ℕ) : ℕ :=
  (2*(r+s)+1)*(deltaTime n u+2)+10*(r+s)+9

set_option maxHeartbeats 800000 in
theorem tagBody_executes (g : BitString → ℕ) {n : ℕ} (a : ConstraintGate n)
    (circuit : BitString) (r s u : ℕ) (gates out exponent : BitString) (negative : Bool) :
    ∃cost, (tagBody (gateTag a)).Executes g
      (store circuit r s u n (4*gatePosition a) 0 gates [] [] out exponent [negative])
      (store circuit r s u n (4*gatePosition a) 0 gates [] []
        ((gateOutput a r s u).reverse++out)
        (List.replicate (gateExponent a r s u) true++exponent) [gateNegative a negative]) cost ∧
      cost ≤ gateTime n r s u := by
  cases a with
  | one p a =>
    obtain ⟨c,hc,hb⟩ := oneDelta_executes g p a circuit r s u 0 gates [] [] out exponent negative
    refine ⟨c,?_,?_⟩
    · cases a <;> simpa only [gateTag,tagBody,gatePosition,gateOutput_one,gateExponent_one,gateNegative] using hc
    · unfold gateTime
      have hm := Nat.le_mul_of_pos_left (deltaTime n u+2) (show 0<2*(r+s)+1 by omega)
      omega
  | forbid p =>
    obtain ⟨c,hc,hb⟩ := copies_executes g false p circuit r s u gates [] [] out exponent [negative]
    refine ⟨c,?_,?_⟩
    · simpa only [gateTag,tagBody,gatePosition,gateOutput_forbid,gateExponent_forbid,gateNegative,sampleNumber,Bool.false_eq_true,if_false] using hc
    · simp only [sampleNumber,Bool.false_eq_true,if_false,if_true] at hb
      unfold gateTime
      nlinarith [Nat.zero_le (s*(deltaTime n u+2))]
  | controlledSign p =>
    obtain ⟨c,hc,hb⟩ := copies_executes g true p circuit r s u gates [] [] out exponent [negative]
    refine ⟨c,?_,?_⟩
    · simpa only [gateTag,tagBody,gatePosition,gateOutput_controlledSign,gateExponent_controlledSign,gateNegative,sampleNumber,if_true] using hc
    · simp only [sampleNumber,Bool.false_eq_true,if_false,if_true] at hb
      unfold gateTime
      nlinarith [Nat.zero_le (r*(deltaTime n u+2))]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
theorem gateBody_executes (g : BitString → ℕ) {n : ℕ} (a : ConstraintGate n)
    (circuit : BitString) (r s u : ℕ) (gates out exponent : BitString) (negative : Bool) :
    ∃cost, gateBody.Executes g
      (store circuit r s u n 0 0 (pairBits (gateBits a) gates) [] [] out exponent [negative])
      (store circuit r s u n 0 0 gates [] [] ((gateOutput a r s u).reverse++out)
        (List.replicate (gateExponent a r s u) true++exponent) [gateNegative a negative]) cost ∧
      cost ≤ gateTime n r s u+24*n+97 := by
  let b := gatePosition a
  have h1 : (SamplePairParser.on gateParseEmbedding).Executes g
      (store circuit r s u n 0 0 (pairBits (gateBits a) gates) [] [] out exponent [negative])
      (store circuit r s u n 0 0 gates (gateBits a) [] out exponent [negative]) (5*(b+9)+7) := by
    convert SamplePairParser.on_executes gateParseEmbedding g (gateBits a) gates
      (store circuit r s u n 0 0 (pairBits (gateBits a) gates) [] [] out exponent [negative])
      (store circuit r s u n 0 0 gates (gateBits a) [] out exponent [negative])
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim) using 1
    rw [gateBits_length]
  have h2 : (SamplePairParser.on atomParseEmbedding).Executes g
      (store circuit r s u n 0 0 gates (gateBits a) [] out exponent [negative])
      (store circuit r s u n 0 0 gates (List.replicate b true) (gateTag a).bits out exponent [negative]) 27 := by
    convert SamplePairParser.on_executes atomParseEmbedding g (gateTag a).bits (List.replicate b true)
      (store circuit r s u n 0 0 gates (gateBits a) [] out exponent [negative])
      (store circuit r s u n 0 0 gates (List.replicate b true) (gateTag a).bits out exponent [negative])
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim) using 1
    simp
  have h3 : (repeatPrepend (9:Fin 32) 12 [true,true,true,true]).Executes g
      (store circuit r s u n 0 0 gates (List.replicate b true) (gateTag a).bits out exponent [negative])
      (store circuit r s u n (4*b) 0 gates [] (gateTag a).bits out exponent [negative]) (15*b+1) := by
    have he : (List.replicate b [true,true,true,true]).flatten=List.replicate (4*b) true := by
      induction b with
      | zero => rfl
      | succ b ih => simp only [List.replicate_succ,List.flatten_cons,ih];rw [Nat.mul_succ,Nat.add_comm (4*b),List.replicate_add];rfl
    convert repeatPrepend_executes g (9:Fin 32) 12 (by decide) [true,true,true,true]
      (store circuit r s u n 0 0 gates (List.replicate b true) (gateTag a).bits out exponent [negative]) using 1
    · funext i;fin_cases i <;> simp [store,he]
    · simp [store]
  obtain ⟨c,hc,hb⟩ := tagBody_executes g a circuit r s u gates out exponent negative
  have h4 : dispatch.Executes g
      (store circuit r s u n (4*b) 0 gates [] (gateTag a).bits out exponent [negative])
      (store circuit r s u n (4*b) 0 gates [] [] ((gateOutput a r s u).reverse++out)
        (List.replicate (gateExponent a r s u) true++exponent) [gateNegative a negative]) (c+8) := by
    apply SampleGateDispatch.block_executes 10 tagBody g (gateTag a) _ _ c rfl
    convert hc using 1
    funext i;fin_cases i <;> rfl
  have h5 : (clear (12:Fin 32)).Executes g
      (store circuit r s u n (4*b) 0 gates [] [] ((gateOutput a r s u).reverse++out)
        (List.replicate (gateExponent a r s u) true++exponent) [gateNegative a negative])
      (store circuit r s u n 0 0 gates [] [] ((gateOutput a r s u).reverse++out)
        (List.replicate (gateExponent a r s u) true++exponent) [gateNegative a negative]) (4*b+1) := by
    convert clear_executes g (12:Fin 32)
      (store circuit r s u n (4*b) 0 gates [] [] ((gateOutput a r s u).reverse++out)
        (List.replicate (gateExponent a r s u) true++exponent) [gateNegative a negative]) using 1
    · funext i;fin_cases i <;> rfl
    · simp [store]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5))),?_⟩
  have hpos : b≤n := by have h:=gatePosition_bound a;dsimp only [b];omega
  omega

lemma tagBody_queryFree (a : GateTag) : (tagBody a).QueryFree := by
  cases a with
  | reset => exact oneDelta_queryFree .reset
  | copy => exact oneDelta_queryFree .copy
  | scale => exact oneDelta_queryFree .scale
  | signScale => exact oneDelta_queryFree .signScale
  | swap => exact oneDelta_queryFree .swap
  | hadamard => exact oneDelta_queryFree .hadamard
  | mix => exact oneDelta_queryFree .mix
  | encodedSwap => exact oneDelta_queryFree .encodedSwap
  | forbid => exact copies_queryFree false
  | controlledSign => exact copies_queryFree true
lemma dispatch_queryFree : dispatch.QueryFree := SampleGateDispatch.block_queryFree _ _ tagBody_queryFree
lemma gateBody_queryFree : gateBody.QueryFree :=
  seq_queryFree _ _ (SamplePairParser.on_queryFree _) (seq_queryFree _ _ (SamplePairParser.on_queryFree _)
    (seq_queryFree _ _ (repeatPrepend_queryFree _ _ _) (seq_queryFree _ _ dispatch_queryFree (clear_queryFree _))))
end HiddenCircuits.Circuit.Runtime.SampleEmitter
