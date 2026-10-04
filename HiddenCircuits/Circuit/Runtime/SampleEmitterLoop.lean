import HiddenCircuits.Circuit.Runtime.SampleEmitterGates

/-! The actual gate-stream loop preserves canonical order. -/
namespace HiddenCircuits.Circuit.Runtime.SampleEmitter
open HiddenCircuits.Complexity OracleBlock

noncomputable def gateLoop : OracleBlock 31 := whilePop 8 gateBody gateBody

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
theorem gateLoop_execution (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n))
    (circuit : BitString) (r s u : ℕ) (out exponent : BitString) (negative : Bool) :
    ∃cost, WhileExecution (8:Fin 32) gateBody gateBody g
      (store circuit r s u n 0 0 (encodeBitList (w.map gateBits)) [] [] out exponent [negative])
      (store circuit r s u n 0 0 [] [] [] ((sampleOutput w r s u).reverse++out)
        (List.replicate (sampleGain w r s u) true++exponent) [sampleNegative w negative]) cost ∧
      cost ≤ w.length*(gateTime n r s u+24*n+99)+1 := by
  induction w generalizing out exponent negative with
  | nil =>
    exact ⟨1,by simpa [sampleGain,sampleNegative] using
      (WhileExecution.empty (stack:=(8:Fin 32)) (B:=gateBody) (C:=gateBody) (g:=g)
        (store circuit r s u n 0 0 [] [] [] out exponent [negative]) rfl),by simp⟩
  | cons a w ih =>
    obtain ⟨c,hc,hcb⟩ := gateBody_executes g a circuit r s u (encodeBitList (w.map gateBits)) out exponent negative
    obtain ⟨d,hd,hdb⟩ := ih ((gateOutput a r s u).reverse++out)
      (List.replicate (gateExponent a r s u) true++exponent) (gateNegative a negative)
    have hu : Function.update
        (store circuit r s u n 0 0 (encodeBitList ((a::w).map gateBits)) [] [] out exponent [negative])
        (8:Fin 32) (pairBits (gateBits a) (encodeBitList (w.map gateBits)))=
        store circuit r s u n 0 0 (pairBits (gateBits a) (encodeBitList (w.map gateBits))) [] [] out exponent [negative] := by
      funext i;fin_cases i <;> rfl
    rw [←hu] at hc
    have h := WhileExecution.one (stack:=(8:Fin 32)) (B:=gateBody) (C:=gateBody) (g:=g) rfl hc hd
    refine ⟨1+c+1+d,?_,?_⟩
    · convert h using 1
      simp only [sampleOutput_cons,List.reverse_append,List.append_assoc,sampleGain,List.map_cons,List.sum_cons,
        sampleNegative,List.foldl_cons,←List.append_assoc,←List.replicate_add]
      rw [Nat.add_comm (gateExponent a r s u)]
    · simp only [List.length_cons]
      nlinarith

theorem gateLoop_executes (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n))
    (circuit : BitString) (r s u : ℕ) (out exponent : BitString) (negative : Bool) :
    ∃cost, gateLoop.Executes g
      (store circuit r s u n 0 0 (encodeBitList (w.map gateBits)) [] [] out exponent [negative])
      (store circuit r s u n 0 0 [] [] [] ((sampleOutput w r s u).reverse++out)
        (List.replicate (sampleGain w r s u) true++exponent) [sampleNegative w negative]) cost ∧
      cost ≤ w.length*(gateTime n r s u+24*n+99)+1 := by
  obtain ⟨c,hc,hb⟩ := gateLoop_execution g w circuit r s u out exponent negative
  exact ⟨c,whilePop_executes _ _ _ g hc,hb⟩
lemma gateLoop_queryFree : gateLoop.QueryFree := whilePop_queryFree _ _ _ gateBody_queryFree gateBody_queryFree
end HiddenCircuits.Circuit.Runtime.SampleEmitter
