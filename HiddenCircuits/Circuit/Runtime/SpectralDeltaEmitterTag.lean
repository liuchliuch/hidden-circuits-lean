import HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitterCopies

namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
open Complexity OracleBlock
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

theorem tagBody_executes (g : BitString → ℕ) {n : ℕ} (a : ConstraintGate n)
    (circuit : BitString) (r s : ℕ) (out stream left right result : BitString) :
    ∃ cost, (tagBody (gateTag a)).Executes g
      (store circuit r s n out stream (List.replicate (gatePosition a) true) [] [] left right result)
      (store circuit r s n ((gateOutput a r s).reverse++out) stream (List.replicate (gatePosition a) true) [] [] left right result)
      cost ∧ cost ≤ gateTime n r s := by
  have hp : gatePosition a ≤ n := by have h:=gatePosition_bound a;omega
  cases a with
  | one p a =>
    have h := atom_executes g (gateTag (.one p a)) circuit r s n p.before out stream [] [] left right result
    refine ⟨14*p.before+68,?_,?_⟩
    · cases a <;> simpa only [gateTag,tagBody,gatePosition,gateOutput_one] using h
    · simp only [gatePosition] at hp
      unfold gateTime
      nlinarith [Nat.zero_le ((r+s)*(14*n+70))]
  | forbid p =>
    obtain ⟨c,h,hb⟩ := copies_executes g false circuit r s n p.before out stream [] left right result
    refine ⟨c,?_,?_⟩
    · simpa only [gateTag,tagBody,gatePosition,gateOutput_forbid,samplePort,sampleNumber,Bool.false_eq_true,if_false] using h
    · simp only [sampleNumber,Bool.false_eq_true,if_false] at hb
      simp only [gatePosition] at hp
      unfold gateTime
      nlinarith [Nat.zero_le (s*(14*n+70)),Nat.mul_le_mul_left (2*r) (show 14*p.before+70 ≤ 14*n+70 by omega)]
  | controlledSign p =>
    obtain ⟨c,h,hb⟩ := copies_executes g true circuit r s n p.before out stream [] left right result
    refine ⟨c,?_,?_⟩
    · simpa only [gateTag,tagBody,gatePosition,gateOutput_sign,samplePort,sampleNumber,if_true] using h
    · simp only [sampleNumber,if_true] at hb
      simp only [gatePosition] at hp
      unfold gateTime
      nlinarith [Nat.zero_le (r*(14*n+70)),Nat.mul_le_mul_left (2*s) (show 14*p.before+70 ≤ 14*n+70 by omega)]

end HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
