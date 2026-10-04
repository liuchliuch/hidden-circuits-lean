import HiddenCircuits.GraphReduction.Runtime.WordGraph.EvenWeightsStages
namespace HiddenCircuits.Complexity.EvenWeightsRuntime
open OracleBlock BinaryArithmetic RegisterMachine Polynomial
open HiddenCircuits.GraphReduction
open HiddenCircuits.GraphReduction.Runtime.WordGraph
set_option maxHeartbeats 1000000

def registers (f v s den p : ℤ) : Fin 7 → ℤ := ![f,v,s,den,p,0,0]
def code : List Instruction := [⟨.divide,0,0,1⟩,⟨.multiply,0,0,2⟩,⟨.multiply,3,3,4⟩]
def combineEmbedding : Fin 16 ↪ Fin 31 where
  toFun i := ![9,10,11,12,13,14,15,16,17,4,7,8,2,6,27,28] i
  inj' := by decide +kernel
def workState (i k : ℕ) (R : Fin 7 → ℤ) : Store 30 :=
  Function.update (Function.update (state i k (signedBits (R 3)) [] (signedBits (R 0))
    (signedBits (R 4)) (signedBits (R 1)) (signedBits (R 2))) 27 (signedBits (R 5))) 28 (signedBits (R 6))
noncomputable def combineConstants : OracleBlock 30 := seq (push 27 false) (push 28 false)
noncomputable def combineFinish : OracleBlock 30 := seq (moveOn 4 3 29 (by decide) (by decide) (by decide))
  (clearList [4,6,7,8,27,28])
noncomputable def combine : OracleBlock 30 := seq combineConstants
  (seq (rename (compile code) combineEmbedding) combineFinish)
noncomputable def componentP : Polynomial ℕ := 4*(X+1)^2+4
noncomputable def combineTime : Polynomial ℕ := 13*straightTime code+12*X+34

lemma evaluate_code (f v s den p : ℤ) : evaluate code (registers f v s den p)=registers (f/v*s) v s (den*p) p := by
  funext q;fin_cases q <;> simp [code,evaluate,Instruction.eval,Operation.eval,registers]
lemma combineConstants_executes (g : BitString → ℕ) (i k : ℕ) (f v s den p : ℤ) :
    combineConstants.Executes g (state i k (signedBits den) [] (signedBits f) (signedBits p) (signedBits v) (signedBits s))
      (workState i k (registers f v s den p)) 4 := by
  let st := state i k (signedBits den) [] (signedBits f) (signedBits p) (signedBits v) (signedBits s)
  have h1 := push_executes g (27:Fin 31) false st
  have h2 := push_executes g (28:Fin 31) false (Function.update st (27:Fin 31) [false])
  have hh := seq_executes _ _ g h1 h2
  convert hh using 1

lemma workState_bound (i k B : ℕ) (R : Fin 7 → ℤ) (hi : i ≤ B) (hk : k ≤ B) (hR : Bounded B R) :
    ∀q,(workState i k R q).length ≤ B := by
  intro q;fin_cases q <;> simp [workState,state] <;>
    first | exact hi | exact hk | exact hR 0 | exact hR 1 | exact hR 2 | exact hR 3 | exact hR 4 | exact hR 5 | exact hR 6


lemma combineFinish_executes (g : BitString → ℕ) (i k : ℕ) (R : Fin 7 → ℤ) (M : ℕ)
    (hM : ∀q,(workState i k R q).length ≤ M) :
    ∃c, combineFinish.Executes g (workState i k R)
      (state i k (signedBits (R 3)) (signedBits (R 0)) [] [] [] []) c ∧ c ≤ 12*M+26 := by
  let st := workState i k R
  let mid := Function.update (Function.update st (3:Fin 31) (signedBits (R 0))) 4 []
  have hn : (signedBits (R 0)).length ≤ M := by simpa [workState,state] using hM 4
  have hm : (moveOn (4:Fin 31) 3 29 (by decide) (by decide) (by decide)).Executes g st mid
      (6*(signedBits (R 0)).length+5) := by
    simpa [st,mid,workState,state] using moveOn_executes g (4:Fin 31) 3 29 (by decide) (by decide) (by decide) st rfl
  have hb : ∀q,(mid q).length ≤ M := by
    intro q
    by_cases h4 : q=4
    · subst q;simp [mid]
    by_cases h3 : q=3
    · subst q;simpa [mid] using hn
    simpa [mid,Function.update_of_ne h4,Function.update_of_ne h3] using hM q
  obtain ⟨c,hc,hcb⟩ := clearList_executes g ([4,6,7,8,27,28]:List (Fin 31)) mid M hb
  have he : eraseStore ([4,6,7,8,27,28]:List (Fin 31)) mid=state i k (signedBits (R 3)) (signedBits (R 0)) [] [] [] [] := by
    funext q;fin_cases q <;> simp [eraseStore,mid,st,workState,state]
  rw [he] at hc
  refine ⟨_,seq_executes _ _ g hm hc,?_⟩
  simp only [List.length_cons,List.length_nil] at hcb
  omega

lemma combine_executes (g : BitString → ℕ) (i k B : ℕ) (f v s den p : ℤ)
    (hi : i ≤ B) (hk : k ≤ B) (hv : v≠0) (hd : v ∣ f) (hR : Bounded B (registers f v s den p)) :
    ∃c, combine.Executes g
      (state i k (signedBits den) [] (signedBits f) (signedBits p) (signedBits v) (signedBits s))
      (state i k (signedBits (den*p)) (signedBits (f/v*s)) [] [] [] []) c ∧ c ≤ combineTime.eval B := by
  have hp := combineConstants_executes g i k f v s den p
  obtain ⟨a,ha,hab⟩ := compile_polynomial code g (registers f v s den p) B hR
    (by simp [code,Valid,Operation.Valid,registers,hv,hd])
  rw [evaluate_code] at ha
  have hrun : (rename (compile code) combineEmbedding).Executes g (workState i k (registers f v s den p))
      (workState i k (registers (f/v*s) v s (den*p) p)) a := by
    apply rename_executes_to (compile code) combineEmbedding g ha
    · funext q;fin_cases q <;> rfl
    · funext q;fin_cases q <;> rfl
    · intro q hq
      have h2 : q.val≠2 := by intro h;exact hq 12 (Fin.ext h.symm)
      have h4 : q.val≠4 := by intro h;exact hq 9 (Fin.ext h.symm)
      simp [workState,registers,Function.update_apply,state,h2,h4]
  obtain ⟨b,hb,hbb⟩ := combineFinish_executes g i k (registers (f/v*s) v s (den*p) p) (B+a)
    (hrun.stack_bound (workState_bound i k B _ hi hk hR))
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hrun hb),?_⟩
  simp only [combineTime,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

lemma componentBound (d : ℕ) (i : Fin (d+1)) :
    Bounded (componentP.eval d) (registers (oddFactorial (d+1):ℤ) ((2*i.val+1:ℕ):ℤ)
      ((-1:ℤ)^d) (interpolationDenominator d i) ((2:ℤ)^d)) := by
  have hB : componentP.eval d=4*(d+1)^2+4 := by simp [componentP]
  rw [hB]
  have hf : (signedBits (oddFactorial (d+1):ℤ)).length ≤ 4*(d+1)^2+4 := by
    have hh := signedBits_length_of_abs_bound (show (oddFactorial (d+1):ℤ).natAbs ≤ 2^(2*(d+1)*(d+1)) by
      simpa using OddFactorialRuntime.oddFactorial_bound (d+1))
    nlinarith
  have hv : (signedBits ((2*i.val+1:ℕ):ℤ)).length ≤ 4*(d+1)^2+4 := by
    have hh := signedBits_length_of_abs_bound (show ((2*i.val+1:ℕ):ℤ).natAbs ≤ 2^(2*d+1) by
      simp only [Int.natAbs_natCast]
      exact (show 2*i.val+1 ≤ 2*d+1 by omega).trans (Nat.lt_two_pow_self.le))
    nlinarith
  have hs : (signedBits ((-1:ℤ)^d)).length ≤ 4*(d+1)^2+4 := by
    have hh := signedBits_length_of_abs_bound (show ((-1:ℤ)^d).natAbs ≤ 2^0 by simp)
    nlinarith
  have hd : (signedBits (interpolationDenominator d i)).length ≤ 4*(d+1)^2+4 := by
    have hh := (interpolation_weights_bit_bound d i).1
    simp only [signedBits,List.length_cons,encodeNat_length]
    nlinarith
  have hp : (signedBits ((2:ℤ)^d)).length ≤ 4*(d+1)^2+4 := by
    have hh := signedBits_length_of_abs_bound (show ((2:ℤ)^d).natAbs ≤ 2^d by simp)
    nlinarith
  have h0 : (signedBits (0:ℤ)).length ≤ 4*(d+1)^2+4 := by change 1 ≤ _;omega
  intro q;fin_cases q <;> first | exact hf | exact hv | exact hs | exact hd | exact hp | exact h0
end HiddenCircuits.Complexity.EvenWeightsRuntime
