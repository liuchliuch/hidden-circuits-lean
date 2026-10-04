import HiddenCircuits.DH.Runtime.ScalarCoefficientCore

/-! Actual factorial generation followed by the checked
six-assignment crossing arithmetic. There is no supplied factorial table. -/
namespace HiddenCircuits.DH.Runtime.ScalarCoefficient
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic
open Complexity.BinaryArithmetic.RegisterMachine Polynomial
set_option maxHeartbeats 2000000

def arithmeticMap : Fin 16↪Fin 26 where
  toFun q:=⟨q.val+8,by omega⟩
  inj':=by intro q z h;apply Fin.ext;have:=congrArg Fin.val h;dsimp at this;omega
noncomputable def arithmetic : OracleBlock 25:=rename CrossTerm.program arithmeticMap
noncomputable def factors : OracleBlock 25:=seq (factorial 0 0) (seq (factorial 1 1)
  (seq (factorial 2 2) (seq (factorial 6 3) (factorial 7 4))))

lemma factors_executes (g : BitString→ ℕ) (i j r A B : ℕ) :
    ∃t,factors.Executes g
      (state i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) [] (i-r) (j-r)
        ![[],[],[],[],[],signedBits (A:ℤ),signedBits (B:ℤ)])
      (state i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) [] (i-r) (j-r)
        (signedBits ∘ CrossTerm.registers i j r A B)) t ∧
      t≤ 5*FactorialInto.time.eval (i+j+r)+8 := by
  let R0:Fin 7→ BitString:=![[],[],[],[],[],signedBits (A:ℤ),signedBits (B:ℤ)]
  let R1:=Function.update R0 0 (signedBits (i.factorial:ℤ))
  let R2:=Function.update R1 1 (signedBits (j.factorial:ℤ))
  let R3:=Function.update R2 2 (signedBits (r.factorial:ℤ))
  let R4:=Function.update R3 3 (signedBits ((i-r).factorial:ℤ))
  let R5:=Function.update R4 4 (signedBits ((j-r).factorial:ℤ))
  obtain ⟨c0,h0,b0⟩:=factorial_executes g i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) [] (i-r) (j-r) R0 0 0 i rfl rfl
  obtain ⟨c1,h1,b1⟩:=factorial_executes g i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) [] (i-r) (j-r) R1 1 1 j rfl rfl
  obtain ⟨c2,h2,b2⟩:=factorial_executes g i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) [] (i-r) (j-r) R2 2 2 r rfl rfl
  obtain ⟨c3,h3,b3⟩:=factorial_executes g i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) [] (i-r) (j-r) R3 6 3 (i-r) rfl rfl
  obtain ⟨c4,h4,b4⟩:=factorial_executes g i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) [] (i-r) (j-r) R4 7 4 (j-r) rfl rfl
  have hR:R5=signedBits ∘ CrossTerm.registers i j r A B:=by funext q;fin_cases q <;> rfl
  have h:=seq_executes _ _ g h0 (seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)))
  change factors.Executes g _ (state _ _ _ _ _ _ _ _ R5) _ at h
  rw [hR] at h
  refine ⟨_,h,?_⟩
  have m0:=polynomial_nat_eval_mono FactorialInto.time (show i≤ i+j+r by omega)
  have m1:=polynomial_nat_eval_mono FactorialInto.time (show j≤ i+j+r by omega)
  have m2:=polynomial_nat_eval_mono FactorialInto.time (show r≤ i+j+r by omega)
  have m3:=polynomial_nat_eval_mono FactorialInto.time (show i-r≤ i+j+r by omega)
  have m4:=polynomial_nat_eval_mono FactorialInto.time (show j-r≤ i+j+r by omega)
  dsimp only at m0 m1 m2 m3 m4
  omega

lemma arithmetic_executes (g : BitString→ ℕ) (i j r A B : ℕ) (hri:r≤ i) (hrj:r≤ j) :
    ∃t,arithmetic.Executes g
      (state i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) [] (i-r) (j-r)
        (signedBits ∘ CrossTerm.registers i j r A B))
      (state i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) [] (i-r) (j-r)
        (signedBits ∘ evaluate CrossTerm.code (CrossTerm.registers i j r A B))) t ∧
      t≤(straightTime CrossTerm.code).eval (CrossTerm.inputSize (CrossTerm.registers i j r A B)) := by
  obtain ⟨t,ht,hb,ho⟩:=CrossTerm.executes g i j r A B hri hrj
  refine ⟨t,?_,hb⟩
  apply rename_executes_to _ arithmeticMap g ht
  · funext q;fin_cases q <;> rfl
  · funext q;fin_cases q <;> rfl
  · intro q hq
    have hq':q.val<8 ∨ 24≤ q.val:=by
      by_contra hn
      have hi:8≤ q.val ∧ q.val<24:=by omega
      exact hq ⟨q.val-8,by omega⟩ (by apply Fin.ext;dsimp [arithmeticMap];omega)
    rcases hq' with hq'|hq'
    · interval_cases h:q.val <;> simp [state,h]
    · simp [state,show q.val≠0 by omega,show q.val≠1 by omega,show q.val≠2 by omega,
        show q.val≠3 by omega,show q.val≠4 by omega,show q.val≠5 by omega,
        show q.val≠6 by omega,show q.val≠7 by omega,show ¬(17≤ q.val ∧ q.val<24) by omega]

def inputSize (i j r A B : ℕ) : ℕ:=i+j+r+(signedBits (A:ℤ)).length+(signedBits (B:ℤ)).length+1
lemma factorial_word_bound (x S : ℕ) (hx:x≤ S) : (signedBits (x.factorial:ℤ)).length≤ S*S+2:=by
  have h:=factorial_binary_length x
  simp only [FactorialInto.signed_nat,List.length_cons]
  nlinarith
lemma cross_input_bound (i j r A B : ℕ) :
    CrossTerm.inputSize (CrossTerm.registers i j r A B)≤ 7*((inputSize i j r A B)^2+inputSize i j r A B+3) := by
  let S:=inputSize i j r A B
  have hi:i≤ S:=by unfold S inputSize;omega
  have hj:j≤ S:=by unfold S inputSize;omega
  have hr:r≤ S:=by unfold S inputSize;omega
  have h0:=factorial_word_bound i S hi
  have h1:=factorial_word_bound j S hj
  have h2:=factorial_word_bound r S hr
  have h3:=factorial_word_bound (i-r) S (by omega)
  have h4:=factorial_word_bound (j-r) S (by omega)
  have hA:(signedBits (A:ℤ)).length≤ S:=by unfold S inputSize;omega
  have hB:(signedBits (B:ℤ)).length≤ S:=by unfold S inputSize;omega
  change (∑q:Fin 7,_)≤ 7*(S^2+S+3)
  calc
    _ ≤ ∑q:Fin 7, (S^2+S+3) := by
      apply Finset.sum_le_sum
      intro q hq;fin_cases q <;> dsimp [CrossTerm.registers] <;> nlinarith
    _ = _ := by simp

lemma factors_queryFree : factors.QueryFree:=seq_queryFree _ _ (FactorialInto.on_queryFree _) (seq_queryFree _ _
  (FactorialInto.on_queryFree _) (seq_queryFree _ _ (FactorialInto.on_queryFree _)
    (seq_queryFree _ _ (FactorialInto.on_queryFree _) (FactorialInto.on_queryFree _))))
lemma arithmetic_queryFree : arithmetic.QueryFree:=rename_queryFree _ _ CrossTerm.queryFree
end HiddenCircuits.DH.Runtime.ScalarCoefficient
