import HiddenCircuits.Circuit.Runtime.SpectralCoefficientsCell
import HiddenCircuits.Circuit.IntegerSpectralWeights
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorProduct

/-! One genuine signed arithmetic step multiplies a Lagrange denominator by x−a. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralDenominator
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic
open HiddenCircuits.Complexity.BinaryArithmetic.RegisterMachine
open Polynomial

def registers (x acc a tmp : ℤ) : Fin 7 → ℤ := fun i =>
  if i.val=0 then x else if i.val=1 then acc else if i.val=2 then a else if i.val=3 then -1
  else if i.val=4 then tmp else 0

def code : List Instruction := [⟨.multiply,4,2,3⟩,⟨.add,4,0,4⟩,⟨.multiply,1,1,4⟩]
noncomputable def arithmetic : OracleBlock 15 := compile code
noncomputable def arithmeticTime : Polynomial ℕ := straightTime code

theorem evaluate_code (x acc a tmp : ℤ) :
    evaluate code (registers x acc a tmp)=registers x (acc*(x-a)) a (x-a) := by
  funext i;fin_cases i <;> simp [evaluate,code,Instruction.eval,Operation.eval,registers] <;> ring_nf <;> simp

theorem arithmetic_executes (g : BitString → ℕ) (x acc a : ℤ) (B : ℕ) (hB : 2≤B)
    (hx : (signedBits x).length≤B) (hc : (signedBits acc).length≤B) (ha : (signedBits a).length≤B) :
    ∃ t, arithmetic.Executes g (RegisterMachine.store [] [] (signedBits ∘ registers x acc a 0))
      (RegisterMachine.store [] [] (signedBits ∘ registers x (acc*(x-a)) a (x-a))) t ∧ t≤arithmeticTime.eval B := by
  have hb : Bounded B (registers x acc a 0) := by
    have hn : (signedBits (-1)).length=2 := by decide +kernel
    have hz : (signedBits 0).length=1 := rfl
    intro i;fin_cases i <;> simp [registers,hn,hz]
    all_goals first | exact hx | exact hc | exact ha | exact hB | exact (show 1≤B by omega)
  have hv : Valid code (registers x acc a 0) := by simp [Valid,code,Operation.Valid]
  simpa only [evaluate_code] using compile_polynomial code g (registers x acc a 0) B hb hv

def streamStore (x acc : ℤ) (a tmp flag rest : BitString) : Store 18 := fun i =>
  if i.val=9 then signedBits x else if i.val=10 then signedBits acc else if i.val=11 then a
  else if i.val=12 then signedBits (-1) else if i.val=13 then tmp else if i.val=14 then signedBits 0
  else if i.val=15 then signedBits 0 else if i.val=16 then rest else if i.val=18 then flag else []

def parseEmbedding : Fin 4 ↪ Fin 19 where
  toFun i := if i.val=0 then 16 else if i.val=1 then 11 else if i.val=2 then 17 else 18
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
 def arithmeticEmbedding : Fin 16 ↪ Fin 19 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 19 => z.val) h)

noncomputable def parseRoot : OracleBlock 18 := GraphVerifier.Runtime.unpairOn parseEmbedding
noncomputable def body : OracleBlock 18 := seq parseRoot (seq (rename arithmetic arithmeticEmbedding)
  (seq (clear 11) (seq (clear 13) (seq (push 13 false) (clear 18)))))
noncomputable def bodyTime : Polynomial ℕ := arithmeticTime+8*X+21

theorem parseRoot_executes (g : BitString → ℕ) (x acc : ℤ) (a rest : BitString) :
    parseRoot.Executes g (streamStore x acc [] (signedBits 0) [] (pairBits a rest))
      (streamStore x acc a (signedBits 0) [true] rest) (5*a.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes parseEmbedding g
    (streamStore x acc [] (signedBits 0) [] (pairBits a rest)) (streamStore x acc a (signedBits 0) [true] rest) (pairBits a rest)
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by
      intro j hj;fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 3 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost]
  omega

theorem body_executes (g : BitString → ℕ) (x acc a : ℤ) (rest : BitString) (B : ℕ) (hB : 2≤B)
    (hx : (signedBits x).length≤B) (hc : (signedBits acc).length≤B) (ha : (signedBits a).length≤B) :
    ∃ t, body.Executes g (streamStore x acc [] (signedBits 0) [] (pairBits (signedBits a) rest))
      (streamStore x (acc*(x-a)) [] (signedBits 0) [] rest) t ∧ t≤bodyTime.eval B := by
  let s₀ := streamStore x acc [] (signedBits 0) [] (pairBits (signedBits a) rest)
  let s₁ := streamStore x acc (signedBits a) (signedBits 0) [true] rest
  let s₂ := streamStore x (acc*(x-a)) (signedBits a) (signedBits (x-a)) [true] rest
  let s₃ := streamStore x (acc*(x-a)) [] (signedBits (x-a)) [true] rest
  let s₄ := streamStore x (acc*(x-a)) [] [] [true] rest
  let s₅ := streamStore x (acc*(x-a)) [] (signedBits 0) [true] rest
  let s₆ := streamStore x (acc*(x-a)) [] (signedBits 0) [] rest
  have h₁ : parseRoot.Executes g s₀ s₁ (5*(signedBits a).length+3) := parseRoot_executes g x acc _ _
  obtain ⟨t,ht,htb⟩ := arithmetic_executes g x acc a B hB hx hc ha
  have h₂ : (rename arithmetic arithmeticEmbedding).Executes g s₁ s₂ t := by
    apply rename_executes_to arithmetic arithmeticEmbedding g ht
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro j hj;fin_cases j
      all_goals first | rfl | exact False.elim (hj 10 rfl) | exact False.elim (hj 13 rfl)
  have h₃ : (clear (11:Fin 19)).Executes g s₂ s₃ ((signedBits a).length+1) := by
    convert clear_executes g (11:Fin 19) s₂ using 1
    funext i;fin_cases i <;> rfl
  have h₄ : (clear (13:Fin 19)).Executes g s₃ s₄ ((signedBits (x-a)).length+1) := by
    convert clear_executes g (13:Fin 19) s₃ using 1
    funext i;fin_cases i <;> rfl
  have h₅ : (push (13:Fin 19) false).Executes g s₄ s₅ 1 := by
    convert push_executes g (13:Fin 19) false s₄ using 1
    funext i;fin_cases i <;> rfl
  have h₆ : (clear (18:Fin 19)).Executes g s₅ s₆ 2 := by
    convert clear_executes g (18:Fin 19) s₅ using 1
    funext i;fin_cases i <;> rfl
  have hna : (signedBits (-a)).length≤B := by simpa [signedBits] using ha
  have hd := operation_bitLength .add x (-a) B hx hna
  change (signedBits (x+-a)).length≤2*B+3 at hd
  rw [←sub_eq_add_neg] at hd
  refine ⟨(5*(signedBits a).length+3)+(t+(((signedBits a).length+1)+(((signedBits (x-a)).length+1)+(1+2+2)+2)+2)+2)+2,
    seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃
      (seq_executes _ _ g h₄ (seq_executes _ _ g h₅ h₆)))),?_⟩
  simp only [bodyTime,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

theorem body_queryFree : body.QueryFree :=
  seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _)
    (seq_queryFree _ _ (rename_queryFree _ _ (compile_queryFree code))
      (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
        (seq_queryFree _ _ (push_queryFree _ _) (clear_queryFree _)))))
end HiddenCircuits.Circuit.Runtime.SpectralDenominator
