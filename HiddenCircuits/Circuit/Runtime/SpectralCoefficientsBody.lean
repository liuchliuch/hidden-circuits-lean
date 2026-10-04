import HiddenCircuits.Circuit.Runtime.SpectralCoefficientsCell
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorProduct

/-! One actual self-delimiting coefficient read, arithmetic update, and signed-word emission. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralCoefficients
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic
open HiddenCircuits.Complexity.BinaryArithmetic.RegisterMachine

def streamStore (a prev : ℤ) (c out flag stream emitted : BitString) : Store 19 := fun i =>
  if i.val=9 then signedBits (-a) else if i.val=10 then signedBits prev
  else if i.val=11 then c else if i.val=12 then out else if i.val=13 then signedBits 0
  else if i.val=14 then signedBits 0 else if i.val=15 then signedBits 0
  else if i.val=16 then stream else if i.val=17 then emitted else if i.val=19 then flag else []

def parseEmbedding : Fin 4 ↪ Fin 20 where
  toFun i := if i.val=0 then 16 else if i.val=1 then 11 else if i.val=2 then 18 else 19
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
 def arithmeticEmbedding : Fin 16 ↪ Fin 20 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 20 => z.val) h)
 def emitEmbedding : Fin 2 ↪ Fin 20 where
  toFun i := if i.val=0 then 12 else 17
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def parseCell : OracleBlock 19 := GraphVerifier.Runtime.unpairOn parseEmbedding
noncomputable def emitCell : OracleBlock 19 := rename wordEmit emitEmbedding
noncomputable def body : OracleBlock 19 :=
  seq parseCell (seq (clear 19) (seq (push 12 false)
    (seq (rename arithmeticCell arithmeticEmbedding) (seq (clear 10)
      (seq (moveOn 11 10 2 (by decide) (by decide) (by decide)) emitCell)))))
noncomputable def bodyTime : Polynomial ℕ := arithmeticTime+36*Polynomial.X+85

theorem parseCell_executes (g : BitString → ℕ) (a prev : ℤ) (c rest emitted : BitString) :
    parseCell.Executes g (streamStore a prev [] [] [] (pairBits c rest) emitted)
      (streamStore a prev c [] [true] rest emitted) (5*c.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes parseEmbedding g
    (streamStore a prev [] [] [] (pairBits c rest) emitted)
    (streamStore a prev c [] [true] rest emitted) (pairBits c rest)
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by
      intro j hj
      fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 3 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost]
  omega

theorem emitCell_executes (g : BitString → ℕ) (a prev : ℤ) (out rest emitted : BitString) :
    emitCell.Executes g (streamStore a prev [] out [] rest emitted)
      (streamStore a prev [] [] [] rest ((wordChunk out).reverse++emitted)) (6*out.length+7) := by
  apply rename_executes_to wordEmit emitEmbedding g (wordEmit_executes g out emitted)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro j hj
    fin_cases j
    all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl)

theorem body_executes (g : BitString → ℕ) (a prev c : ℤ) (rest emitted : BitString) (B : ℕ)
    (ha : (signedBits a).length≤B) (hp : (signedBits prev).length≤B) (hc : (signedBits c).length≤B) :
    ∃ t, body.Executes g (streamStore a prev [] [] [] (pairBits (signedBits c) rest) emitted)
      (streamStore a c [] [] [] rest ((wordChunk (signedBits (prev-a*c))).reverse++emitted)) t ∧
      t≤bodyTime.eval B := by
  let s₀ := streamStore a prev [] [] [] (pairBits (signedBits c) rest) emitted
  let s₁ := streamStore a prev (signedBits c) [] [true] rest emitted
  let s₂ := streamStore a prev (signedBits c) [] [] rest emitted
  let s₃ := streamStore a prev (signedBits c) (signedBits 0) [] rest emitted
  let s₄ := streamStore a prev (signedBits c) (signedBits (prev-a*c)) [] rest emitted
  let s₅ := Function.update s₄ (10:Fin 20) []
  let s₆ := streamStore a c [] (signedBits (prev-a*c)) [] rest emitted
  have h₁ : parseCell.Executes g s₀ s₁ (5*(signedBits c).length+3) := parseCell_executes g a prev _ rest emitted
  have h₂ : (clear (19:Fin 20)).Executes g s₁ s₂ 2 := by
    convert clear_executes g (19:Fin 20) s₁ using 1
    funext i;fin_cases i <;> rfl
  have h₃ : (push (12:Fin 20) false).Executes g s₂ s₃ 1 := by
    convert push_executes g (12:Fin 20) false s₂ using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨t,ht,htb⟩ := arithmetic_executes g a prev c B ha hp hc
  have h₄ : (rename arithmeticCell arithmeticEmbedding).Executes g s₃ s₄ t := by
    apply rename_executes_to arithmeticCell arithmeticEmbedding g ht
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro j hj
      fin_cases j
      all_goals first | rfl | exact False.elim (hj 12 rfl)
  have h₅ : (clear (10:Fin 20)).Executes g s₄ s₅ ((signedBits prev).length+1) := clear_executes g _ s₄
  have h₆ : (moveOn (11:Fin 20) 10 2 (by decide) (by decide) (by decide)).Executes g s₅ s₆ (6*(signedBits c).length+5) := by
    convert moveOn_executes g (11:Fin 20) 10 2 (by decide) (by decide) (by decide) s₅ rfl using 1
    funext i;fin_cases i <;> simp [s₅,s₄,s₆,streamStore]
  have h₇ := emitCell_executes g a c (signedBits (prev-a*c)) rest emitted
  refine ⟨(5*(signedBits c).length+3)+(2+(1+(t+(((signedBits prev).length+1)+((6*(signedBits c).length+5)+(6*(signedBits (prev-a*c)).length+7)+2)+2)+2)+2)+2)+2,
    seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃
      (seq_executes _ _ g h₄ (seq_executes _ _ g h₅ (seq_executes _ _ g h₆ h₇))))),?_⟩
  have ho := cell_output_length a prev c B ha hp hc
  simp only [bodyTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
  omega

theorem body_queryFree : body.QueryFree :=
  seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (push_queryFree _ _)
      (seq_queryFree _ _ (rename_queryFree _ _ (compile_queryFree cellCode))
        (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
          (rename_queryFree _ _ wordEmit_queryFree))))))
end HiddenCircuits.Circuit.Runtime.SpectralCoefficients
