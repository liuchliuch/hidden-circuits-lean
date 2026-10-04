import HiddenCircuits.Circuit.Runtime.SpectralCoefficientsBody

/-! A real streamed exact quotient computes target*(D/denominator) for every basis row. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralScales
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic
open HiddenCircuits.Complexity.BinaryArithmetic.RegisterMachine
open Polynomial

 def value (scale : ℤ) (p : ℤ × ℤ) : ℤ := p.2*(scale/p.1)
 def output (scale : ℤ) (ps : List (ℤ × ℤ)) : List ℤ := ps.map (value scale)

def store (scale : ℤ) (u v out flag left right emitted : BitString) : Store 20 := fun i =>
  if i.val=9 then signedBits scale else if i.val=10 then v else if i.val=11 then u else if i.val=12 then out
  else if i.val=13 then signedBits 0 else if i.val=14 then signedBits 0 else if i.val=15 then signedBits 0
  else if i.val=16 then left else if i.val=17 then emitted else if i.val=19 then flag else if i.val=20 then right else []

def leftEmbedding : Fin 4 ↪ Fin 21 where
  toFun i := if i.val=0 then 16 else if i.val=1 then 11 else if i.val=2 then 18 else 19
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
 def rightEmbedding : Fin 4 ↪ Fin 21 where
  toFun i := if i.val=0 then 20 else if i.val=1 then 10 else if i.val=2 then 18 else 19
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
 def arithmeticEmbedding : Fin 16 ↪ Fin 21 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 21 => z.val) h)
 def emitEmbedding : Fin 2 ↪ Fin 21 where
  toFun i := if i.val=0 then 12 else 17
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def parseLeft : OracleBlock 20 := GraphVerifier.Runtime.unpairOn leftEmbedding
noncomputable def parseRight : OracleBlock 20 := GraphVerifier.Runtime.unpairOn rightEmbedding
def registers (D target den out : ℤ) : Fin 7 → ℤ := fun i =>
  if i.val=0 then D else if i.val=1 then target else if i.val=2 then den else if i.val=3 then out else 0
 def code : List Instruction := [⟨.divide,3,0,2⟩,⟨.multiply,3,1,3⟩]
noncomputable def arithmeticCell : OracleBlock 15 := compile code
noncomputable def arithmeticTime : Polynomial ℕ := straightTime code
noncomputable def arithmetic : OracleBlock 20 := rename arithmeticCell arithmeticEmbedding
noncomputable def emit : OracleBlock 20 := rename wordEmit emitEmbedding
noncomputable def rightBody : OracleBlock 20 := seq parseRight (seq (clear 19) (seq (push 12 false)
  (seq arithmetic (seq (clear 10) (seq (clear 11) emit)))))
noncomputable def body : OracleBlock 20 := seq parseLeft (seq (clear 19) (branchPop 20 skip skip rightBody))
noncomputable def bodyTime : Polynomial ℕ := arithmeticTime+36*X+110

theorem parseLeft_executes (g : BitString → ℕ) (scale : ℤ) (u left right emitted : BitString) :
    parseLeft.Executes g (store scale [] [] [] [] (pairBits u left) right emitted)
      (store scale u [] [] [true] left right emitted) (5*u.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes leftEmbedding g
    (store scale [] [] [] [] (pairBits u left) right emitted) (store scale u [] [] [true] left right emitted) (pairBits u left)
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 3 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost];omega

theorem parseRight_executes (g : BitString → ℕ) (scale : ℤ) (u v left right emitted : BitString) :
    parseRight.Executes g (store scale u [] [] [] left (pairBits v right) emitted)
      (store scale u v [] [true] left right emitted) (5*v.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes rightEmbedding g
    (store scale u [] [] [] left (pairBits v right) emitted) (store scale u v [] [true] left right emitted) (pairBits v right)
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 3 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost];omega

theorem emit_executes (g : BitString → ℕ) (scale : ℤ) (out left right emitted : BitString) :
    emit.Executes g (store scale [] [] out [] left right emitted)
      (store scale [] [] [] [] left right ((wordChunk out).reverse++emitted)) (6*out.length+7) := by
  apply rename_executes_to wordEmit emitEmbedding g (wordEmit_executes g out emitted)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl)

theorem evaluate_code (D target den out : ℤ) :
    evaluate code (registers D target den out)=registers D target den (target*(D/den)) := by
  funext i;fin_cases i <;> simp [evaluate,code,Instruction.eval,Operation.eval,registers]

theorem arithmetic_executes (g : BitString → ℕ) (scale u v : ℤ) (left right emitted : BitString) (B : ℕ)
    (hs : (signedBits scale).length≤B) (hu : (signedBits u).length≤B) (hv : (signedBits v).length≤B)
    (hne : u≠0) (hdiv : u∣scale) :
    ∃ t, arithmetic.Executes g (store scale (signedBits u) (signedBits v) (signedBits 0) [] left right emitted)
      (store scale (signedBits u) (signedBits v) (signedBits (v*(scale/u))) [] left right emitted) t ∧
      t≤arithmeticTime.eval B := by
  have hB : 1≤B := by simp only [signedBits,List.length_cons] at hs;omega
  have hb : Bounded B (registers scale v u 0) := by
    intro i;fin_cases i <;> simp only [registers] <;> first | exact hs | exact hu | exact hv | exact hB
  have hv' : Valid code (registers scale v u 0) := by
    simp [Valid,code,Operation.Valid,registers,hne,hdiv]
  obtain ⟨t,ht,hb'⟩ := compile_polynomial code g (registers scale v u 0) B hb hv'
  rw [evaluate_code] at ht
  refine ⟨t,?_,hb'⟩
  apply rename_executes_to arithmeticCell arithmeticEmbedding g ht
  · funext i;fin_cases i <;> simp [Function.comp_def,arithmeticEmbedding,store,RegisterMachine.store,registers]
  · funext i;fin_cases i <;> simp [Function.comp_def,arithmeticEmbedding,store,RegisterMachine.store,registers]
  · intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 12 rfl)

theorem output_length (scale u v : ℤ) (B : ℕ)
    (hs : (signedBits scale).length≤B) (hu : (signedBits u).length≤B) (hv : (signedBits v).length≤B) :
    (signedBits (v*(scale/u))).length≤4*B+9 := by
  have hq := operation_bitLength .divide scale u B hs hu
  have hv' : (signedBits v).length≤2*B+3 := by omega
  have hm := operation_bitLength .multiply v (scale/u) (2*B+3) hv' hq
  simpa only [Operation.eval,show 2*(2*B+3)+3=4*B+9 by ring] using hm

theorem rightBody_executes (g : BitString → ℕ) (scale u v : ℤ) (left right emitted : BitString) (B : ℕ)
    (hs : (signedBits scale).length≤B) (hu : (signedBits u).length≤B) (hv : (signedBits v).length≤B)
    (hne : u≠0) (hdiv : u∣scale) :
    ∃ t, rightBody.Executes g (store scale (signedBits u) [] [] [] left (pairBits (signedBits v) right) emitted)
      (store scale [] [] [] [] left right ((wordChunk (signedBits (v*(scale/u)))).reverse++emitted)) t ∧
      t≤arithmeticTime.eval B+31*B+90 := by
  let s₀ := store scale (signedBits u) [] [] [] left (pairBits (signedBits v) right) emitted
  let s₁ := store scale (signedBits u) (signedBits v) [] [true] left right emitted
  let s₂ := store scale (signedBits u) (signedBits v) [] [] left right emitted
  let s₃ := store scale (signedBits u) (signedBits v) (signedBits 0) [] left right emitted
  let s₄ := store scale (signedBits u) (signedBits v) (signedBits (v*(scale/u))) [] left right emitted
  let s₅ := store scale (signedBits u) [] (signedBits (v*(scale/u))) [] left right emitted
  let s₆ := store scale [] [] (signedBits (v*(scale/u))) [] left right emitted
  have h₁ : parseRight.Executes g s₀ s₁ (5*(signedBits v).length+3) := parseRight_executes g _ _ _ _ _ _
  have h₂ : (clear (19:Fin 21)).Executes g s₁ s₂ 2 := by
    convert clear_executes g (19:Fin 21) s₁ using 1
    funext i;fin_cases i <;> rfl
  have h₃ : (push (12:Fin 21) false).Executes g s₂ s₃ 1 := by
    convert push_executes g (12:Fin 21) false s₂ using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨t,ht,htb⟩ := arithmetic_executes g scale u v left right emitted B hs hu hv hne hdiv
  have h₅ : (clear (10:Fin 21)).Executes g s₄ s₅ ((signedBits v).length+1) := by
    convert clear_executes g (10:Fin 21) s₄ using 1
    funext i;fin_cases i <;> rfl
  have h₆ : (clear (11:Fin 21)).Executes g s₅ s₆ ((signedBits u).length+1) := by
    convert clear_executes g (11:Fin 21) s₅ using 1
    funext i;fin_cases i <;> rfl
  have h₇ := emit_executes g scale (signedBits (v*(scale/u))) left right emitted
  refine ⟨(5*(signedBits v).length+3)+(2+(1+(t+(((signedBits v).length+1)+(((signedBits u).length+1)+(6*(signedBits (v*(scale/u))).length+7)+2)+2)+2)+2)+2)+2,
    seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃
      (seq_executes _ _ g ht (seq_executes _ _ g h₅ (seq_executes _ _ g h₆ h₇))))),?_⟩
  have ho := output_length scale u v B hs hu hv
  omega

theorem body_executes (g : BitString → ℕ) (scale u v : ℤ) (left right emitted : BitString) (B : ℕ)
    (hs : (signedBits scale).length≤B) (hu : (signedBits u).length≤B) (hv : (signedBits v).length≤B)
    (hne : u≠0) (hdiv : u∣scale) :
    ∃ t, body.Executes g (store scale [] [] [] [] (pairBits (signedBits u) left)
        (true::pairBits (signedBits v) right) emitted)
      (store scale [] [] [] [] left right ((wordChunk (signedBits (v*(scale/u)))).reverse++emitted)) t ∧
      t≤bodyTime.eval B := by
  have h₁ := parseLeft_executes g scale (signedBits u) left (true::pairBits (signedBits v) right) emitted
  let s₁ := store scale (signedBits u) [] [] [true] left (true::pairBits (signedBits v) right) emitted
  let s₂ := store scale (signedBits u) [] [] [] left (true::pairBits (signedBits v) right) emitted
  have h₂ : (clear (19:Fin 21)).Executes g s₁ s₂ 2 := by
    convert clear_executes g (19:Fin 21) s₁ using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨t,ht,htb⟩ := rightBody_executes g scale u v left right emitted B hs hu hv hne hdiv
  have he : Function.update s₂ (20:Fin 21) (pairBits (signedBits v) right)=
      store scale (signedBits u) [] [] [] left (pairBits (signedBits v) right) emitted := by
    funext i;fin_cases i <;> rfl
  have h₃ := branchPop_true (20:Fin 21) skip skip rightBody g (s:=s₂) (rest:=pairBits (signedBits v) right) rfl
    (by rw [he];exact ht)
  refine ⟨(5*(signedBits u).length+3)+(2+(t+2)+2)+2,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃),?_⟩
  simp only [bodyTime,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

theorem body_queryFree : body.QueryFree :=
  seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree
      (seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _)
        (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (push_queryFree _ _)
          (seq_queryFree _ _ (rename_queryFree _ _ (compile_queryFree code))
            (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
              (rename_queryFree _ _ wordEmit_queryFree)))))))))
end HiddenCircuits.Circuit.Runtime.SpectralScales
