import HiddenCircuits.Circuit.Runtime.SpectralCoefficientsStep

/-! A literal node-stream loop applies the coefficient step to every encoded root. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralCoefficients
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

noncomputable def coefficientStreamBound : Polynomial ℕ := (X+1)*(2*((X+1)*X+2)+2)
noncomputable def stepInputBound : Polynomial ℕ := X+coefficientStreamBound
noncomputable def nodeBodyTime : Polynomial ℕ := stepTime.comp stepInputBound+5*X+6*coefficientStreamBound+16

theorem coefficientStream_length (xs : List ℤ) (N : ℕ) (hlen : xs.length≤N)
    (hxs : ∀a∈xs,(signedBits a).length≤N) :
    (encodeBitList ((coefficients xs).map signedBits)).length≤coefficientStreamBound.eval N := by
  have hb : ∀c∈coefficients xs,(signedBits c).length≤(N+1)*N+2 := by
    intro c hc
    have hh := coefficients_bit_bound xs N (fun a ha => abs_le_pow_signed_length a N (hxs a ha)) c hc
    have hm := Nat.mul_le_mul_left (N+1) hlen
    omega
  have he := encodedWords_length_le ((coefficients xs).map signedBits) ((N+1)*N+2) (by
    intro w hw;obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hw;exact hb c hc)
  simp only [List.length_map,coefficients_length] at he
  apply he.trans
  simp only [coefficientStreamBound,eval_mul,eval_add,eval_X,eval_one,eval_ofNat]
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hlen 1)

def nodeStore (root coeff rest flag : BitString) : Store 22 := fun i =>
  if i.val=0 then root else if i.val=1 then coeff else if i.val=20 then rest else if i.val=22 then flag else []

def nodeParseEmbedding : Fin 4 ↪ Fin 23 where
  toFun i := if i.val=0 then 20 else if i.val=1 then 0 else if i.val=2 then 21 else 22
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
 def stepEmbedding : Fin 20 ↪ Fin 23 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 23 => z.val) h)

noncomputable def parseNode : OracleBlock 22 := GraphVerifier.Runtime.unpairOn nodeParseEmbedding
noncomputable def nodeBody : OracleBlock 22 := seq parseNode
  (seq (clear 22) (seq (rename stepProgram stepEmbedding) (moveOn 0 1 2 (by decide) (by decide) (by decide))))
noncomputable def nodeLoop : OracleBlock 22 := whilePop 20 skip nodeBody

theorem parseNode_executes (g : BitString → ℕ) (root coeff rest : BitString) :
    parseNode.Executes g (nodeStore [] coeff (pairBits root rest) []) (nodeStore root coeff rest [true])
      (5*root.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes nodeParseEmbedding g
    (nodeStore [] coeff (pairBits root rest) []) (nodeStore root coeff rest [true]) (pairBits root rest)
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by
      intro j hj;fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 3 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost]
  omega

theorem nodeBody_executes (g : BitString → ℕ) (a : ℤ) (xs : List ℤ) (rest : BitString) (N : ℕ)
    (ha : (signedBits a).length≤N) (hlen : xs.length+1≤N) (hxs : ∀z∈xs,(signedBits z).length≤N) :
    ∃ t, nodeBody.Executes g
      (nodeStore [] (encodeBitList ((coefficients xs).map signedBits)) (pairBits (signedBits a) rest) [])
      (nodeStore [] (encodeBitList ((coefficients (a::xs)).map signedBits)) rest []) t ∧ t≤nodeBodyTime.eval N := by
  let input := encodeBitList ((coefficients xs).map signedBits)
  let output := encodeBitList ((coefficients (a::xs)).map signedBits)
  let s₀ := nodeStore [] input (pairBits (signedBits a) rest) []
  let s₁ := nodeStore (signedBits a) input rest [true]
  let s₂ := nodeStore (signedBits a) input rest []
  let s₃ := nodeStore output [] rest []
  let s₄ := nodeStore [] output rest []
  have h₁ : parseNode.Executes g s₀ s₁ (5*(signedBits a).length+3) := parseNode_executes g _ _ _
  have h₂ : (clear (22:Fin 23)).Executes g s₁ s₂ 2 := by
    convert clear_executes g (22:Fin 23) s₁ using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨c,hc,hcb⟩ := stepProgram_executes g a (coefficients xs)
  rw [step_coefficients] at hc
  have h₃ : (rename stepProgram stepEmbedding).Executes g s₂ s₃ c := by
    apply rename_executes_to stepProgram stepEmbedding g hc
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro j hj;fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl)
  have h₄ : (moveOn (0:Fin 23) 1 2 (by decide) (by decide) (by decide)).Executes g s₃ s₄ (6*output.length+5) := by
    convert moveOn_executes g (0:Fin 23) 1 2 (by decide) (by decide) (by decide) s₃ rfl using 1
    funext i;fin_cases i <;> simp [s₃,s₄,nodeStore]
  have hi := coefficientStream_length xs N (by omega) hxs
  have ho := coefficientStream_length (a::xs) N (by simpa using hlen) (by
    intro z hz;rcases List.mem_cons.mp hz with rfl|hz;exact ha;exact hxs z hz)
  have hin : stepInputLength a (coefficients xs)≤stepInputBound.eval N := by
    simp only [stepInputLength,stepInputBound,eval_add,eval_X]
    omega
  have hm := polynomial_nat_eval_mono stepTime hin
  dsimp only at hm
  refine ⟨(5*(signedBits a).length+3)+(2+(c+(6*output.length+5)+2)+2)+2,
    seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),?_⟩
  simp only [nodeBodyTime,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat]
  dsimp [output]
  omega

theorem nodeLoop_executes (g : BitString → ℕ) (todo done : List ℤ) (N : ℕ)
    (hlen : todo.length+done.length≤N)
    (htodo : ∀z∈todo,(signedBits z).length≤N) (hdone : ∀z∈done,(signedBits z).length≤N) :
    ∃ t, nodeLoop.Executes g
      (nodeStore [] (encodeBitList ((coefficients done).map signedBits)) (encodeBitList (todo.map signedBits)) [])
      (nodeStore [] (encodeBitList ((coefficients (todo.reverse++done)).map signedBits)) [] []) t ∧
      t≤todo.length*(nodeBodyTime.eval N+2)+1 := by
  suffices ∃ t, WhileExecution (20:Fin 23) skip nodeBody g
      (nodeStore [] (encodeBitList ((coefficients done).map signedBits)) (encodeBitList (todo.map signedBits)) [])
      (nodeStore [] (encodeBitList ((coefficients (todo.reverse++done)).map signedBits)) [] []) t ∧
      t≤todo.length*(nodeBodyTime.eval N+2)+1 by
    obtain ⟨t,ht,hb⟩ := this
    exact ⟨t,whilePop_executes _ _ _ g ht,hb⟩
  induction todo generalizing done with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa [encodeBitList] using (WhileExecution.empty (stack:=(20:Fin 23)) (B:=skip) (C:=nodeBody)
      (g:=g) (nodeStore [] (encodeBitList ((coefficients done).map signedBits)) [] []) rfl)
  | cons a todo ih =>
    have ha := htodo a (by simp)
    have ht' : ∀z∈todo,(signedBits z).length≤N := fun z hz => htodo z (by simp [hz])
    have hd' : ∀z∈a::done,(signedBits z).length≤N := by
      intro z hz;rcases List.mem_cons.mp hz with rfl|hz;exact ha;exact hdone z hz
    obtain ⟨c,hc,hcb⟩ := nodeBody_executes g a done (encodeBitList (todo.map signedBits)) N ha (by simp at hlen;omega) hdone
    obtain ⟨t,ht,htb⟩ := ih (a::done) (by simp at hlen ⊢;omega) ht' hd'
    have he : Function.update
        (nodeStore [] (encodeBitList ((coefficients done).map signedBits)) (encodeBitList ((a::todo).map signedBits)) []) (20:Fin 23)
        (pairBits (signedBits a) (encodeBitList (todo.map signedBits)))=
        nodeStore [] (encodeBitList ((coefficients done).map signedBits)) (pairBits (signedBits a) (encodeBitList (todo.map signedBits))) [] := by
      funext i;fin_cases i <;> rfl
    rw [←he] at hc
    have hh := WhileExecution.one
      (show nodeStore [] (encodeBitList ((coefficients done).map signedBits)) (encodeBitList ((a::todo).map signedBits)) [] 20=
        true::pairBits (signedBits a) (encodeBitList (todo.map signedBits)) from rfl) hc ht
    refine ⟨1+c+1+t,?_,?_⟩
    · simpa [List.reverse_cons,List.append_assoc] using hh
    · simp only [List.length_cons]
      nlinarith

theorem nodeLoop_queryFree : nodeLoop.QueryFree :=
  whilePop_queryFree _ _ _ skip_queryFree
    (seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _)
      (seq_queryFree _ _ (clear_queryFree _)
        (seq_queryFree _ _ (rename_queryFree _ _ stepProgram_queryFree) (moveOn_queryFree _ _ _ _ _ _))))
end HiddenCircuits.Circuit.Runtime.SpectralCoefficients
