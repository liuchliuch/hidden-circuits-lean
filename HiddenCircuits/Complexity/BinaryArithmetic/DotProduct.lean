import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorRuntime

/-! Actual finite signed dot-product computation from two canonical streams. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock OracleMachine

def dotStore (a b product tmp flag spare acc left right : BitString) : Store 8 := fun i =>
  if i.val=0 then a else if i.val=1 then b else if i.val=2 then product
  else if i.val=3 then tmp else if i.val=4 then flag else if i.val=5 then spare
  else if i.val=6 then acc else if i.val=7 then left else right

def dotLeftEmbedding : Fin 4 ↪ Fin 9 where
  toFun i := if i.val=0 then 7 else if i.val=1 then 0 else if i.val=2 then 3 else 4
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def dotRightEmbedding : Fin 4 ↪ Fin 9 where
  toFun i := if i.val=0 then 8 else if i.val=1 then 1 else if i.val=2 then 3 else 4
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def dotMulEmbedding : Fin 6 ↪ Fin 9 where
  toFun i := i.castLE (by decide)
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 9 => x.val) h)

def dotAddEmbedding : Fin 7 ↪ Fin 9 where
  toFun i := if i.val=0 then 6 else if i.val=1 then 2 else if i.val=2 then 0
    else if i.val=3 then 1 else if i.val=4 then 3 else if i.val=5 then 4 else 5
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def dotParseLeft : OracleBlock 8 := GraphVerifier.Runtime.unpairOn dotLeftEmbedding
noncomputable def dotParseRight : OracleBlock 8 := GraphVerifier.Runtime.unpairOn dotRightEmbedding
noncomputable def dotMultiply : OracleBlock 8 := rename signedMultiplicationBlock dotMulEmbedding
noncomputable def dotAdd : OracleBlock 8 := rename signedAddClean dotAddEmbedding

lemma dotParseLeft_executes (g : BitString → ℕ) (a acc left right : BitString) :
    dotParseLeft.Executes g (dotStore [] [] [] [] [] [] acc (pairBits a left) right)
      (dotStore a [] [] [] [true] [] acc left right) (5*a.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes dotLeftEmbedding g
    (dotStore [] [] [] [] [] [] acc (pairBits a left) right)
    (dotStore a [] [] [] [true] [] acc left right) (pairBits a left)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro j hj; fin_cases j <;> first | rfl | (exact False.elim (hj 0 rfl)) | (exact False.elim (hj 1 rfl)) | (exact False.elim (hj 3 rfl)))
  convert h using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost]; omega

lemma dotParseRight_executes (g : BitString → ℕ) (a b acc left right : BitString) :
    dotParseRight.Executes g (dotStore a [] [] [] [] [] acc left (pairBits b right))
      (dotStore a b [] [] [true] [] acc left right) (5*b.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes dotRightEmbedding g
    (dotStore a [] [] [] [] [] acc left (pairBits b right))
    (dotStore a b [] [] [true] [] acc left right) (pairBits b right)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro j hj; fin_cases j <;> first | rfl | (exact False.elim (hj 0 rfl)) | (exact False.elim (hj 1 rfl)) | (exact False.elim (hj 3 rfl)))
  convert h using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost]; omega

lemma dotClearFlag_executes (g : BitString → ℕ) (a b acc left right : BitString) :
    (clear (4 : Fin 9)).Executes g (dotStore a b [] [] [true] [] acc left right)
      (dotStore a b [] [] [] [] acc left right) 2 := by
  convert clear_executes g (4 : Fin 9) (dotStore a b [] [] [true] [] acc left right) using 1
  funext i; fin_cases i <;> rfl

lemma dotMultiply_executes (g : BitString → ℕ) (a b : ℤ) (acc left right : BitString) :
    ∃ t, dotMultiply.Executes g (dotStore (signedBits a) (signedBits b) [] [] [] [] acc left right)
      (dotStore [] (Computability.encodeNat b.natAbs) (signedBits (a*b)) [] [] [] acc left right) t ∧
      t ≤ integerMultiplicationTime.eval ((signedBits a).length+(signedBits b).length) := by
  obtain ⟨t,ht,hbound⟩ := signed_multiply_polynomial g a b
  refine ⟨t,?_,hbound⟩
  apply rename_executes_to signedMultiplicationBlock dotMulEmbedding g ht
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · intro j hj; fin_cases j <;> first | rfl | (exact False.elim (hj 0 rfl)) | (exact False.elim (hj 1 rfl)) | (exact False.elim (hj 2 rfl))

lemma dotClearRight_executes (g : BitString → ℕ) (b product acc left right : BitString) :
    (clear (1 : Fin 9)).Executes g (dotStore [] b product [] [] [] acc left right)
      (dotStore [] [] product [] [] [] acc left right) (b.length+1) := by
  convert clear_executes g (1 : Fin 9) (dotStore [] b product [] [] [] acc left right) using 1
  funext i; fin_cases i <;> rfl

lemma dotAdd_executes (g : BitString → ℕ) (acc product : ℤ) (left right : BitString) :
    ∃ t, dotAdd.Executes g (dotStore [] [] (signedBits product) [] [] [] (signedBits acc) left right)
      (dotStore [] [] [] [] [] [] (signedBits (acc+product)) left right) t ∧
      t≤400*(max (Computability.encodeNat acc.natAbs).length (Computability.encodeNat product.natAbs).length+1) := by
  obtain ⟨t,ht,hbound⟩ := signedAddClean_executes g acc product
  refine ⟨t,?_,hbound⟩
  apply rename_executes_to signedAddClean dotAddEmbedding g ht
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · intro j hj; fin_cases j <;> first | rfl | (exact False.elim (hj 0 rfl)) | (exact False.elim (hj 1 rfl))

noncomputable def dotRightBody : OracleBlock 8 :=
  seq dotParseRight (seq (clear 4) (seq dotMultiply (seq (clear 1) dotAdd)))
noncomputable def dotBody : OracleBlock 8 :=
  seq dotParseLeft (seq (clear 4) (branchPop 8 skip skip dotRightBody))

def dotIterationBound (B : ℕ) : ℕ := 50*(2*B+1)^3+400*(B+1)+11*B+30

lemma dotRightBody_executes (g : BitString → ℕ) (a b acc : ℤ) (left right : BitString) :
    ∃ t, dotRightBody.Executes g
      (dotStore (signedBits a) [] [] [] [] [] (signedBits acc) left (pairBits (signedBits b) right))
      (dotStore [] [] [] [] [] [] (signedBits (acc+a*b)) left right) t ∧
      t≤5*(signedBits b).length+(Computability.encodeNat b.natAbs).length+14+
        integerMultiplicationTime.eval ((signedBits a).length+(signedBits b).length)+
        400*(max (Computability.encodeNat acc.natAbs).length (Computability.encodeNat (a*b).natAbs).length+1) := by
  have hp := dotParseRight_executes g (signedBits a) (signedBits b) (signedBits acc) left right
  have hc := dotClearFlag_executes g (signedBits a) (signedBits b) (signedBits acc) left right
  obtain ⟨m,hm,hmb⟩ := dotMultiply_executes g a b (signedBits acc) left right
  have hx := dotClearRight_executes g (Computability.encodeNat b.natAbs) (signedBits (a*b)) (signedBits acc) left right
  obtain ⟨s,hs,hsb⟩ := dotAdd_executes g acc (a*b) left right
  have h := seq_executes _ _ g hp (seq_executes _ _ g hc (seq_executes _ _ g hm (seq_executes _ _ g hx hs)))
  exact ⟨_,h,by omega⟩

lemma dotBody_executes (g : BitString → ℕ) (a b acc : ℤ) (left right : BitString) (B : ℕ)
    (ha : (signedBits a).length≤B) (hb : (signedBits b).length≤B)
    (hc : (signedBits acc).length≤B) (hp : (signedBits (a*b)).length≤B) :
    ∃ t, dotBody.Executes g
      (dotStore [] [] [] [] [] [] (signedBits acc) (pairBits (signedBits a) left) (true::pairBits (signedBits b) right))
      (dotStore [] [] [] [] [] [] (signedBits (acc+a*b)) left right) t ∧ t+2≤dotIterationBound B := by
  have hl := dotParseLeft_executes g (signedBits a) (signedBits acc) left (true::pairBits (signedBits b) right)
  have hf := dotClearFlag_executes g (signedBits a) [] (signedBits acc) left (true::pairBits (signedBits b) right)
  obtain ⟨r,hr,hrb⟩ := dotRightBody_executes g a b acc left right
  have hup : Function.update
      (dotStore (signedBits a) [] [] [] [] [] (signedBits acc) left (true::pairBits (signedBits b) right)) (8 : Fin 9)
      (pairBits (signedBits b) right) =
      dotStore (signedBits a) [] [] [] [] [] (signedBits acc) left (pairBits (signedBits b) right) := by
    funext i; fin_cases i <;> rfl
  have hbranch := branchPop_true (8 : Fin 9) skip skip dotRightBody g
    (s := dotStore (signedBits a) [] [] [] [] [] (signedBits acc) left (true::pairBits (signedBits b) right))
    (rest := pairBits (signedBits b) right) rfl (by rw [hup]; exact hr)
  have h := seq_executes _ _ g hl (seq_executes _ _ g hf hbranch)
  refine ⟨_,h,?_⟩
  have hm : integerMultiplicationTime.eval ((signedBits a).length+(signedBits b).length)≤50*(2*B+1)^3 := by
    simp only [integerMultiplicationTime,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    gcongr
    omega
  simp only [signedBits,List.length_cons] at ha hb hc hp
  unfold dotIterationBound
  simp only [signedBits,List.length_cons] at *
  omega

/-- Bounds on mathematical operands, products, and successive sums only. -/
def DotBitBound (B : ℕ) : ℤ → List (ℤ×ℤ) → Prop
  | acc, [] => (signedBits acc).length≤B
  | acc, (a,b)::ps => (signedBits acc).length≤B ∧ (signedBits a).length≤B ∧
      (signedBits b).length≤B ∧ (signedBits (a*b)).length≤B ∧ DotBitBound B (acc+a*b) ps

noncomputable def dotAccumulator : OracleBlock 8 := whilePop 7 skip dotBody

lemma dotAccumulator_while (g : BitString → ℕ) (ps : List (ℤ×ℤ)) (acc : ℤ) (B : ℕ)
    (hB : DotBitBound B acc ps) :
    ∃ t, WhileExecution (7 : Fin 9) skip dotBody g
      (dotStore [] [] [] [] [] [] (signedBits acc)
        (encodeBitList (ps.map (fun p => signedBits p.1))) (encodeBitList (ps.map (fun p => signedBits p.2))))
      (dotStore [] [] [] [] [] [] (signedBits ((ps.map (fun p => p.1*p.2)).foldl (·+·) acc)) [] []) t ∧
      t≤1+ps.length*dotIterationBound B := by
  induction ps generalizing acc with
  | nil => exact ⟨1,WhileExecution.empty _ rfl,by simp⟩
  | cons p ps ih =>
    rcases p with ⟨a,b⟩
    obtain ⟨hc,ha,hb,hp,htail⟩ := hB
    obtain ⟨body,hbody,hbb⟩ := dotBody_executes g a b acc
      (encodeBitList (ps.map (fun p => signedBits p.1)))
      (encodeBitList (ps.map (fun p => signedBits p.2))) B ha hb hc hp
    obtain ⟨tail,ht,htb⟩ := ih (acc+a*b) htail
    refine ⟨2+body+tail,?_,?_⟩
    · have hup : Function.update
          (dotStore [] [] [] [] [] [] (signedBits acc)
            (encodeBitList (((a,b)::ps).map (fun p => signedBits p.1)))
            (encodeBitList (((a,b)::ps).map (fun p => signedBits p.2)))) (7 : Fin 9)
          (pairBits (signedBits a) (encodeBitList (ps.map (fun p => signedBits p.1)))) =
          dotStore [] [] [] [] [] [] (signedBits acc)
            (pairBits (signedBits a) (encodeBitList (ps.map (fun p => signedBits p.1))))
            (true::pairBits (signedBits b) (encodeBitList (ps.map (fun p => signedBits p.2)))) := by
        funext i; fin_cases i <;> rfl
      have hw := WhileExecution.one
        (s := dotStore [] [] [] [] [] [] (signedBits acc)
          (encodeBitList (((a,b)::ps).map (fun p => signedBits p.1)))
          (encodeBitList (((a,b)::ps).map (fun p => signedBits p.2))))
        (rest := pairBits (signedBits a) (encodeBitList (ps.map (fun p => signedBits p.1))))
        rfl (by rw [hup]; exact hbody) ht
      convert hw using 1 <;> omega
    · simp only [List.length_cons]
      nlinarith

theorem dotAccumulator_executes (g : BitString → ℕ) (ps : List (ℤ×ℤ)) (acc : ℤ) (B : ℕ)
    (hB : DotBitBound B acc ps) :
    ∃ t, dotAccumulator.Executes g
      (dotStore [] [] [] [] [] [] (signedBits acc)
        (encodeBitList (ps.map (fun p => signedBits p.1))) (encodeBitList (ps.map (fun p => signedBits p.2))))
      (dotStore [] [] [] [] [] [] (signedBits (acc+(ps.map (fun p => p.1*p.2)).sum)) [] []) t ∧
      t≤1+ps.length*dotIterationBound B := by
  obtain ⟨t,ht,hbound⟩ := dotAccumulator_while g ps acc B hB
  exact ⟨t,by simpa [foldl_add_eq] using whilePop_executes _ _ _ _ ht,hbound⟩

lemma dotAccumulator_queryFree : dotAccumulator.QueryFree := by
  have hm : dotMultiply.QueryFree := rename_queryFree _ _ signedMultiplicationBlock_queryFree
  have ha : dotAdd.QueryFree := rename_queryFree _ _ signedAddClean_queryFree
  have hr : dotRightBody.QueryFree := seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ hm (seq_queryFree _ _ (clear_queryFree _) ha)))
  exact whilePop_queryFree _ _ _ skip_queryFree (seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree hr)))

end HiddenCircuits.Complexity.BinaryArithmetic
