import HiddenCircuits.Complexity.BinaryArithmetic.Runtime
import HiddenCircuits.Complexity.GraphVerifier.RuntimeLibrary
import HiddenCircuits.Complexity.BitList

/-! An actual finite bit-stack product fold over self-delimiting signed words.
The supplied bound concerns only mathematical bit lengths, never runtime. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock OracleMachine

/-- Bound all input operands and the actual successive accumulator values. -/
def ProductBitBound (B : ℕ) : ℤ → List ℤ → Prop
  | a, [] => (signedBits a).length ≤ B
  | a, z::zs => (signedBits a).length ≤ B ∧ (signedBits z).length ≤ B ∧ ProductBitBound B (a*z) zs

lemma ProductBitBound.head {B : ℕ} {a : ℤ} {zs : List ℤ} (h : ProductBitBound B a zs) :
    (signedBits a).length ≤ B := by
  cases zs with
  | nil => exact h
  | cons z zs => exact h.1

def productStore (acc item result tmp flag spare stream : BitString) : Store 6 := fun i =>
  if i.val=0 then acc else if i.val=1 then item else if i.val=2 then result
  else if i.val=3 then tmp else if i.val=4 then flag else if i.val=5 then spare else stream

def productParseEmbedding : Fin 4 ↪ Fin 7 where
  toFun i := if i.val=0 then 6 else if i.val=1 then 1 else if i.val=2 then 3 else 4
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def productParse : OracleBlock 6 := GraphVerifier.Runtime.unpairOn productParseEmbedding

lemma pair_parse_cost (x y : BitString) : GraphVerifier.parseCost (pairBits x y)=3*x.length+2 := by
  induction x with
  | nil => rfl
  | cons b xs ih => simp [pairBits,GraphVerifier.parseCost,ih]; omega

theorem productParse_executes (g : BitString → ℕ) (acc item rest : BitString) :
    productParse.Executes g (productStore acc [] [] [] [] [] (pairBits item rest))
      (productStore acc item [] [] [true] [] rest) (5*item.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes productParseEmbedding g
    (productStore acc [] [] [] [] [] (pairBits item rest))
    (productStore acc item [] [] [true] [] rest) (pairBits item rest)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by
      intro j hj
      fin_cases j
      · rfl
      · exact False.elim (hj 1 rfl)
      · rfl
      · rfl
      · exact False.elim (hj 3 rfl)
      · rfl
      · exact False.elim (hj 0 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost]; omega

def productMulEmbedding : Fin 6 ↪ Fin 7 where
  toFun i := i.castLE (by decide)
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 7 => x.val) h)

noncomputable def productMultiply : OracleBlock 6 := rename signedMultiplicationBlock productMulEmbedding

theorem productMultiply_executes (g : BitString → ℕ) (a z : ℤ) (rest : BitString) :
    ∃ t, productMultiply.Executes g (productStore (signedBits a) (signedBits z) [] [] [] [] rest)
      (productStore [] (Computability.encodeNat z.natAbs) (signedBits (a*z)) [] [] [] rest) t ∧
      t ≤ integerMultiplicationTime.eval ((signedBits a).length+(signedBits z).length) := by
  obtain ⟨t,ht,hb⟩ := signed_multiply_polynomial g a z
  refine ⟨t,?_,hb⟩
  apply rename_executes_to signedMultiplicationBlock productMulEmbedding g ht
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · intro j hj
    fin_cases j
    · exact False.elim (hj 0 rfl)
    · exact False.elim (hj 1 rfl)
    · exact False.elim (hj 2 rfl)
    · rfl
    · rfl
    · rfl
    · rfl

/-- Restore the new signed accumulator to stack zero and clear the retained operand. -/
noncomputable def productRestore : OracleBlock 6 :=
  seq (clear 1) (seq (reverseOn 2 3 (by decide)) (reverseOn 3 0 (by decide)))

theorem productRestore_executes (g : BitString → ℕ) (item result rest : BitString) :
    productRestore.Executes g (productStore [] item result [] [] [] rest)
      (productStore result [] [] [] [] [] rest) (item.length+4*result.length+7) := by
  have hc : (clear (1 : Fin 7)).Executes g (productStore [] item result [] [] [] rest)
      (productStore [] [] result [] [] [] rest) (item.length+1) := by
    convert clear_executes g (1 : Fin 7) (productStore [] item result [] [] [] rest) using 1
    funext i; fin_cases i <;> rfl
  have hr₁ : (reverseOn (2 : Fin 7) 3 (by decide)).Executes g (productStore [] [] result [] [] [] rest)
      (productStore [] [] [] result.reverse [] [] rest) (2*result.length+1) := by
    convert reverseOn_executes g (2 : Fin 7) 3 (by decide) (productStore [] [] result [] [] [] rest) using 1
    funext i; fin_cases i <;> simp [productStore]
  have hr₂ : (reverseOn (3 : Fin 7) 0 (by decide)).Executes g (productStore [] [] [] result.reverse [] [] rest)
      (productStore result [] [] [] [] [] rest) (2*result.length+1) := by
    convert reverseOn_executes g (3 : Fin 7) 0 (by decide) (productStore [] [] [] result.reverse [] [] rest) using 1
    · funext i; fin_cases i <;> simp [productStore]
    · simp [productStore]
  have h := seq_executes _ _ g hc (seq_executes _ _ g hr₁ hr₂)
  convert h using 1 <;> omega

noncomputable def productBody : OracleBlock 6 :=
  seq productParse (seq (clear 4) (seq productMultiply productRestore))

def productIterationBound (B : ℕ) : ℕ := 50*(2*B+1)^3+10*B+20

theorem productBody_executes (g : BitString → ℕ) (a z : ℤ) (rest : BitString) (B : ℕ)
    (ha : (signedBits a).length≤B) (hz : (signedBits z).length≤B) (hp : (signedBits (a*z)).length≤B) :
    ∃ t, productBody.Executes g (productStore (signedBits a) [] [] [] [] [] (pairBits (signedBits z) rest))
      (productStore (signedBits (a*z)) [] [] [] [] [] rest) t ∧ t+2≤productIterationBound B := by
  have hparse := productParse_executes g (signedBits a) (signedBits z) rest
  have hclear : (clear (4 : Fin 7)).Executes g (productStore (signedBits a) (signedBits z) [] [] [true] [] rest)
      (productStore (signedBits a) (signedBits z) [] [] [] [] rest) 2 := by
    convert clear_executes g (4 : Fin 7) (productStore (signedBits a) (signedBits z) [] [] [true] [] rest) using 1
    funext i; fin_cases i <;> rfl
  obtain ⟨t,hm,ht⟩ := productMultiply_executes g a z rest
  have hr := productRestore_executes g (Computability.encodeNat z.natAbs) (signedBits (a*z)) rest
  have h := seq_executes _ _ g hparse (seq_executes _ _ g hclear (seq_executes _ _ g hm hr))
  refine ⟨_,h,?_⟩
  have hmBound : t≤50*(2*B+1)^3 := by
    apply ht.trans
    simp only [integerMultiplicationTime,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    gcongr
    omega
  have hz' : (Computability.encodeNat z.natAbs).length≤B := by
    simp only [signedBits,List.length_cons] at hz; omega
  unfold productIterationBound
  omega

noncomputable def productAccumulator : OracleBlock 6 := whilePop 6 skip productBody

/-- The encoded stream is parsed and folded by a single fixed finite program.
Its polynomial bound is linear in the number of factors and cubic in B. -/
theorem productAccumulator_while (g : BitString → ℕ) (zs : List ℤ) (a : ℤ) (B : ℕ)
    (hB : ProductBitBound B a zs) :
    ∃ t, WhileExecution (6 : Fin 7) skip productBody g
      (productStore (signedBits a) [] [] [] [] [] (encodeBitList (zs.map signedBits)))
      (productStore (signedBits (zs.foldl (·*·) a)) [] [] [] [] [] []) t ∧
      t≤1+zs.length*productIterationBound B := by
  induction zs generalizing a with
  | nil =>
    refine ⟨1,?_,by simp⟩
    exact WhileExecution.empty _ rfl
  | cons z zs ih =>
    obtain ⟨ha,hz,htail⟩ := hB
    obtain ⟨body,hbody,hbodyBound⟩ := productBody_executes g a z (encodeBitList (zs.map signedBits)) B ha hz htail.head
    obtain ⟨tail,ht,hbound⟩ := ih (a*z) htail
    refine ⟨2+body+tail,?_,?_⟩
    · have hs : Function.update
          (productStore (signedBits a) [] [] [] [] [] (encodeBitList ((z::zs).map signedBits))) (6 : Fin 7)
          (pairBits (signedBits z) (encodeBitList (zs.map signedBits))) =
          productStore (signedBits a) [] [] [] [] [] (pairBits (signedBits z) (encodeBitList (zs.map signedBits))) := by
        funext i; fin_cases i <;> rfl
      have hw := WhileExecution.one
        (s := productStore (signedBits a) [] [] [] [] [] (encodeBitList ((z::zs).map signedBits)))
        (rest := pairBits (signedBits z) (encodeBitList (zs.map signedBits)))
        (by rfl) (by rw [hs]; exact hbody) ht
      convert hw using 1 <;> omega
    · simp only [List.length_cons]
      nlinarith

theorem productAccumulator_executes (g : BitString → ℕ) (zs : List ℤ) (a : ℤ) (B : ℕ)
    (hB : ProductBitBound B a zs) :
    ∃ t, productAccumulator.Executes g
      (productStore (signedBits a) [] [] [] [] [] (encodeBitList (zs.map signedBits)))
      (productStore (signedBits (zs.foldl (·*·) a)) [] [] [] [] [] []) t ∧
      t≤1+zs.length*productIterationBound B := by
  obtain ⟨t,ht,hbound⟩ := productAccumulator_while g zs a B hB
  exact ⟨t,whilePop_executes _ _ _ _ ht,hbound⟩

lemma productAccumulator_queryFree : productAccumulator.QueryFree := by
  have hp : productParse.QueryFree := GraphVerifier.Runtime.unpairOn_queryFree _
  have hm : productMultiply.QueryFree := rename_queryFree _ _ signedMultiplicationBlock_queryFree
  have hr : productRestore.QueryFree := seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (reverseOn_queryFree _ _ _))
  exact whilePop_queryFree _ _ _ skip_queryFree
    (seq_queryFree _ _ hp (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ hm hr)))

end HiddenCircuits.Complexity.BinaryArithmetic
