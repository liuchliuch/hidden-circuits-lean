import HiddenCircuits.DH.Runtime.FinalProductModel

/-! Actual parsing, root selection and multiplication for one live-table row. -/
namespace HiddenCircuits.DH.Runtime.FinalProduct
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 800000

lemma parseLive_executes (g : BitString→ℕ) (b : Bool) (ls ts acc : BitString) :
    parseLive.Executes g (store (pairBits [b] ls) ts [] [] acc [])
      (store ls ts [] [b] acc []) 12 := by
  apply Circuit.Runtime.SamplePairParser.on_executes liveMap g [b] ls
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro j hj;fin_cases j <;> first | rfl | (exfalso;exact hj 0 rfl) | (exfalso;exact hj 1 rfl)

lemma parseRow_executes (g : BitString→ℕ) (ls ts row mark acc : BitString) :
    parseRow.Executes g (store ls (true::pairBits row ts) [] mark acc [])
      (store ls ts row mark acc []) (5*row.length+9) := by
  apply branchPop_true 1 _ _ _ g (by rfl)
  have he : Function.update (store ls (true::pairBits row ts) [] mark acc []) (1:Fin 14) (pairBits row ts)=
      store ls (pairBits row ts) [] mark acc [] := by funext i;fin_cases i <;> rfl
  rw [he]
  apply Circuit.Runtime.SamplePairParser.on_executes rowMap g row ts
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro j hj;fin_cases j <;> first | rfl | (exfalso;exact hj 0 rfl) | (exfalso;exact hj 1 rfl)

lemma parseHead_executes (g : BitString→ℕ) (ls ts row word mark acc : BitString) :
    parseHead.Executes g (store ls ts (true::pairBits word row) mark acc [])
      (store ls ts row mark acc word) (5*word.length+9) := by
  apply branchPop_true 2 _ _ _ g (by rfl)
  have he : Function.update (store ls ts (true::pairBits word row) mark acc []) (2:Fin 14) (pairBits word row)=
      store ls ts (pairBits word row) mark acc [] := by funext i;fin_cases i <;> rfl
  rw [he]
  apply Circuit.Runtime.SamplePairParser.on_executes headMap g word row
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro j hj;fin_cases j <;> first | rfl | (exfalso;exact hj 0 rfl) | (exfalso;exact hj 1 rfl)

lemma multiply_executes (g : BitString→ℕ) (ls ts : BitString) (a x : ℕ) :
    ∃c,multiply.Executes g (store ls ts [] [] (signedBits (a:ℤ)) (signedBits (x:ℤ)))
      (store ls ts [] [] (signedBits ((a*x:ℕ):ℤ)) []) c ∧
      c≤operationTime.eval ((signedBits (a:ℤ)).length+(signedBits (x:ℤ)).length) := by
  obtain ⟨c,hc,hb⟩:=Operation.executes .multiply g (a:ℤ) (x:ℤ) trivial
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ mulMap g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> simp [store,mulMap,Operation.eval,binaryStore]
  · intro j hj;fin_cases j <;> first | rfl | (exfalso;exact hj 0 rfl) | (exfalso;exact hj 1 rfl)

lemma choose_executes (g : BitString→ℕ) (b : Bool) (ls ts : BitString) (a x B R : ℕ)
    (ha : (signedBits (a:ℤ)).length≤B) (hx : (signedBits (x:ℤ)).length≤R) :
    ∃c,choose.Executes g (store ls ts [] [b] (signedBits (a:ℤ)) (signedBits (x:ℤ)))
      (store ls ts [] [] (signedBits ((a*(if b then x else 1):ℕ):ℤ)) []) c ∧
      c≤operationTime.eval (B+R)+R+3 := by
  cases b with
  | false =>
    have hc : (clear (5:Fin 14)).Executes g
        (store ls ts [] [] (signedBits (a:ℤ)) (signedBits (x:ℤ)))
        (store ls ts [] [] (signedBits (a:ℤ)) []) ((signedBits (x:ℤ)).length+1) := by
      convert clear_executes g (5:Fin 14) (store ls ts [] [] (signedBits (a:ℤ)) (signedBits (x:ℤ))) using 1
      funext i;fin_cases i <;> rfl
    refine ⟨(signedBits (x:ℤ)).length+3,?_,by omega⟩
    simp only [Bool.false_eq_true,↓reduceIte,Nat.mul_one]
    apply branchPop_false 3 _ _ _ g (by rfl)
    convert hc using 1
    · funext i;fin_cases i <;> rfl
  | true =>
    obtain ⟨c,hc,hb⟩:=multiply_executes g ls ts a x
    refine ⟨c+2,?_,?_⟩
    · simp only [↓reduceIte]
      apply branchPop_true 3 _ _ _ g (by rfl)
      convert hc using 1
      · funext i;fin_cases i <;> rfl
    · have hm:=polynomial_nat_eval_mono operationTime (Nat.add_le_add ha hx)
      dsimp only at hm
      omega

lemma body_executes (g : BitString→ℕ) (b : Bool) (x a B R : ℕ) (row : List ℕ) (xs : Rows)
    (ha : (signedBits (a:ℤ)).length≤B) (hr : (NumericEncoding.rowBits (x::row)).length≤R) :
    ∃c,body.Executes g
      (store (pairBits [b] (live xs)) (table ((b,x::row)::xs)) [] [] (signedBits (a:ℤ)) [])
      (loopStore xs (a*(if b then x else 1))) c ∧ c≤bodyBound B R := by
  have hp:=parseLive_executes g b (live xs) (table ((b,x::row)::xs)) (signedBits (a:ℤ))
  have hrp:=parseRow_executes g (live xs) (table xs) (NumericEncoding.rowBits (x::row)) [b] (signedBits (a:ℤ))
  have hhead:=parseHead_executes g (live xs) (table xs) (NumericEncoding.rowBits row)
    (signedBits (x:ℤ)) [b] (signedBits (a:ℤ))
  have hclear : (clear (2:Fin 14)).Executes g
      (store (live xs) (table xs) (NumericEncoding.rowBits row) [b] (signedBits (a:ℤ)) (signedBits (x:ℤ)))
      (store (live xs) (table xs) [] [b] (signedBits (a:ℤ)) (signedBits (x:ℤ)))
      ((NumericEncoding.rowBits row).length+1) := by
    convert clear_executes g (2:Fin 14) (store (live xs) (table xs) (NumericEncoding.rowBits row) [b]
      (signedBits (a:ℤ)) (signedBits (x:ℤ))) using 1
    funext i;fin_cases i <;> rfl
  have hlen : (NumericEncoding.rowBits (x::row)).length=
      2*(signedBits (x:ℤ)).length+(NumericEncoding.rowBits row).length+2 := by
    rw [rowBits_cons,List.length_cons,pairBits_length]
  have hx : (signedBits (x:ℤ)).length≤R := by omega
  obtain ⟨c,hc,hb⟩:=choose_executes g b (live xs) (table xs) a x B R ha hx
  have he:=seq_executes _ _ g hp (seq_executes _ _ g hrp (seq_executes _ _ g hhead (seq_executes _ _ g hclear hc)))
  refine ⟨12+(5*(NumericEncoding.rowBits (x::row)).length+9+
    (5*(signedBits (x:ℤ)).length+9+((NumericEncoding.rowBits row).length+1+c+2)+2)+2)+2,?_,?_⟩
  · exact he
  · dsimp only [bodyBound]
    omega

lemma body_queryFree : body.QueryFree := seq_queryFree _ _ (Circuit.Runtime.SamplePairParser.on_queryFree _)
  (seq_queryFree _ _ (branchPop_queryFree _ _ _ _ skip_queryFree
      (Circuit.Runtime.SamplePairParser.on_queryFree _) (Circuit.Runtime.SamplePairParser.on_queryFree _))
    (seq_queryFree _ _ (branchPop_queryFree _ _ _ _ skip_queryFree
        (Circuit.Runtime.SamplePairParser.on_queryFree _) (Circuit.Runtime.SamplePairParser.on_queryFree _))
      (seq_queryFree _ _ (clear_queryFree _) (branchPop_queryFree _ _ _ _ skip_queryFree
        (clear_queryFree _) (rename_queryFree _ _ (Operation.queryFree _))))))
end HiddenCircuits.DH.Runtime.FinalProduct
