import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit

/-! One counted iteration of the uniform consecutive-weight stream generator. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock OracleMachine

 def denominatorAt (d i : ℕ) : BitString :=
  if h : i<d+1 then signedBits (interpolationDenominator d ⟨i,h⟩) else []
 def negativeNumeratorAt (d i : ℕ) : BitString :=
  if h : i<d+1 then signedBits (interpolationNegativeNumerator d ⟨i,h⟩) else []
 def weightWordBound (d : ℕ) : ℕ := (d+1)^2+2

 theorem denominatorAt_length (d i : ℕ) : (denominatorAt d i).length ≤ weightWordBound d := by
  unfold denominatorAt
  split
  · rename_i h
    have hh := (interpolation_weights_bit_bound d ⟨i,h⟩).1
    have hp : d^2 ≤ (d+1)^2 := Nat.pow_le_pow_left (Nat.le_succ d) 2
    simp only [signedBits,List.length_cons,encodeNat_length,weightWordBound]
    omega
  · simp

 theorem negativeNumeratorAt_length (d i : ℕ) : (negativeNumeratorAt d i).length ≤ weightWordBound d := by
  unfold negativeNumeratorAt
  split
  · rename_i h
    have hh := (interpolation_weights_bit_bound d ⟨i,h⟩).2
    have hp : d^2 ≤ (d+1)^2 := Nat.pow_le_pow_left (Nat.le_succ d) 2
    simp only [signedBits,List.length_cons,encodeNat_length,weightWordBound]
    omega
  · simp

/-- Work registers 0--11; increasing/decreasing unary indices 12/13; loop
clock 14; the two reverse output streams 15/16. -/
 def weightStreamStore (i k : ℕ) (a b clock outD outN : BitString) : Store 16 := fun j =>
  if j.val=0 then a else if j.val=1 then b else if j.val=12 then List.replicate i true
  else if j.val=13 then List.replicate k true else if j.val=14 then clock
  else if j.val=15 then outD else if j.val=16 then outN else []

 def weightStreamPairEmbedding : Fin 12 ↪ Fin 17 where
  toFun j := j.castLE (by decide)
  inj' := by intro i j h; exact Fin.ext (congrArg (fun q : Fin 17 => q.val) h)
 def weightStreamDenEmitEmbedding : Fin 2 ↪ Fin 17 where
  toFun j := if j=0 then 0 else 15
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
 def weightStreamNumEmitEmbedding : Fin 2 ↪ Fin 17 where
  toFun j := if j=0 then 1 else 16
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

 noncomputable def weightStreamPair : OracleBlock 16 := rename weightPairUnary weightStreamPairEmbedding
 noncomputable def weightStreamDenEmit : OracleBlock 16 := rename wordEmit weightStreamDenEmitEmbedding
 noncomputable def weightStreamNumEmit : OracleBlock 16 := rename wordEmit weightStreamNumEmitEmbedding

 def weightStreamDrop : OracleBlock 16 where
  labelCount := 2
  start := 0
  exit := 1
  code q := if q=0 then .pop 13 1 1 1 else .halt
  exit_halt := rfl
 noncomputable def weightStreamTick : OracleBlock 16 := seq (push 12 true) weightStreamDrop

 theorem weightStreamTick_executes (g : BitString → ℕ) (i k : ℕ) (clock outD outN : BitString) :
    weightStreamTick.Executes g (weightStreamStore i k [] [] clock outD outN)
      (weightStreamStore (i+1) (k-1) [] [] clock outD outN) 4 := by
  have h1 : (push (12 : Fin 17) true).Executes g
      (weightStreamStore i k [] [] clock outD outN) (weightStreamStore (i+1) k [] [] clock outD outN) 1 := by
    convert push_executes g (12 : Fin 17) true (weightStreamStore i k [] [] clock outD outN) using 1
    funext j; fin_cases j <;> simp [weightStreamStore,List.replicate_succ]
  have h2 : weightStreamDrop.Executes g (weightStreamStore (i+1) k [] [] clock outD outN)
      (weightStreamStore (i+1) (k-1) [] [] clock outD outN) 1 := by
    apply OracleMachine.Steps.single
    cases k with
    | zero => rfl
    | succ k =>
      change some ((⟨(1 : Fin 2),Function.update (weightStreamStore (i+1) (k+1) [] [] clock outD outN) (13 : Fin 17) (List.replicate k true)⟩ : weightStreamDrop.machine.Config),1) =
        some ((⟨(1 : Fin 2),weightStreamStore (i+1) k [] [] clock outD outN⟩ : weightStreamDrop.machine.Config),1)
      apply congrArg (fun s : Store 16 => some ((⟨(1 : Fin 2),s⟩ : weightStreamDrop.machine.Config),1))
      funext j; fin_cases j <;> rfl
  exact seq_executes _ _ g h1 h2

 noncomputable def weightStreamBody : OracleBlock 16 :=
  seq (copyOn 12 0 2 (by decide) (by decide) (by decide))
    (seq (copyOn 13 1 2 (by decide) (by decide) (by decide))
      (seq weightStreamPair (seq weightStreamDenEmit (seq weightStreamNumEmit weightStreamTick))))

 noncomputable def weightStreamBodyTime : Polynomial ℕ :=
  weightPairUnaryTime+5*Polynomial.X+12*((Polynomial.X+1)^2+2)+36

 theorem weightStreamBody_executes (g : BitString → ℕ) (d i : ℕ) (hi : i<d+1)
    (clock outD outN : BitString) :
    ∃ t, weightStreamBody.Executes g (weightStreamStore i (d-i) [] [] clock outD outN)
      (weightStreamStore (i+1) (d-(i+1)) [] [] clock
        ((wordChunk (denominatorAt d i)).reverse++outD)
        ((wordChunk (negativeNumeratorAt d i)).reverse++outN)) t ∧
      t+2 ≤ weightStreamBodyTime.eval d := by
  have h1 : (copyOn (12 : Fin 17) 0 2 (by decide) (by decide) (by decide)).Executes g
      (weightStreamStore i (d-i) [] [] clock outD outN)
      (weightStreamStore i (d-i) (List.replicate i true) [] clock outD outN) (5*i+2) := by
    convert copyOn_executes g (12 : Fin 17) 0 2 (by decide) (by decide) (by decide)
      (weightStreamStore i (d-i) [] [] clock outD outN) rfl using 1
    · funext j; fin_cases j <;> simp [weightStreamStore]
    · simp [weightStreamStore]
  have h2 : (copyOn (13 : Fin 17) 1 2 (by decide) (by decide) (by decide)).Executes g
      (weightStreamStore i (d-i) (List.replicate i true) [] clock outD outN)
      (weightStreamStore i (d-i) (List.replicate i true) (List.replicate (d-i) true) clock outD outN) (5*(d-i)+2) := by
    convert copyOn_executes g (13 : Fin 17) 1 2 (by decide) (by decide) (by decide)
      (weightStreamStore i (d-i) (List.replicate i true) [] clock outD outN) rfl using 1
    · funext j; fin_cases j <;> simp [weightStreamStore]
    · simp [weightStreamStore]
  obtain ⟨tp,hp,hbp⟩ := weightPairUnary_executes g d ⟨i,hi⟩
  have h3 : weightStreamPair.Executes g
      (weightStreamStore i (d-i) (List.replicate i true) (List.replicate (d-i) true) clock outD outN)
      (weightStreamStore i (d-i) (denominatorAt d i) (negativeNumeratorAt d i) clock outD outN) tp := by
    apply rename_executes_to weightPairUnary weightStreamPairEmbedding g hp
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> simp [weightStreamStore,weightPairStore,weightStreamPairEmbedding,denominatorAt,negativeNumeratorAt,hi]
    · intro j hj; fin_cases j <;> first | rfl | (exfalso; exact hj 0 rfl) | (exfalso; exact hj 1 rfl)
  have h4 : weightStreamDenEmit.Executes g
      (weightStreamStore i (d-i) (denominatorAt d i) (negativeNumeratorAt d i) clock outD outN)
      (weightStreamStore i (d-i) [] (negativeNumeratorAt d i) clock ((wordChunk (denominatorAt d i)).reverse++outD) outN)
      (6*(denominatorAt d i).length+7) := by
    apply rename_executes_to wordEmit weightStreamDenEmitEmbedding g (wordEmit_executes g _ _)
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
    · intro j hj; fin_cases j <;> first | rfl | (exfalso; exact hj 0 rfl) | (exfalso; exact hj 1 rfl)
  have h5 : weightStreamNumEmit.Executes g
      (weightStreamStore i (d-i) [] (negativeNumeratorAt d i) clock ((wordChunk (denominatorAt d i)).reverse++outD) outN)
      (weightStreamStore i (d-i) [] [] clock ((wordChunk (denominatorAt d i)).reverse++outD)
        ((wordChunk (negativeNumeratorAt d i)).reverse++outN)) (6*(negativeNumeratorAt d i).length+7) := by
    apply rename_executes_to wordEmit weightStreamNumEmitEmbedding g (wordEmit_executes g _ _)
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
    · intro j hj; fin_cases j <;> first | rfl | (exfalso; exact hj 0 rfl) | (exfalso; exact hj 1 rfl)
  have h6 := weightStreamTick_executes g i (d-i) clock
    ((wordChunk (denominatorAt d i)).reverse++outD) ((wordChunk (negativeNumeratorAt d i)).reverse++outN)
  have he : d-i-1=d-(i+1) := by omega
  rw [he] at h6
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6)))),?_⟩
  have hd := denominatorAt_length d i
  have hn := negativeNumeratorAt_length d i
  have hik : i+(d-i)=d := by omega
  simp only [weightStreamBodyTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X]
  unfold weightWordBound at hd hn
  omega

 lemma weightStreamBody_queryFree : weightStreamBody.QueryFree := by
  have ht : weightStreamDrop.QueryFree := by
    intro q i o next; fin_cases q <;> simp [machine,weightStreamDrop]
  exact seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (rename_queryFree _ _ weightPairUnary_queryFree)
        (seq_queryFree _ _ (rename_queryFree _ _ wordEmit_queryFree)
          (seq_queryFree _ _ (rename_queryFree _ _ wordEmit_queryFree)
            (seq_queryFree _ _ (push_queryFree _ _) ht)))))

end HiddenCircuits.Complexity.BinaryArithmetic
