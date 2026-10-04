import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsLoop

/-! Uniform canonical interpolation-weight streams from a single unary degree. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock OracleMachine

 noncomputable def weightStreamInit : OracleBlock 16 :=
  seq (copyOn 0 13 2 (by decide) (by decide) (by decide))
    (seq (reverseOn 0 14 (by decide)) (push 14 true))

 theorem weightStreamInit_executes (g : BitString → ℕ) (d : ℕ) :
    weightStreamInit.Executes g (weightStreamStore 0 0 (List.replicate d true) [] [] [] [])
      (weightStreamStore 0 d [] [] (List.replicate (d+1) true) [] []) (7*d+8) := by
  have h1 : (copyOn (0 : Fin 17) 13 2 (by decide) (by decide) (by decide)).Executes g
      (weightStreamStore 0 0 (List.replicate d true) [] [] [] [])
      (weightStreamStore 0 d (List.replicate d true) [] [] [] []) (5*d+2) := by
    convert copyOn_executes g (0 : Fin 17) 13 2 (by decide) (by decide) (by decide)
      (weightStreamStore 0 0 (List.replicate d true) [] [] [] []) rfl using 1
    · funext j; fin_cases j <;> simp [weightStreamStore]
    · simp [weightStreamStore]
  have h2 : (reverseOn (0 : Fin 17) 14 (by decide)).Executes g
      (weightStreamStore 0 d (List.replicate d true) [] [] [] [])
      (weightStreamStore 0 d [] [] (List.replicate d true) [] []) (2*d+1) := by
    convert reverseOn_executes g (0 : Fin 17) 14 (by decide)
      (weightStreamStore 0 d (List.replicate d true) [] [] [] []) using 1
    · funext j; fin_cases j <;> simp [weightStreamStore]
    · simp [weightStreamStore]
  have h3 : (push (14 : Fin 17) true).Executes g
      (weightStreamStore 0 d [] [] (List.replicate d true) [] [])
      (weightStreamStore 0 d [] [] (List.replicate (d+1) true) [] []) 1 := by
    convert push_executes g (14 : Fin 17) true (weightStreamStore 0 d [] [] (List.replicate d true) [] []) using 1
    funext j; fin_cases j <;> simp [weightStreamStore,List.replicate_succ]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1 <;> omega

 noncomputable def weightStreamFinish : OracleBlock 16 :=
  seq (clear 12) (seq (reverseOn 15 0 (by decide)) (reverseOn 16 1 (by decide)))

 theorem weightStreamFinish_executes (g : BitString → ℕ) (i : ℕ) (outD outN : BitString) :
    weightStreamFinish.Executes g (weightStreamStore i 0 [] [] [] outD outN)
      (weightStreamStore 0 0 outD.reverse outN.reverse [] [] [])
      (i+7+2*outD.length+2*outN.length) := by
  have h1 : (clear (12 : Fin 17)).Executes g
      (weightStreamStore i 0 [] [] [] outD outN) (weightStreamStore 0 0 [] [] [] outD outN) (i+1) := by
    convert clear_executes g (12 : Fin 17) (weightStreamStore i 0 [] [] [] outD outN) using 1
    · funext j; fin_cases j <;> rfl
    · simp [weightStreamStore]
  have h2 : (reverseOn (15 : Fin 17) 0 (by decide)).Executes g
      (weightStreamStore 0 0 [] [] [] outD outN)
      (weightStreamStore 0 0 outD.reverse [] [] [] outN) (2*outD.length+1) := by
    convert reverseOn_executes g (15 : Fin 17) 0 (by decide) (weightStreamStore 0 0 [] [] [] outD outN) using 1
    funext j; fin_cases j <;> simp [weightStreamStore]
  have h3 : (reverseOn (16 : Fin 17) 1 (by decide)).Executes g
      (weightStreamStore 0 0 outD.reverse [] [] [] outN)
      (weightStreamStore 0 0 outD.reverse outN.reverse [] [] []) (2*outN.length+1) := by
    convert reverseOn_executes g (16 : Fin 17) 1 (by decide) (weightStreamStore 0 0 outD.reverse [] [] [] outN) using 1
    funext j; fin_cases j <;> simp [weightStreamStore]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1 <;> omega

/-- The instruction graph is fixed: degree and both consecutive indices live
only on bit stacks, and completed weight words are emitted by real bit loops. -/
 noncomputable def weightStreams : OracleBlock 16 :=
  seq weightStreamInit (seq weightStreamLoop weightStreamFinish)

 noncomputable def weightStreamsTime : Polynomial ℕ :=
  (Polynomial.X+1)*weightStreamBodyTime+
    4*(Polynomial.X+1)*(2*((Polynomial.X+1)^2+2)+2)+8*Polynomial.X+21

/-- Both canonical self-delimiting streams are in increasing node order.
Every register except the denominator output 0 and numerator output 1 is empty. -/
 theorem weightStreams_executes (g : BitString → ℕ) (d : ℕ) :
    ∃ t, weightStreams.Executes g (weightStreamStore 0 0 (List.replicate d true) [] [] [] [])
      (weightStreamStore 0 0 (encodeBitList (denominatorWords d))
        (encodeBitList (negativeNumeratorWords d)) [] [] []) t ∧
      t ≤ weightStreamsTime.eval d := by
  have hi := weightStreamInit_executes g d
  obtain ⟨t,ht,hbound⟩ := weightStreamLoop_all g d
  have hf := weightStreamFinish_executes g (d+1)
    (encodeBitList (denominatorWords d)).reverse (encodeBitList (negativeNumeratorWords d)).reverse
  simp only [List.reverse_reverse,List.length_reverse] at hf
  refine ⟨_,seq_executes _ _ g hi (seq_executes _ _ g ht hf),?_⟩
  have hd := denominatorWords_length_bound d
  have hn := negativeNumeratorWords_length_bound d
  simp only [weightStreamsTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X]
  unfold weightWordBound at hd hn
  nlinarith

 lemma weightStreams_queryFree : weightStreams.QueryFree :=
  seq_queryFree _ _
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (push_queryFree _ _)))
    (seq_queryFree _ _ weightStreamLoop_queryFree
      (seq_queryFree _ _ (clear_queryFree _)
        (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (reverseOn_queryFree _ _ _))))

 theorem weightStreams_runs (g : BitString → ℕ) (d : ℕ) :
    ∃ (c : weightStreams.machine.Config) (t : ℕ),
      weightStreams.machine.Runs g
        (weightStreams.config weightStreams.start (weightStreamStore 0 0 (List.replicate d true) [] [] [] [])) c t ∧
      c.stack = weightStreamStore 0 0 (encodeBitList (denominatorWords d))
        (encodeBitList (negativeNumeratorWords d)) [] [] [] ∧
      t ≤ weightStreamsTime.eval d := by
  obtain ⟨t,ht,hbound⟩ := weightStreams_executes g d
  refine ⟨weightStreams.config weightStreams.exit
    (weightStreamStore 0 0 (encodeBitList (denominatorWords d))
      (encodeBitList (negativeNumeratorWords d)) [] [] []),t,?_,rfl,hbound⟩
  apply (runs_iff_steps_halt _).mpr
  exact ⟨ht,by simp [OracleMachine.step,machine,config,weightStreams.exit_halt]⟩

end HiddenCircuits.Complexity.BinaryArithmetic
