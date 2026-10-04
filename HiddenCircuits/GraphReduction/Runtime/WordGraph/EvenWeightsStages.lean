import HiddenCircuits.GraphReduction.Runtime.WordGraph.EvenWeightsDefs
namespace HiddenCircuits.Complexity.EvenWeightsRuntime
open OracleBlock BinaryArithmetic Polynomial
open HiddenCircuits.GraphReduction
open HiddenCircuits.GraphReduction.Runtime.WordGraph
set_option maxHeartbeats 1000000

lemma fact_executes (g : BitString → ℕ) (i k : ℕ) (den : BitString) :
    ∃c, fact.Executes g (state i k den [] [] [] [] [])
      (state i k den [] (signedBits (oddFactorial (i+k+1):ℤ)) [] [] []) c ∧
      c ≤ OddFactorialRuntime.time.eval (i+k+1)+12*(i+k+1)^2+5*(i+k)+30 := by
  let st := state i k den [] [] [] [] []
  let mid := Function.update st (26:Fin 31) (List.replicate (i+k+1) true)
  let fin := Function.update st (26:Fin 31) (signedBits (oddFactorial (i+k+1):ℤ))
  have hp := oddClock_executes g i k den
  obtain ⟨a,ha,hab⟩ := OddFactorialRuntime.program_executes g (List.replicate (i+k+1) true)
  simp only [List.length_replicate] at ha hab
  have hrun : (rename OddFactorialRuntime.program oddEmbedding).Executes g mid fin a := by
    apply rename_executes_to OddFactorialRuntime.program oddEmbedding g ha
    · funext q;fin_cases q <;> rfl
    · funext q;fin_cases q <;> rfl
    · intro q hq
      have h26 : q≠(26:Fin 31) := fun h=>hq 0 h.symm
      simp only [mid,fin,Function.update_of_ne h26]
  have hm : (moveOn (26:Fin 31) 4 29 (by decide) (by decide) (by decide)).Executes g fin
      (state i k den [] (signedBits (oddFactorial (i+k+1):ℤ)) [] [] [])
      (6*(signedBits (oddFactorial (i+k+1):ℤ)).length+5) := by
    convert moveOn_executes g (26:Fin 31) 4 29 (by decide) (by decide) (by decide) fin rfl using 1
    funext q;fin_cases q <;> simp [fin,st,state]
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hrun hm),?_⟩
  have hh : (signedBits (oddFactorial (i+k+1):ℤ)).length ≤ 2*(i+k+1)*(i+k+1)+2 :=
    signedBits_length_of_abs_bound (by simpa using OddFactorialRuntime.oddFactorial_bound (i+k+1))
  nlinarith

lemma powerConstants_executes (g : BitString → ℕ) (i k : ℕ) (den f : BitString) :
    powerConstants.Executes g (Function.update (state i k den [] f [] [] []) (25:Fin 31) (List.replicate (i+k) true))
      (Function.update (Function.update (state i k den [] f [] [] []) (25:Fin 31) (List.replicate (i+k) true))
        26 (signedBits (2:ℤ))) 7 := by
  let st := Function.update (state i k den [] f [] [] []) (25:Fin 31) (List.replicate (i+k) true)
  let a := Function.update st (26:Fin 31) [true]
  let b := Function.update st (26:Fin 31) [false,true]
  have h1 : (push (26:Fin 31) true).Executes g st a 1 := push_executes g _ _ _
  have h2 : (push (26:Fin 31) false).Executes g a b 1 := by
    simpa [a,b] using push_executes g (26:Fin 31) false a
  have h3 : (push (26:Fin 31) false).Executes g b (Function.update st 26 (signedBits (2:ℤ))) 1 := by
    have hh : signedBits (2:ℤ)=[false,false,true] := by decide
    simpa [b,hh] using push_executes g (26:Fin 31) false b
  exact seq_executes _ _ g h1 (seq_executes _ _ g h2 h3)

lemma power_executes (g : BitString → ℕ) (i k : ℕ) (den f : BitString) :
    ∃c, power.Executes g (state i k den [] f [] [] [])
      (state i k den [] f (signedBits ((2:ℤ)^(i+k))) [] []) c ∧
      c ≤ PowerRuntime.time.eval (i+k+3)+11*(i+k)+36 := by
  let st := state i k den [] f [] [] []
  let mid := Function.update (Function.update st (25:Fin 31) (List.replicate (i+k) true)) 26 (signedBits (2:ℤ))
  let fin := Function.update st (26:Fin 31) (signedBits ((2:ℤ)^(i+k)))
  have hp := sumClock_executes g i k den [] f [] [] []
  have hc := powerConstants_executes g i k den f
  obtain ⟨a,ha,hab⟩ := PowerRuntime.program_executes g (2:ℤ) (List.replicate (i+k) true)
  simp only [List.length_replicate] at ha hab
  have hrun : (rename PowerRuntime.program powerEmbedding).Executes g mid fin a := by
    apply rename_executes_to PowerRuntime.program powerEmbedding g ha
    · funext q;fin_cases q <;> rfl
    · funext q;fin_cases q <;> rfl
    · intro q hq
      have h25 : q≠(25:Fin 31) := fun h=>hq 1 h.symm
      have h26 : q≠(26:Fin 31) := fun h=>hq 0 h.symm
      simp only [mid,fin,Function.update_of_ne h25,Function.update_of_ne h26]
  have hm : (moveOn (26:Fin 31) 6 29 (by decide) (by decide) (by decide)).Executes g fin
      (state i k den [] f (signedBits ((2:ℤ)^(i+k))) [] []) (6*(signedBits ((2:ℤ)^(i+k))).length+5) := by
    convert moveOn_executes g (26:Fin 31) 6 29 (by decide) (by decide) (by decide) fin rfl using 1
    funext q;fin_cases q <;> simp [fin,st,state]
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hc (seq_executes _ _ g hrun hm)),?_⟩
  have hh : (signedBits ((2:ℤ)^(i+k))).length ≤ i+k+2 := signedBits_length_of_abs_bound (by simp)
  have htwo : (signedBits (2:ℤ)).length=3 := by decide
  rw [htwo,show 3+(i+k)=i+k+3 by omega] at hab
  omega

lemma divisor_executes (g : BitString → ℕ) (i k : ℕ) (den f p : BitString) :
    ∃c, divisor.Executes g (state i k den [] f p [] [])
      (state i k den [] f p (signedBits ((2*i+1:ℕ):ℤ)) []) c ∧
      c ≤ (2*i+1)*(4*(2*i+1)+5)+22*i+34 := by
  let st := state i k den [] f p [] []
  let mid := Function.update st (25:Fin 31) (List.replicate (2*i+1) true)
  let fin := Function.update st (26:Fin 31) (Computability.encodeNat (2*i+1))
  let signed := Function.update st (26:Fin 31) (signedBits ((2*i+1:ℕ):ℤ))
  have hp := divisorClock_executes g i k den f p
  have ha := unaryBinary_executes g (List.replicate (2*i+1) true) 0
  simp only [List.length_replicate,Nat.zero_add] at ha
  have hrun : (rename unaryBinary unaryEmbedding).Executes g mid fin (unaryBinaryCost 0 (2*i+1)) := by
    apply rename_executes_to unaryBinary unaryEmbedding g ha
    · funext q;fin_cases q <;> rfl
    · funext q;fin_cases q <;> rfl
    · intro q hq
      have h25 : q≠(25:Fin 31) := fun h=>hq 0 h.symm
      have h26 : q≠(26:Fin 31) := fun h=>hq 1 h.symm
      simp only [mid,fin,Function.update_of_ne h25,Function.update_of_ne h26]
  have hs : (push (26:Fin 31) false).Executes g fin signed 1 := by
    simpa [fin,signed,DH.Runtime.FactorialInto.signed_nat] using push_executes g (26:Fin 31) false fin
  have hm : (moveOn (26:Fin 31) 7 29 (by decide) (by decide) (by decide)).Executes g signed
      (state i k den [] f p (signedBits ((2*i+1:ℕ):ℤ)) []) (6*(signedBits ((2*i+1:ℕ):ℤ)).length+5) := by
    convert moveOn_executes g (26:Fin 31) 7 29 (by decide) (by decide) (by decide) signed rfl using 1
    funext q;fin_cases q <;> simp [signed,st,state]
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hrun (seq_executes _ _ g hs hm)),?_⟩
  have hh : (signedBits ((2*i+1:ℕ):ℤ)).length ≤ 2*i+2 := by
    simp only [DH.Runtime.FactorialInto.signed_nat,List.length_cons,encodeNat_length]
    have h := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=2*i+1))
    omega
  have hu := unaryBinaryCost_le (2*i+1) 0 (2*i+1) (by omega)
  omega

lemma sign_executes (g : BitString → ℕ) (i k : ℕ) (den f p v : BitString) :
    sign.Executes g (state i k den [] f p v [])
      (state i k den [] f p v (signedBits ((-1:ℤ)^(i+k)))) (6*(i+k)+13) := by
  let st := state i k den [] f p v []
  let mid := Function.update st (25:Fin 31) (List.replicate (i+k) true)
  let fin := Function.update mid (8:Fin 31) [true]
  have hp := sumClock_executes g i k den [] f p v []
  have hs : (push (8:Fin 31) true).Executes g mid fin 1 := push_executes g _ _ _
  have ha := parityBlock_executes g (List.replicate (i+k) true) [true]
  simp only [List.length_replicate,RatioNormalization.parity_one] at ha
  have hrun : (rename parityBlock parityEmbedding).Executes g fin
      (state i k den [] f p v (signedBits ((-1:ℤ)^(i+k)))) (i+k+2) := by
    apply rename_executes_to parityBlock parityEmbedding g ha
    · funext q;fin_cases q <;> rfl
    · funext q;fin_cases q <;> rfl
    · intro q hq
      have h25 : q≠(25:Fin 31) := fun h=>hq 0 h.symm
      have h8 : q≠(8:Fin 31) := fun h=>hq 1 h.symm
      have hv8 : q.val≠8 := fun h=>h8 (Fin.ext h)
      simp only [fin,mid,st,Function.update_of_ne h25,Function.update_of_ne h8,state,hv8,if_false]
  convert seq_executes _ _ g hp (seq_executes _ _ g hs hrun) using 1 <;> omega
end HiddenCircuits.Complexity.EvenWeightsRuntime
