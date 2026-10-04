import HiddenCircuits.Complexity.SourceGrid.Cleanup

/-! Generate the cell weights from live unary counters, execute all five exact
binary arithmetic assignments, and restore the persistent-only frame. -/
namespace HiddenCircuits.Complexity.SourceGrid
open OracleBlock BinaryArithmetic BinaryArithmetic.RegisterMachine

noncomputable def calculate : OracleBlock 42 :=
  seq (GridWeightsRuntime.programOn weightsEmbedding) (seq (push 16 false)
    (seq (GridTermRuntime.programOn arithmeticEmbedding) clearGenerated))

theorem calculate_executes (g : BitString → ℕ) (n m : ℕ) (i : Fin (n+1)) (j : Fin (m+1))
    (inner outer formula : BitString) (value acc : ℤ) (B : ℕ)
    (hb : Bounded B (GridTermRuntime.registers (gridDenominator n m) (interpolationDenominator n i)
      (interpolationDenominator m j) (interpolationNegativeNumerator m j) value acc 0))
    (ht : (signedBits (gridTerm n m i j value)).length≤B) :
    ∃ c, calculate.Executes g
      (store n m i.val j.val inner outer {formula:=formula,denominator:=signedBits (gridDenominator n m),accumulator:=signedBits acc,value:=signedBits value})
      (store n m i.val j.val inner outer {formula:=formula,denominator:=signedBits (gridDenominator n m),accumulator:=signedBits (acc+gridTerm n m i j value)}) c ∧
      c≤GridWeightsRuntime.time.eval (n+m)+GridTermRuntime.time.eval B+5*B+20 := by
  let v₀ : Values := {formula:=formula,denominator:=signedBits (gridDenominator n m),accumulator:=signedBits acc,value:=signedBits value}
  let v₁ : Values := {v₀ with leftWeight:=signedBits (interpolationDenominator n i),rightWeight:=signedBits (interpolationDenominator m j),numeratorWeight:=signedBits (interpolationNegativeNumerator m j)}
  let v₂ : Values := {v₁ with temporary:=signedBits 0}
  let v₃ : Values := {v₂ with accumulator:=signedBits (acc+gridTerm n m i j value),temporary:=signedBits (gridTerm n m i j value)}
  obtain ⟨a,ha,hab⟩ := GridWeightsRuntime.programOn_executes weightsEmbedding g
    (store n m i.val j.val inner outer v₀) n m i j (restrict_weights _ _ _ _ _ _ _)
  have h₀ : (GridWeightsRuntime.programOn weightsEmbedding).Executes g
      (store n m i.val j.val inner outer v₀) (store n m i.val j.val inner outer v₁) a := by
    simpa only [show weightsEmbedding 4=12 from rfl,show weightsEmbedding 5=13 from rfl,
      show weightsEmbedding 6=14 from rfl,update_leftWeight,update_rightWeight,update_numeratorWeight] using ha
  have h₁ : (push (16 : Fin 43) false).Executes g (store n m i.val j.val inner outer v₁)
      (store n m i.val j.val inner outer v₂) 1 := by
    simpa only [update_temporary] using push_executes g (16 : Fin 43) false (store n m i.val j.val inner outer v₁)
  obtain ⟨b,hbRun,hbb⟩ := GridTermRuntime.programOn_executes arithmeticEmbedding g
    (store n m i.val j.val inner outer v₂) (gridDenominator n m) (interpolationDenominator n i)
    (interpolationDenominator m j) (interpolationNegativeNumerator m j) value acc 0 B
    (gridDivisor_ne_zero n m i j) (gridDivisor_dvd n m i j) hb
    (restrict_arithmetic _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  have h₂ : (GridTermRuntime.programOn arithmeticEmbedding).Executes g
      (store n m i.val j.val inner outer v₂) (store n m i.val j.val inner outer v₃) b := by
    simpa only [show arithmeticEmbedding 14=11 from rfl,show arithmeticEmbedding 15=16 from rfl,
      update_accumulator,update_temporary] using hbRun
  have h₃ := clearGenerated_executes g n m i.val j.val inner outer v₃
  have he := seq_executes _ _ g h₀ (seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃))
  refine ⟨_,he,?_⟩
  have hi := hb 1
  have hj := hb 2
  have hn := hb 3
  have hv := hb 4
  change (signedBits (interpolationDenominator n i)).length≤B at hi
  change (signedBits (interpolationDenominator m j)).length≤B at hj
  change (signedBits (interpolationNegativeNumerator m j)).length≤B at hn
  change (signedBits value).length≤B at hv
  dsimp only [v₃,v₂,v₁,v₀]
  omega

lemma calculate_queryFree : calculate.QueryFree :=
  seq_queryFree _ _ (GridWeightsRuntime.programOn_queryFree _)
    (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _
      (GridTermRuntime.programOn_queryFree _) clearGenerated_queryFree))

end HiddenCircuits.Complexity.SourceGrid
