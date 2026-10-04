import HiddenCircuits.GraphReduction.Runtime.UnitOrderRootsSelect

/-! A whole original-label root trial, including bounded component generation,
umbrella validation, first-success residual saving, and cleanup. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitOrderRoots
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

noncomputable def cleanTrial : OracleBlock 43 := seq (clear 3) (seq (clear 4) (clear 33))

theorem cleanTrial_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (b : Best n) (i : ℕ) (s : UnitRecognitionComponent.Data n) (clock : BitString) :
    cleanTrial.Executes g (state G A b i (some s) clock [] [] [] [] [])
      (state G A b i none clock [] [] [] [] []) (8*n+(UnitRecognitionComponent.orderBits s.order).length+7) := by
  let s0 := state G A b i (some s) clock [] [] [] [] []
  have h1 := clear_executes g (3 : Fin 44) s0
  have h2 := clear_executes g (4 : Fin 44) (Function.update s0 3 [])
  have h3 := clear_executes g (33 : Fin 44) (Function.update (Function.update s0 3 []) 4 [])
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1
  · funext j;fin_cases j <;> simp [s0,state,UnitRecognitionComponent.store,UnitRecognitionChoice.rawState]
  · simp [s0,state,UnitRecognitionComponent.store,UnitRecognitionChoice.rawState,liveBits_length];ring

noncomputable def body : OracleBlock 43 := seq computeComponent (seq checkOrder
  (seq readEligible (seq decideRoot (seq select (seq cleanTrial (push 39 true))))))

theorem body_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (b : Best n) (i : Fin n) (clock : BitString) :
    ∃t, body.Executes g (state G A b i.val none clock [] [] [] [] [])
      (state G A (step G A i b) (i.val+1) none clock [] [] [] [] []) t ∧ t≤11000*(n+1)^5 := by
  obtain ⟨c1,h1,b1⟩ := computeComponent_executes g G A b i clock
  obtain ⟨c2,h2,b2⟩ := checkOrder_executes g G A b i clock
  obtain ⟨c3,h3,b3⟩ := readEligible_executes g G A b i (UnitRecognitionComponent.component G A i) clock _
  have h4 := decideRoot_executes g G A b i clock
  obtain ⟨c5,h5,b5⟩ := select_executes g G A b i clock
  have h6 := cleanTrial_executes g G A (step G A i b) i.val (UnitRecognitionComponent.component G A i) clock
  have h7 : (push (39 : Fin 44) true).Executes g
      (state G A (step G A i b) i.val none clock [] [] [] [] [])
      (state G A (step G A i b) (i.val+1) none clock [] [] [] [] []) 1 := by
    convert push_executes g (39 : Fin 44) true _ using 1
    funext j;fin_cases j <;> simp [state,List.replicate_succ]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 (seq_executes _ _ g h6 h7))))),?_⟩
  have hl := UnitRecognitionComponent.component_orderBits_length G A i
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4),Nat.zero_le (n^5)]

lemma cleanTrial_queryFree : cleanTrial.QueryFree := seq_queryFree _ _ (clear_queryFree _)
  (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))
lemma body_queryFree : body.QueryFree := seq_queryFree _ _ computeComponent_queryFree
  (seq_queryFree _ _ checkOrder_queryFree (seq_queryFree _ _ readEligible_queryFree
    (seq_queryFree _ _ decideRoot_queryFree (seq_queryFree _ _ select_queryFree
      (seq_queryFree _ _ cleanTrial_queryFree (push_queryFree _ _))))))

end HiddenCircuits.GraphReduction.Runtime.UnitOrderRoots
