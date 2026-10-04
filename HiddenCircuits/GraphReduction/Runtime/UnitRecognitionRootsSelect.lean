import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRootsState

/-! First-good-root gating and physical saving of its residual alive mask. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRoots
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

def decisionValue : List Bool → Bool
  | [found,test,eligible] => !found && (eligible && test)
  | _ => false
noncomputable def decideRoot : OracleBlock 42 := seq
  (copyOn 38 41 15 (by decide) (by decide) (by decide))
  (GraphVerifier.Runtime.decision 42 [41,35,36] decisionValue)

theorem decideRoot_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (b : Best n) (i : Fin n) (clock : BitString) :
    decideRoot.Executes g
      (state G A b i.val (some (UnitRecognitionComponent.component G A i)) clock []
        [UnitRecognitionUmbrella.check G (UnitRecognitionComponent.component G A i).order.reverse] [A[i.val]] [] [])
      (state G A b i.val (some (UnitRecognitionComponent.component G A i)) clock [] [] [] []
        [!b.isSome && good G A i]) 19 := by
  let test := UnitRecognitionUmbrella.check G (UnitRecognitionComponent.component G A i).order.reverse
  let s := UnitRecognitionComponent.component G A i
  have h1 : (copyOn (38 : Fin 43) 41 15 (by decide) (by decide) (by decide)).Executes g
      (state G A b i.val (some s) clock [] [test] [A[i.val]] [] [])
      (state G A b i.val (some s) clock [] [test] [A[i.val]] [b.isSome] []) 7 := by
    convert copyOn_executes g (38 : Fin 43) 41 15 (by decide) (by decide) (by decide)
      (state G A b i.val (some s) clock [] [test] [A[i.val]] [] []) rfl using 1
    funext j;fin_cases j <;> simp [state]
  let bits : Fin 43 → Bool := fun r=>if r.val=41 then b.isSome else if r.val=35 then test else A[i.val]
  have h2 : (GraphVerifier.Runtime.decision (42 : Fin 43) [41,35,36] decisionValue).Executes g
      (state G A b i.val (some s) clock [] [test] [A[i.val]] [b.isSome] [])
      (state G A b i.val (some s) clock [] [] [] [] [!b.isSome && good G A i]) 10 := by
    have h := GraphVerifier.Runtime.decision_executes (42 : Fin 43) [41,35,36]
      (by decide) (by decide) decisionValue bits g
      (state G A b i.val (some s) clock [] [test] [A[i.val]] [b.isSome] [])
      (by intro j hj;fin_cases j <;> simp [state,UnitRecognitionComponent.store,UnitRecognitionChoice.rawState,bits] at *)
    convert h using 1
    funext j;fin_cases j <;> simp [state,UnitRecognitionComponent.store,UnitRecognitionChoice.rawState,
      bits,eraseStore,decisionValue,good,test]
  exact seq_executes _ _ g h1 h2

noncomputable def saveResidual : OracleBlock 42 := seq (clear 37)
  (seq (copyOn 4 37 15 (by decide) (by decide) (by decide)) (GraphVerifier.Runtime.writeBool 38 true))

theorem saveResidual_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (b : Best n) (i : Fin n) (clock : BitString) :
    saveResidual.Executes g
      (state G A b i.val (some (UnitRecognitionComponent.component G A i)) clock [] [] [] [] [])
      (state G A (some i) i.val (some (UnitRecognitionComponent.component G A i)) clock [] [] [] [] []) (24*n+12) := by
  let s := state G A b i.val (some (UnitRecognitionComponent.component G A i)) clock [] [] [] [] []
  have h1 := clear_executes g (37 : Fin 43) s
  have h2 := copyOn_executes g (4 : Fin 43) 37 15 (by decide) (by decide) (by decide)
    (Function.update s 37 []) rfl
  have h3 := GraphVerifier.Runtime.writeBool_executes (38 : Fin 43) true g
    (Function.update (Function.update s 37 []) 37
      ((Function.update s 37 []) 4 ++ (Function.update s 37 []) 37))
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1
  · funext j;fin_cases j <;> simp [s,state,UnitRecognitionComponent.store,UnitRecognitionChoice.rawState,residual]
  · simp [s,state,UnitRecognitionComponent.store,UnitRecognitionChoice.rawState,liveBits_length];ring

noncomputable def select : OracleBlock 42 := branchPop 42 skip skip saveResidual

theorem select_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (b : Best n) (i : Fin n) (clock : BitString) :
    ∃t, select.Executes g
      (state G A b i.val (some (UnitRecognitionComponent.component G A i)) clock [] [] [] [] [!b.isSome && good G A i])
      (state G A (step G A i b) i.val (some (UnitRecognitionComponent.component G A i)) clock [] [] [] [] []) t ∧
      t≤24*n+14 := by
  have he (flag : Bool) : Function.update
      (state G A b i.val (some (UnitRecognitionComponent.component G A i)) clock [] [] [] [] [flag]) 42 [] =
      state G A b i.val (some (UnitRecognitionComponent.component G A i)) clock [] [] [] [] [] := by
    funext j;fin_cases j <;> rfl
  cases hp : !b.isSome && good G A i with
  | false =>
    refine ⟨3,?_,by omega⟩
    apply branchPop_false 42 skip skip saveResidual g rfl
    rw [he]
    have hs : step G A i b=b := by unfold step;rw [hp];rfl
    rw [hs]
    exact skip_executes g _
  | true =>
    refine ⟨24*n+14,?_,by omega⟩
    apply branchPop_true 42 skip skip saveResidual g rfl
    rw [he]
    have hs : step G A i b=some i := by unfold step;rw [hp];rfl
    rw [hs]
    exact saveResidual_executes g G A b i clock

lemma decideRoot_queryFree : decideRoot.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (GraphVerifier.Runtime.decision_queryFree _ _ _)
lemma saveResidual_queryFree : saveResidual.QueryFree := seq_queryFree _ _ (clear_queryFree _)
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (GraphVerifier.Runtime.writeBool_queryFree _ _))
lemma select_queryFree : select.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree saveResidual_queryFree

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRoots
