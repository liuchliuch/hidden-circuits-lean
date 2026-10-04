import HiddenCircuits.Complexity.EvalValidation.PairAtom

/-! A real width-one unary placement scanner, reusing the checked width-two
scanner with one physical dummy width bit that is removed afterwards. -/
namespace HiddenCircuits.Complexity.NativeValidation.OneIndex
open OracleBlock EvalValidation
set_option maxHeartbeats 800000
def valid (xs width : BitString) : Bool := xs.all id && decide (xs.length+1≤width.length)
noncomputable def popWidth : OracleBlock 8 := branchPop 1 skip skip skip
noncomputable def program : OracleBlock 8 := seq (push 1 true) (seq DirectIndex.program popWidth)
theorem program_executes (g : BitString→ℕ) (xs width : BitString) :
    ∃c,program.Executes g (Index.store xs width [] [] [] [] [])
      (Index.store [] width [valid xs width] [] [] [] []) c ∧ c≤210*(xs.length+width.length+1) := by
  have hp:(push (1:Fin 9) true).Executes g (Index.store xs width [] [] [] [] [])
      (Index.store xs (true::width) [] [] [] [] []) 1 := by
    convert push_executes g (1:Fin 9) true (Index.store xs width [] [] [] [] []) using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨c,hc,hb⟩:=DirectIndex.program_executes g xs (true::width)
  have hv:Index.valid xs (true::width)=valid xs width := by simp [Index.valid,valid]
  rw [hv] at hc
  have he:Function.update (Index.store [] (true::width) [valid xs width] [] [] [] []) 1 width=
      Index.store [] width [valid xs width] [] [] [] [] := by funext i;fin_cases i <;> rfl
  have hz:popWidth.Executes g (Index.store [] (true::width) [valid xs width] [] [] [] [])
      (Index.store [] width [valid xs width] [] [] [] []) 3 := by
    apply branchPop_true 1 _ _ _ g rfl
    rw [he]
    exact skip_executes g _
  exact ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hc hz),by simp only [List.length_cons] at hb;omega⟩
end HiddenCircuits.Complexity.NativeValidation.OneIndex
