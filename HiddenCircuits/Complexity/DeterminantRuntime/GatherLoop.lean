import HiddenCircuits.Complexity.DeterminantRuntime.GatherCore

/-! The finite count-controlled gather loop. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.Gather
open OracleBlock BinaryArithmetic

noncomputable def loop : OracleBlock 13 := whilePop 6 body body

theorem lookupBound_mono (L i j : ℕ) (h : i ≤ j) :
    GraphReduction.Runtime.lookupBound L i ≤ GraphReduction.Runtime.lookupBound L j := by
  unfold GraphReduction.Runtime.lookupBound
  nlinarith

theorem loop_execution (g : BitString → ℕ) (ws : List BitString) (start stride count : ℕ)
    (out : BitString) (position remaining maxPosition : ℕ) (acc : BitString)
    (hp : position+stride*remaining ≤ maxPosition) :
    ∃ t, WhileExecution (6 : Fin 14) body body g
      (state (encodeBitList ws) start stride count out position remaining [] acc)
      (state (encodeBitList ws) start stride count out (position+stride*remaining) 0 []
        ((encodeBitList (words ws position stride remaining)).reverse++acc)) t ∧
      t ≤ remaining * (GraphReduction.Runtime.lookupBound (encodeBitList ws).length maxPosition +
        6*(encodeBitList ws).length+5*stride+15)+1 := by
  induction remaining generalizing position acc with
  | zero =>
    refine ⟨1, ?_, by simp⟩
    simpa [words, encodeBitList] using (WhileExecution.empty
      (stack := (6 : Fin 14)) (B := body) (C := body) (g := g)
      (state (encodeBitList ws) start stride count out position 0 [] acc) rfl)
  | succ remaining ih =>
    obtain ⟨c,hc,hcb⟩ := body_executes g ws start stride count out position remaining acc
    obtain ⟨t,ht,htb⟩ := ih (position+stride)
      ((wordChunk (ws[position]?.getD [])).reverse++acc) (by nlinarith)
    have he : Function.update
        (state (encodeBitList ws) start stride count out position (remaining+1) [] acc)
        (6 : Fin 14) (List.replicate remaining true) =
        state (encodeBitList ws) start stride count out position remaining [] acc := by
      funext i; fin_cases i <;> rfl
    have h := WhileExecution.one
      (show state (encodeBitList ws) start stride count out position (remaining+1) [] acc 6 =
        true::List.replicate remaining true from rfl)
      (by rw [he]; exact hc) ht
    refine ⟨1+c+1+t, ?_, ?_⟩
    · convert h using 1
      simp [words, encodeBitList_eq_chunks, List.reverse_append, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · have hm := lookupBound_mono (encodeBitList ws).length position maxPosition (by nlinarith)
      nlinarith

end HiddenCircuits.Complexity.DeterminantRuntime.Gather
