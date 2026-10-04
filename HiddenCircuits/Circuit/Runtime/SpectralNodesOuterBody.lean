import HiddenCircuits.Circuit.Runtime.SpectralNodesRow
import HiddenCircuits.Circuit.Runtime.SpectralNodesShift

namespace HiddenCircuits.Circuit.Runtime.SpectralNodes
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

def outerState (x n g : ℕ) (out : BitString) : Store 12 := fun i =>
  if i.val=7 then out else if i.val=10 then signedBits (x:ℤ)
  else if i.val=11 then List.replicate n true else if i.val=12 then List.replicate g true else []
def rowEmbedding : Fin 10 ↪ Fin 13 :=
  ⟨fun i => ⟨i.val,by omega⟩,by intro i j h;apply Fin.ext;exact congrArg (fun z : Fin 13 => z.val) h⟩
noncomputable def rowOn : OracleBlock 12 := rename rowProgram rowEmbedding
noncomputable def outerCopy : OracleBlock 12 := copyOn 10 0 9 (by decide) (by decide) (by decide)
noncomputable def clockCopy : OracleBlock 12 := copyOn 11 6 9 (by decide) (by decide) (by decide)
noncomputable def outerBody : OracleBlock 12 :=
  seq outerCopy (seq clockCopy (seq (push 6 true) (seq rowOn (seq (clear 0) (prepend 10 [false,false])))))

theorem outerBody_executes (oracle : BitString → ℕ) (x n g : ℕ) (out : BitString)
    (hx : 0<x) (B : ℕ) (hB : ∀y∈row (x:ℤ) (n+1),(signedBits y).length≤B)
    (hfinal : (signedBits ((x:ℤ)*9^(n+1))).length≤B) :
    ∃ t, outerBody.Executes oracle (outerState x n g out)
      (outerState (x*4) n g ((encodeBitList ((row (x:ℤ) (n+1)).map signedBits)).reverse++out)) t ∧
      t≤(n+1)*(bodyTime.eval B+2)+6*B+5*n+30 := by
  let s₀ := outerState x n g out
  let s₁ := Function.update s₀ (0:Fin 13) (signedBits (x:ℤ))
  let s₂ := Function.update s₁ (6:Fin 13) (List.replicate n true)
  let s₃ := Function.update s₁ (6:Fin 13) (List.replicate (n+1) true)
  let output := (encodeBitList ((row (x:ℤ) (n+1)).map signedBits)).reverse++out
  let s₄ := Function.update (outerState x n g output) (0:Fin 13) (signedBits ((x:ℤ)*9^(n+1)))
  let s₅ := outerState x n g output
  have h₁ : outerCopy.Executes oracle s₀ s₁ (5*(signedBits (x:ℤ)).length+2) := by
    simpa [s₀,s₁,outerState] using copyOn_executes oracle (10:Fin 13) 0 9 (by decide) (by decide) (by decide) s₀ rfl
  have h₂ : clockCopy.Executes oracle s₁ s₂ (5*n+2) := by
    simpa [s₀,s₁,s₂,outerState] using copyOn_executes oracle (11:Fin 13) 6 9 (by decide) (by decide) (by decide) s₁ rfl
  have h₃ : (push (6:Fin 13) true).Executes oracle s₂ s₃ 1 := by
    convert push_executes oracle (6:Fin 13) true s₂ using 1
    funext i;fin_cases i <;> simp [s₂,s₃,s₁,s₀,outerState,List.replicate_succ]
  obtain ⟨c,hc,hcb⟩ := rowProgram_executes oracle (n+1) (x:ℤ) out B hB
  have h₄ : rowOn.Executes oracle s₃ s₄ c := by
    apply rename_executes_to rowProgram rowEmbedding oracle hc
    · funext i;fin_cases i <;> simp [s₃,s₁,s₀,outerState,rowEmbedding,state]
    · funext i;fin_cases i <;> simp [s₄,output,outerState,rowEmbedding,state]
    · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 6 rfl) | exact False.elim (hi 7 rfl)
  have h₅ : (clear (0:Fin 13)).Executes oracle s₄ s₅ ((signedBits ((x:ℤ)*9^(n+1))).length+1) := by
    convert clear_executes oracle (0:Fin 13) s₄ using 1
    · funext i;fin_cases i <;> simp [s₄,s₅,outerState]
  have h₆ : (prepend (10:Fin 13) [false,false]).Executes oracle s₅ (outerState (x*4) n g output) 7 := by
    convert prepend_executes oracle (10:Fin 13) [false,false] s₅ using 1
    funext i;fin_cases i <;> simp [s₅,outerState,signed_four_mul x hx]
  refine ⟨_,seq_executes _ _ oracle h₁ (seq_executes _ _ oracle h₂ (seq_executes _ _ oracle h₃
    (seq_executes _ _ oracle h₄ (seq_executes _ _ oracle h₅ h₆)))),?_⟩
  have hstart := hB (x:ℤ) (by simp [row])
  omega

theorem outerBody_queryFree : outerBody.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (rename_queryFree _ _ rowProgram_queryFree)
      (seq_queryFree _ _ (clear_queryFree _) (prepend_queryFree _ _)))))
end HiddenCircuits.Circuit.Runtime.SpectralNodes
