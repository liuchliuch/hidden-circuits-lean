import HiddenCircuits.Circuit.Runtime.SpectralNodesPure
import HiddenCircuits.Complexity.BinaryArithmetic.CleanOperations
import HiddenCircuits.Complexity.OracleRepeat

namespace HiddenCircuits.Circuit.Runtime.SpectralNodes
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

def state (x : ℤ) (counter out : BitString) : Store 9 := fun i =>
  if i.val=0 then signedBits x else if i.val=6 then counter else if i.val=7 then out else []
def mulEmbedding : Fin 6 ↪ Fin 10 := ⟨fun i => ⟨i.val,by omega⟩,by intro i j h; apply Fin.ext; exact congrArg (fun z : Fin 10 => z.val) h⟩
def emitEmbedding : Fin 2 ↪ Fin 10 where
  toFun i := if i.val=0 then 8 else 7
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def multiply : OracleBlock 9 := rename cleanMultiply mulEmbedding
noncomputable def emit : OracleBlock 9 := rename wordEmit emitEmbedding
noncomputable def copy : OracleBlock 9 := copyOn 0 8 9 (by decide) (by decide) (by decide)
noncomputable def body : OracleBlock 9 := seq copy (seq emit (seq (prepend 1 (signedBits 9)) multiply))
noncomputable def bodyTime : Polynomial ℕ := cleanMultiplyTime.comp (X+5)+11*X+31

theorem body_executes (g : BitString → ℕ) (x : ℤ) (counter out : BitString) :
    ∃ t, body.Executes g (state x counter out)
      (state (x*9) counter ((wordChunk (signedBits x)).reverse++out)) t ∧
      t≤bodyTime.eval (signedBits x).length := by
  let s₀ := state x counter out
  let s₁ := Function.update s₀ (8:Fin 10) (signedBits x)
  let s₂ := state x counter ((wordChunk (signedBits x)).reverse++out)
  let s₃ := Function.update s₂ (1:Fin 10) (signedBits 9)
  have h₁ : copy.Executes g s₀ s₁ (5*(signedBits x).length+2) := by
    simpa [s₀,s₁,state] using copyOn_executes g (0:Fin 10) 8 9 (by decide) (by decide) (by decide) s₀ rfl
  have h₂ : emit.Executes g s₁ s₂ (6*(signedBits x).length+7) := by
    apply rename_executes_to wordEmit emitEmbedding g (wordEmit_executes g (signedBits x) out)
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)
  have h₃ : (prepend (1:Fin 10) (signedBits 9)).Executes g s₂ s₃ 16 := by
    simpa [s₂,s₃,state,signedBits] using prepend_executes g (1:Fin 10) (signedBits 9) s₂
  obtain ⟨c,hc,hcb⟩ := cleanMultiply_executes g x 9
  have h₄ : multiply.Executes g s₃ (state (x*9) counter ((wordChunk (signedBits x)).reverse++out)) c := by
    apply rename_executes_to cleanMultiply mulEmbedding g hc
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)
  refine ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),?_⟩
  have h9 : (signedBits (9:ℤ)).length=5 := by decide
  rw [h9] at hcb
  simp only [bodyTime,eval_add,eval_mul,eval_ofNat,eval_X,eval_comp]
  omega

theorem body_queryFree : body.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ wordEmit_queryFree)
      (seq_queryFree _ _ (prepend_queryFree _ _) (rename_queryFree _ _ cleanMultiply_queryFree)))
end HiddenCircuits.Circuit.Runtime.SpectralNodes
