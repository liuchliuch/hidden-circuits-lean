import HiddenCircuits.Complexity.BinaryArithmetic.CleanOperations
import HiddenCircuits.Complexity.OracleMove
import HiddenCircuits.Complexity.PolynomialBounds

/-! Three ordinary arithmetic operators compiled to a common clean nine-stack
interface. Exact division is used only after its mathematical divisibility proof. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock Polynomial

inductive Operation | add | multiply | divide deriving DecidableEq

def Operation.eval : Operation → ℤ → ℤ → ℤ
  | .add,a,b => a+b
  | .multiply,a,b => a*b
  | .divide,a,b => a/b

def Operation.Valid : Operation → ℤ → ℤ → Prop
  | .divide,a,b => b≠0 ∧ b∣a
  | _,_,_ => True

def arithmeticEmbedding (n : ℕ) (hn : n≤9) : Fin n ↪ Fin 9 where
  toFun i := ⟨i.val,by have := i.isLt;omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun t : Fin 9 => t.val) h)

noncomputable def Operation.program : Operation → OracleBlock 8
  | .add => rename signedAddClean (arithmeticEmbedding 7 (by decide))
  | .multiply => rename cleanMultiply (arithmeticEmbedding 6 (by decide))
  | .divide => cleanDivide

noncomputable def operationTime : Polynomial ℕ := cleanAddTime+cleanMultiplyTime+cleanDivideTime

theorem Operation.executes (op : Operation) (g : BitString → ℕ) (a b : ℤ) (hv : op.Valid a b) :
    ∃ t, op.program.Executes g (binaryStore (signedBits a) (signedBits b))
      (binaryStore (signedBits (op.eval a b)) []) t ∧
      t ≤ operationTime.eval ((signedBits a).length+(signedBits b).length) := by
  cases op with
  | add =>
    obtain ⟨t,ht,hb⟩ := cleanAdd_executes g a b
    refine ⟨t,?_,?_⟩
    · apply rename_executes_to signedAddClean (arithmeticEmbedding 7 (by decide)) g ht
      · funext i;fin_cases i <;> rfl
      · funext i;fin_cases i <;> rfl
      · intro i hi;fin_cases i <;> first | rfl | (exfalso;exact hi 0 rfl) | (exfalso;exact hi 1 rfl)
    · simp only [operationTime,eval_add];omega
  | multiply =>
    obtain ⟨t,ht,hb⟩ := cleanMultiply_executes g a b
    refine ⟨t,?_,?_⟩
    · apply rename_executes_to cleanMultiply (arithmeticEmbedding 6 (by decide)) g ht
      · funext i;fin_cases i <;> rfl
      · funext i;fin_cases i <;> rfl
      · intro i hi;fin_cases i <;> first | rfl | (exfalso;exact hi 0 rfl) | (exfalso;exact hi 1 rfl)
    · simp only [operationTime,eval_add];omega
  | divide =>
    obtain ⟨t,ht,hb⟩ := cleanDivide_executes g a b hv.1 hv.2
    exact ⟨t,ht,by simp only [operationTime,eval_add];omega⟩

lemma Operation.queryFree (op : Operation) : op.program.QueryFree := by
  cases op with
  | add => exact rename_queryFree _ _ signedAddClean_queryFree
  | multiply => exact rename_queryFree _ _ cleanMultiply_queryFree
  | divide => exact cleanDivide_queryFree

end HiddenCircuits.Complexity.BinaryArithmetic
