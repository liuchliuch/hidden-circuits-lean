import HiddenCircuits.Complexity.DeterminantRuntime.MatrixProductPrepare
import HiddenCircuits.Complexity.DeterminantRuntime.GatherSemantics
import HiddenCircuits.Complexity.DeterminantRuntime.GatherBounds
import HiddenCircuits.Complexity.BinaryArithmetic.DotProductRuntime
import Mathlib.Algebra.BigOperators.Fin

/-! Actual row and column gathering followed by the finite signed dot product. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.MatrixProduct
open OracleBlock BinaryArithmetic
variable {n : ℕ}

def rowPorts : Fin 14 ↪ Fin 25 where
  toFun := ![8,10,11,0,12,13,14,15,16,17,18,19,20,21]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
def columnPorts : Fin 14 ↪ Fin 25 where
  toFun := ![9,2,11,0,22,13,14,15,16,17,18,19,20,21]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
def dotPorts : Fin 9 ↪ Fin 25 where
  toFun := ![13,14,15,16,17,18,3,12,22]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def gatherRow : OracleBlock 24 := Gather.on rowPorts
noncomputable def gatherColumn : OracleBlock 24 := Gather.on columnPorts
noncomputable def dotBlock : OracleBlock 24 := rename dotAccumulator dotPorts

def rowWords (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : BitString :=
  encodeBitList (List.ofFn fun j => signedBits (A i j))
def columnWords (B : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : BitString :=
  encodeBitList (List.ofFn fun i => signedBits (B i j))

theorem gatherRow_executes (g : BitString → ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) (result out inner outer b : BitString) :
    ∃ t, gatherRow.Executes g
      (cellState n i.val j.val result out inner outer (encodeBitList (matrixWords A)) b
        (List.replicate (i.val*n) true) [true] [] [])
      (cellState n i.val j.val result out inner outer (encodeBitList (matrixWords A)) b
        (List.replicate (i.val*n) true) [true] (rowWords A i) []) t ∧
      t ≤ Gather.timeBound (encodeBitList (matrixWords A)).length (i.val*n) 1 n := by
  obtain ⟨t,ht,hb⟩ := Gather.on_executes rowPorts g (matrixWords A) (i.val*n) 1 n []
    (cellState n i.val j.val result out inner outer (encodeBitList (matrixWords A)) b
      (List.replicate (i.val*n) true) [true] [] [])
    (by funext q; fin_cases q <;> rfl)
  rw [gather_row, List.append_nil] at ht
  have he : Function.update
      (cellState n i.val j.val result out inner outer (encodeBitList (matrixWords A)) b
        (List.replicate (i.val*n) true) [true] [] []) (rowPorts 4) (rowWords A i) =
      cellState n i.val j.val result out inner outer (encodeBitList (matrixWords A)) b
        (List.replicate (i.val*n) true) [true] (rowWords A i) [] := by
    funext q; fin_cases q <;> rfl
  change gatherRow.Executes g _ _ t at ht
  change ∃ t, gatherRow.Executes g _ _ t ∧ _
  rw [show encodeBitList (List.ofFn fun j => signedBits (A i j)) = rowWords A i from rfl,he] at ht
  exact ⟨t,ht,hb⟩

theorem gatherColumn_executes (g : BitString → ℕ) (B : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) (result out inner outer a start left : BitString) :
    ∃ t, gatherColumn.Executes g
      (cellState n i.val j.val result out inner outer a (encodeBitList (matrixWords B))
        start (List.replicate n true) left [])
      (cellState n i.val j.val result out inner outer a (encodeBitList (matrixWords B))
        start (List.replicate n true) left (columnWords B j)) t ∧
      t ≤ Gather.timeBound (encodeBitList (matrixWords B)).length j.val n n := by
  obtain ⟨t,ht,hb⟩ := Gather.on_executes columnPorts g (matrixWords B) j.val n n []
    (cellState n i.val j.val result out inner outer a (encodeBitList (matrixWords B))
      start (List.replicate n true) left [])
    (by funext q; fin_cases q <;> rfl)
  rw [gather_column, List.append_nil] at ht
  have he : Function.update
      (cellState n i.val j.val result out inner outer a (encodeBitList (matrixWords B))
        start (List.replicate n true) left []) (columnPorts 4) (columnWords B j) =
      cellState n i.val j.val result out inner outer a (encodeBitList (matrixWords B))
        start (List.replicate n true) left (columnWords B j) := by
    funext q; fin_cases q <;> rfl
  rw [show encodeBitList (List.ofFn fun i => signedBits (B i j)) = columnWords B j from rfl,he] at ht
  exact ⟨t,ht,hb⟩

theorem zipWith_ofFn (f g : Fin n → ℤ) :
    List.zipWith (·*·) (List.ofFn f) (List.ofFn g) = List.ofFn (fun i => f i * g i) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem dotBlock_executes (g : BitString → ℕ) (A B : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) (out inner outer a b start stride : BitString) :
    ∃ t, dotBlock.Executes g
      (cellState n i.val j.val (signedBits 0) out inner outer a b start stride (rowWords A i) (columnWords B j))
      (cellState n i.val j.val (signedBits ((A*B) i j)) out inner outer a b start stride [] []) t ∧
      t ≤ dotAccumulatorTime.eval (1+(rowWords A i).length+(columnWords B j).length) := by
  obtain ⟨t,ht,hb⟩ := dotAccumulator_zip_polynomial g
    (List.ofFn (fun k => A i k)) (List.ofFn (fun k => B k j)) 0 (by simp)
  have he : 0+(List.zipWith (·*·) (List.ofFn (fun k => A i k)) (List.ofFn (fun k => B k j))).sum =
      (A*B) i j := by rw [zipWith_ofFn]; simp [Matrix.mul_apply,List.sum_ofFn]
  rw [he] at ht
  simp only [List.map_ofFn, Function.comp_def] at ht hb
  refine ⟨t,?_,?_⟩
  · apply rename_executes_to dotAccumulator dotPorts g ht
    · funext q; fin_cases q <;> rfl
    · funext q; fin_cases q <;> rfl
    · intro q hq; fin_cases q <;> first
        | exact (hq 6 rfl).elim
        | exact (hq 7 rfl).elim
        | exact (hq 8 rfl).elim
        | rfl
  · simpa [rowWords,columnWords,signedBits,negative] using hb

theorem gatherRow_queryFree : gatherRow.QueryFree := Gather.on_queryFree _
theorem gatherColumn_queryFree : gatherColumn.QueryFree := Gather.on_queryFree _
theorem dotBlock_queryFree : dotBlock.QueryFree := rename_queryFree _ _ dotAccumulator_queryFree

end HiddenCircuits.Complexity.DeterminantRuntime.MatrixProduct
