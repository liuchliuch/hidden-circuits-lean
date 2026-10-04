import HiddenCircuits.Small.Gate8Suffix28
import HiddenCircuits.Small.Gate8E6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix27Rows : Fin 70 → List (Fin 70 × ℚ) := ![[],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(12,16)],
  [],
  [(10,16)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(22,16)],
  [],
  [(20,16)],
  [],
  [],
  [],
  [(28,16)],
  [],
  [(26,16)],
  [],
  [],
  [(31,32)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(42,16)],
  [],
  [(40,16)],
  [],
  [],
  [],
  [(48,16)],
  [],
  [(46,16)],
  [],
  [],
  [(51,32)],
  [],
  [],
  [],
  [],
  [(58,16)],
  [],
  [(56,16)],
  [],
  [],
  [(61,32)],
  [],
  [],
  [],
  [(65,32)],
  [],
  [],
  [],
  []]
def Gate8Suffix27 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix27Rows
theorem gate8_suffix_step27 : (fun a => sparseMultiplyRow (Gate8E6Rows a) Gate8Suffix28Rows) = Gate8Suffix27Rows := by
  decide +kernel
theorem gate8_suffix27 : ([Gate8E6, Gate8D6, Gate8R6, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix27 := by
  rw [List.prod_cons, gate8_suffix28]
  exact (sparseMatrix_mul_sparseMatrix Gate8E6Rows Gate8Suffix28Rows).trans
    (congrArg sparseMatrix gate8_suffix_step27)

end HiddenCircuits.Small
