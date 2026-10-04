import HiddenCircuits.Small.Gate8Suffix38
import HiddenCircuits.Small.Gate8E6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix37Rows : Fin 70 → List (Fin 70 × ℚ) := ![[],
  [],
  [],
  [(3,2)],
  [],
  [],
  [],
  [(7,2)],
  [],
  [],
  [(10,2)],
  [],
  [(12,2)],
  [],
  [],
  [],
  [],
  [(17,2)],
  [],
  [],
  [(20,2)],
  [],
  [(22,2)],
  [],
  [],
  [],
  [(26,2)],
  [],
  [(28,2)],
  [],
  [],
  [(31,2)],
  [],
  [],
  [],
  [],
  [],
  [(37,2)],
  [],
  [],
  [(40,2)],
  [],
  [(42,2)],
  [],
  [],
  [],
  [(46,2)],
  [],
  [(48,2)],
  [],
  [],
  [(51,2)],
  [],
  [],
  [],
  [],
  [(56,2)],
  [],
  [(58,2)],
  [],
  [],
  [(61,2)],
  [],
  [],
  [],
  [(65,2)],
  [],
  [],
  [],
  []]
def Gate8Suffix37 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix37Rows
theorem gate8_suffix_step37 : (fun a => sparseMultiplyRow (Gate8E6Rows a) Gate8Suffix38Rows) = Gate8Suffix37Rows := by
  decide +kernel
theorem gate8_suffix37 : ([Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix37 := by
  rw [List.prod_cons, gate8_suffix38]
  exact (sparseMatrix_mul_sparseMatrix Gate8E6Rows Gate8Suffix38Rows).trans
    (congrArg sparseMatrix gate8_suffix_step37)

end HiddenCircuits.Small
