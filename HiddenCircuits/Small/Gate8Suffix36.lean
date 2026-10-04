import HiddenCircuits.Small.Gate8Suffix37
import HiddenCircuits.Small.Gate8R4

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix36Rows : Fin 70 → List (Fin 70 × ℚ) := ![[],
  [],
  [],
  [(3,2)],
  [],
  [],
  [],
  [(7,2)],
  [],
  [(12,-4)],
  [(10,2)],
  [],
  [(10,2)],
  [],
  [],
  [],
  [],
  [(17,2)],
  [],
  [(22,-4)],
  [(20,2)],
  [],
  [(20,2)],
  [],
  [],
  [(28,-4)],
  [(26,2)],
  [],
  [(26,2)],
  [],
  [],
  [(31,4)],
  [],
  [],
  [],
  [],
  [],
  [(37,2)],
  [],
  [(42,-4)],
  [(40,2)],
  [],
  [(40,2)],
  [],
  [],
  [(48,-4)],
  [(46,2)],
  [],
  [(46,2)],
  [],
  [],
  [(51,4)],
  [],
  [],
  [],
  [(58,-4)],
  [(56,2)],
  [],
  [(56,2)],
  [],
  [],
  [(61,4)],
  [],
  [],
  [],
  [(65,4)],
  [],
  [],
  [],
  []]
def Gate8Suffix36 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix36Rows
theorem gate8_suffix_step36 : (fun a => sparseMultiplyRow (Gate8R4Rows a) Gate8Suffix37Rows) = Gate8Suffix36Rows := by
  decide +kernel
theorem gate8_suffix36 : ([Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix36 := by
  rw [List.prod_cons, gate8_suffix37]
  exact (sparseMatrix_mul_sparseMatrix Gate8R4Rows Gate8Suffix37Rows).trans
    (congrArg sparseMatrix gate8_suffix_step36)

end HiddenCircuits.Small
