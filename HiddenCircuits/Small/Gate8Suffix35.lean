import HiddenCircuits.Small.Gate8Suffix36
import HiddenCircuits.Small.Gate8R5

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix35Rows : Fin 70 → List (Fin 70 × ℚ) := ![[],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(12,-4)],
  [(12,-4)],
  [],
  [(10,4)],
  [],
  [],
  [],
  [],
  [],
  [],
  [(22,-4)],
  [(22,-4)],
  [],
  [(20,4)],
  [],
  [],
  [(28,-4)],
  [(28,-4)],
  [],
  [(26,4)],
  [],
  [],
  [(31,8)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(42,-4)],
  [(42,-4)],
  [],
  [(40,4)],
  [],
  [],
  [(48,-4)],
  [(48,-4)],
  [],
  [(46,4)],
  [],
  [],
  [(51,8)],
  [],
  [],
  [],
  [(58,-4)],
  [(58,-4)],
  [],
  [(56,4)],
  [],
  [],
  [(61,8)],
  [],
  [],
  [],
  [(65,8)],
  [],
  [],
  [],
  []]
def Gate8Suffix35 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix35Rows
theorem gate8_suffix_step35 : (fun a => sparseMultiplyRow (Gate8R5Rows a) Gate8Suffix36Rows) = Gate8Suffix35Rows := by
  decide +kernel
theorem gate8_suffix35 : ([Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix35 := by
  rw [List.prod_cons, gate8_suffix36]
  exact (sparseMatrix_mul_sparseMatrix Gate8R5Rows Gate8Suffix36Rows).trans
    (congrArg sparseMatrix gate8_suffix_step35)

end HiddenCircuits.Small
