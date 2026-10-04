import HiddenCircuits.Small.Gate8Suffix32
import HiddenCircuits.Small.Gate8D6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix31Rows : Fin 70 → List (Fin 70 × ℚ) := ![[],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(12,8)],
  [(12,-8)],
  [(12,-8)],
  [(10,4)],
  [(10,4)],
  [],
  [],
  [],
  [],
  [],
  [(22,8)],
  [(22,-8)],
  [(22,-8)],
  [(20,4)],
  [(20,4)],
  [],
  [(28,8)],
  [(28,-8)],
  [(28,-8)],
  [(26,4)],
  [(26,4)],
  [],
  [(31,8)],
  [(31,8)],
  [],
  [],
  [],
  [],
  [],
  [],
  [(42,8)],
  [(42,-8)],
  [(42,-8)],
  [(40,4)],
  [(40,4)],
  [],
  [(48,8)],
  [(48,-8)],
  [(48,-8)],
  [(46,4)],
  [(46,4)],
  [],
  [(51,8)],
  [(51,8)],
  [],
  [],
  [(58,8)],
  [(58,-8)],
  [(58,-8)],
  [(56,4)],
  [(56,4)],
  [],
  [(61,8)],
  [(61,8)],
  [],
  [],
  [(65,8)],
  [(65,8)],
  [],
  [],
  []]
def Gate8Suffix31 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix31Rows
theorem gate8_suffix_step31 : (fun a => sparseMultiplyRow (Gate8D6Rows a) Gate8Suffix32Rows) = Gate8Suffix31Rows := by
  decide +kernel
theorem gate8_suffix31 : ([Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix31 := by
  rw [List.prod_cons, gate8_suffix32]
  exact (sparseMatrix_mul_sparseMatrix Gate8D6Rows Gate8Suffix32Rows).trans
    (congrArg sparseMatrix gate8_suffix_step31)

end HiddenCircuits.Small
