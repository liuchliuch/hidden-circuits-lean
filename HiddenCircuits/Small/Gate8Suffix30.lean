import HiddenCircuits.Small.Gate8Suffix31
import HiddenCircuits.Small.Gate8R5

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix30Rows : Fin 70 → List (Fin 70 × ℚ) := ![[],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(12,8)],
  [(12,8)],
  [(12,-8)],
  [(10,8)],
  [(10,4)],
  [(10,4)],
  [],
  [],
  [],
  [],
  [(22,8)],
  [(22,8)],
  [(22,-8)],
  [(20,8)],
  [(20,4)],
  [(20,4)],
  [(28,8)],
  [(28,8)],
  [(28,-8)],
  [(26,8)],
  [(26,4)],
  [(26,4)],
  [(31,16)],
  [(31,8)],
  [(31,8)],
  [],
  [],
  [],
  [],
  [],
  [(42,8)],
  [(42,8)],
  [(42,-8)],
  [(40,8)],
  [(40,4)],
  [(40,4)],
  [(48,8)],
  [(48,8)],
  [(48,-8)],
  [(46,8)],
  [(46,4)],
  [(46,4)],
  [(51,16)],
  [(51,8)],
  [(51,8)],
  [],
  [(58,8)],
  [(58,8)],
  [(58,-8)],
  [(56,8)],
  [(56,4)],
  [(56,4)],
  [(61,16)],
  [(61,8)],
  [(61,8)],
  [],
  [(65,16)],
  [(65,8)],
  [(65,8)],
  [],
  []]
def Gate8Suffix30 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix30Rows
theorem gate8_suffix_step30 : (fun a => sparseMultiplyRow (Gate8R5Rows a) Gate8Suffix31Rows) = Gate8Suffix30Rows := by
  decide +kernel
theorem gate8_suffix30 : ([Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix30 := by
  rw [List.prod_cons, gate8_suffix31]
  exact (sparseMatrix_mul_sparseMatrix Gate8R5Rows Gate8Suffix31Rows).trans
    (congrArg sparseMatrix gate8_suffix_step30)

end HiddenCircuits.Small
