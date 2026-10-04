import HiddenCircuits.Small.Gate8Suffix24
import HiddenCircuits.Small.Gate8B5

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix23Rows : Fin 70 → List (Fin 70 × ℚ) := ![[],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(10,64)],
  [(10,-64)],
  [(10,-64)],
  [(12,32)],
  [],
  [(12,32)],
  [],
  [],
  [],
  [],
  [(20,64)],
  [(20,-64)],
  [(20,-64)],
  [(22,32)],
  [],
  [(22,32)],
  [(26,64)],
  [(26,-64)],
  [(26,-64)],
  [(28,32)],
  [],
  [(28,32)],
  [(31,128)],
  [],
  [(31,128)],
  [],
  [],
  [],
  [],
  [],
  [(40,64)],
  [(40,-64)],
  [(40,-64)],
  [(42,32)],
  [],
  [(42,32)],
  [(46,64)],
  [(46,-64)],
  [(46,-64)],
  [(48,32)],
  [],
  [(48,32)],
  [(51,128)],
  [],
  [(51,128)],
  [],
  [(56,64)],
  [(56,-64)],
  [(56,-64)],
  [(58,32)],
  [],
  [(58,32)],
  [(61,128)],
  [],
  [(61,128)],
  [],
  [(65,128)],
  [],
  [(65,128)],
  [],
  []]
def Gate8Suffix23 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix23Rows
theorem gate8_suffix_step23 : (fun a => sparseMultiplyRow (Gate8B5Rows a) Gate8Suffix24Rows) = Gate8Suffix23Rows := by
  decide +kernel
theorem gate8_suffix23 : ([Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix23 := by
  rw [List.prod_cons, gate8_suffix24]
  exact (sparseMatrix_mul_sparseMatrix Gate8B5Rows Gate8Suffix24Rows).trans
    (congrArg sparseMatrix gate8_suffix_step23)

end HiddenCircuits.Small
