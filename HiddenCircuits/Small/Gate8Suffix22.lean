import HiddenCircuits.Small.Gate8Suffix23
import HiddenCircuits.Small.Gate8R6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix22Rows : Fin 70 → List (Fin 70 × ℚ) := ![[],
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
  [(12,32)],
  [(12,64)],
  [],
  [],
  [],
  [],
  [(20,64)],
  [(20,-64)],
  [(20,-64)],
  [(22,32)],
  [(22,32)],
  [(22,64)],
  [(26,64)],
  [(26,-64)],
  [(26,-64)],
  [(28,32)],
  [(28,32)],
  [(28,64)],
  [(31,128)],
  [(31,128)],
  [(31,256)],
  [],
  [],
  [],
  [],
  [],
  [(40,64)],
  [(40,-64)],
  [(40,-64)],
  [(42,32)],
  [(42,32)],
  [(42,64)],
  [(46,64)],
  [(46,-64)],
  [(46,-64)],
  [(48,32)],
  [(48,32)],
  [(48,64)],
  [(51,128)],
  [(51,128)],
  [(51,256)],
  [],
  [(56,64)],
  [(56,-64)],
  [(56,-64)],
  [(58,32)],
  [(58,32)],
  [(58,64)],
  [(61,128)],
  [(61,128)],
  [(61,256)],
  [],
  [(65,128)],
  [(65,128)],
  [(65,256)],
  [],
  []]
def Gate8Suffix22 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix22Rows
theorem gate8_suffix_step22 : (fun a => sparseMultiplyRow (Gate8R6Rows a) Gate8Suffix23Rows) = Gate8Suffix22Rows := by
  decide +kernel
theorem gate8_suffix22 : ([Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix22 := by
  rw [List.prod_cons, gate8_suffix23]
  exact (sparseMatrix_mul_sparseMatrix Gate8R6Rows Gate8Suffix23Rows).trans
    (congrArg sparseMatrix gate8_suffix_step22)

end HiddenCircuits.Small
