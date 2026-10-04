import HiddenCircuits.Small.Gate8Suffix25
import HiddenCircuits.Small.Gate8R6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix24Rows : Fin 70 → List (Fin 70 × ℚ) := ![[],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(10,-32)],
  [(10,-32)],
  [(10,-32)],
  [(12,32)],
  [(12,32)],
  [],
  [],
  [],
  [],
  [],
  [(20,-32)],
  [(20,-32)],
  [(20,-32)],
  [(22,32)],
  [(22,32)],
  [],
  [(26,-32)],
  [(26,-32)],
  [(26,-32)],
  [(28,32)],
  [(28,32)],
  [],
  [(31,128)],
  [(31,128)],
  [],
  [],
  [],
  [],
  [],
  [],
  [(40,-32)],
  [(40,-32)],
  [(40,-32)],
  [(42,32)],
  [(42,32)],
  [],
  [(46,-32)],
  [(46,-32)],
  [(46,-32)],
  [(48,32)],
  [(48,32)],
  [],
  [(51,128)],
  [(51,128)],
  [],
  [],
  [(56,-32)],
  [(56,-32)],
  [(56,-32)],
  [(58,32)],
  [(58,32)],
  [],
  [(61,128)],
  [(61,128)],
  [],
  [],
  [(65,128)],
  [(65,128)],
  [],
  [],
  []]
def Gate8Suffix24 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix24Rows
theorem gate8_suffix_step24 : (fun a => sparseMultiplyRow (Gate8R6Rows a) Gate8Suffix25Rows) = Gate8Suffix24Rows := by
  decide +kernel
theorem gate8_suffix24 : ([Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix24 := by
  rw [List.prod_cons, gate8_suffix25]
  exact (sparseMatrix_mul_sparseMatrix Gate8R6Rows Gate8Suffix25Rows).trans
    (congrArg sparseMatrix gate8_suffix_step24)

end HiddenCircuits.Small
