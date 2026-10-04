import HiddenCircuits.Small.Gate8Suffix20
import HiddenCircuits.Small.Gate8R2

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix19Rows : Fin 70 → List (Fin 70 × ℚ) := ![[(10,128), (12,-64)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(10,64)],
  [(10,64)],
  [(10,-64)],
  [(12,64)],
  [(12,32)],
  [(12,32)],
  [(26,-256), (28,128), (31,768)],
  [(26,-128), (31,512)],
  [(26,-128), (31,512)],
  [(26,128), (31,256)],
  [(20,64)],
  [(20,64)],
  [(20,-64)],
  [(22,64)],
  [(22,32)],
  [(22,32)],
  [(20,64)],
  [(20,64)],
  [(20,-64)],
  [(22,64)],
  [(22,32)],
  [(22,32)],
  [(31,256)],
  [(31,128)],
  [(31,128)],
  [],
  [(46,-256), (48,128), (51,768)],
  [(46,-128), (51,512)],
  [(46,-128), (51,512)],
  [(46,128), (51,256)],
  [(40,64)],
  [(40,64)],
  [(40,-64)],
  [(42,64)],
  [(42,32)],
  [(42,32)],
  [(40,64)],
  [(40,64)],
  [(40,-64)],
  [(42,64)],
  [(42,32)],
  [(42,32)],
  [(51,256)],
  [(51,128)],
  [(51,128)],
  [],
  [(56,128), (65,-1024)],
  [(56,128), (65,-1024)],
  [(56,-128), (65,-512)],
  [(58,128), (65,-512)],
  [(58,64), (65,-256)],
  [(58,64), (65,-256)],
  [(61,256)],
  [(61,128)],
  [(61,128)],
  [],
  [(61,256)],
  [(61,128)],
  [(61,128)],
  [],
  []]
def Gate8Suffix19 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix19Rows
theorem gate8_suffix_step19 : (fun a => sparseMultiplyRow (Gate8R2Rows a) Gate8Suffix20Rows) = Gate8Suffix19Rows := by
  decide +kernel
theorem gate8_suffix19 : ([Gate8R2, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix19 := by
  rw [List.prod_cons, gate8_suffix20]
  exact (sparseMatrix_mul_sparseMatrix Gate8R2Rows Gate8Suffix20Rows).trans
    (congrArg sparseMatrix gate8_suffix_step19)

end HiddenCircuits.Small
