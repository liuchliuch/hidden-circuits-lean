import HiddenCircuits.Small.Gate8Suffix8
import HiddenCircuits.Small.Gate8E2

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix7Rows : Fin 70 → List (Fin 70 × ℚ) := ![[(12,-14336), (20,-2048), (22,1024), (31,-8192), (40,-4096), (42,6144), (51,-24576), (61,45056)],
  [(12,-14336), (20,-2048), (22,1024), (31,-8192), (40,-4096), (42,9216), (51,-12288), (61,-16384)],
  [(10,2048), (12,-4096), (20,-1024), (40,-3072), (42,2048), (51,8192), (61,8192)],
  [(10,2048), (12,4096), (20,-1024), (31,8192), (40,-3072), (42,-2048), (51,24576), (61,24576)],
  [(10,-2048), (12,6144), (20,1024), (31,8192), (40,3072), (42,-3072), (51,20480), (61,20480)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(40,2048), (42,-1024), (51,-4096), (61,-12288)],
  [(40,1024), (61,-8192)],
  [(40,1024), (61,-8192)],
  [(40,-1024), (61,-4096)],
  [(40,1024), (61,-8192)],
  [(40,1024), (61,-8192)],
  [(40,-1024), (61,-4096)],
  [(42,1024), (51,4096), (61,-4096)],
  [(42,512), (51,2048), (61,-2048)],
  [(42,512), (51,2048), (61,-2048)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(20,2048), (22,-1024), (31,-4096), (61,-12288)],
  [(20,1024), (61,-8192)],
  [(20,1024), (61,-8192)],
  [(20,-1024), (61,-4096)],
  [(20,1024), (61,-8192)],
  [(20,1024), (61,-8192)],
  [(20,-1024), (61,-4096)],
  [(22,1024), (31,4096), (61,-4096)],
  [(22,512), (31,2048), (61,-2048)],
  [(22,512), (31,2048), (61,-2048)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  []]
def Gate8Suffix7 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix7Rows
theorem gate8_suffix_step7 : (fun a => sparseMultiplyRow (Gate8E2Rows a) Gate8Suffix8Rows) = Gate8Suffix7Rows := by
  decide +kernel
theorem gate8_suffix7 : ([Gate8E2, Gate8D2, Gate8R2, Gate8R1, Gate8D2, Gate8R2, Gate8B1, Gate8R2, Gate8R1, Gate8R0, Gate8E2, Gate8D2, Gate8R2, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix7 := by
  rw [List.prod_cons, gate8_suffix8]
  exact (sparseMatrix_mul_sparseMatrix Gate8E2Rows Gate8Suffix8Rows).trans
    (congrArg sparseMatrix gate8_suffix_step7)

end HiddenCircuits.Small
