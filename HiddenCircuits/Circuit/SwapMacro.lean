import HiddenCircuits.Circuit.WirePermutation
import HiddenCircuits.Circuit.Conjugation
import HiddenCircuits.Circuit.SampleWords

namespace HiddenCircuits.Circuit
open scoped BigOperators

def hadamardFirst : Matrix (Fin 4) (Fin 4) ℚ := !![1,0,1,0;0,1,0,1;1,0,-1,0;0,1,0,-1]
def hadamardSecond : Matrix (Fin 4) (Fin 4) ℚ := !![1,1,0,0;1,-1,0,0;0,0,1,1;0,0,1,-1]
def cnotForward : Matrix (Fin 4) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,0,1;0,0,1,0]
def cnotBackward : Matrix (Fin 4) (Fin 4) ℚ := !![1,0,0,0;0,0,0,1;0,0,1,0;0,1,0,0]
def swapTwo : Matrix (Fin 4) (Fin 4) ℚ := !![1,0,0,0;0,0,1,0;0,1,0,0;0,0,0,1]

 theorem first_hadamard_basis : (firstBit.lift OneGate.hadamard.logical).submatrix twoBitEquiv twoBitEquiv=hadamardFirst := by
  decide +kernel
 theorem second_hadamard_basis : (secondBit.lift OneGate.hadamard.logical).submatrix twoBitEquiv twoBitEquiv=hadamardSecond := by
  decide +kernel
 theorem full_controlledSign_basis : (fullTwoBits.lift (logicalConstraint (-1))).submatrix twoBitEquiv twoBitEquiv=constraintDiagonal (-1) := by
  decide +kernel

 theorem cnotForward_identity : hadamardSecond * constraintDiagonal (-1) * hadamardSecond=(2:ℚ) • cnotForward := by
  decide +kernel
 theorem cnotBackward_identity : hadamardFirst * constraintDiagonal (-1) * hadamardFirst=(2:ℚ) • cnotBackward := by
  decide +kernel
 theorem swap_cnot_identity : cnotForward*cnotBackward*cnotForward=swapTwo := by
  decide +kernel

/-- The complete literal H/CZ word for an adjacent exchange, retaining its factor8. -/
theorem swap_hadamard_word :
    (hadamardSecond*constraintDiagonal (-1)*hadamardSecond) *
      (hadamardFirst*constraintDiagonal (-1)*hadamardFirst) *
      (hadamardSecond*constraintDiagonal (-1)*hadamardSecond) = (8:ℚ) • swapTwo := by
  rw [cnotForward_identity,cnotBackward_identity]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,swap_cnot_identity]
  norm_num

/-- An explicit9-gate constraint circuit, with six H and three CZ gates. -/
def swapLocalCircuit : List (ConstraintGate 2) :=
  [.one secondBit .hadamard,.controlledSign fullTwoBits,.one secondBit .hadamard,
   .one firstBit .hadamard,.controlledSign fullTwoBits,.one firstBit .hadamard,
   .one secondBit .hadamard,.controlledSign fullTwoBits,.one secondBit .hadamard]

 theorem swapLocalCircuit_length : swapLocalCircuit.length=9 := rfl

 theorem swapLocalCircuit_basis :
    (constraintCircuitMatrix swapLocalCircuit).submatrix twoBitEquiv twoBitEquiv=(8:ℚ) • swapTwo := by
  rw [constraintCircuitMatrix,reindex_list_prod]
  simp only [swapLocalCircuit,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    ConstraintGate.matrix,first_hadamard_basis,second_hadamard_basis,full_controlledSign_basis,mul_one]
  simpa only [Matrix.mul_assoc] using swap_hadamard_word

/-- The finite permutation is the real exchange of the two Boolean assignment coordinates. -/
theorem wireSwap_basis :
    (wireMatrix (Equiv.swap (0:Fin 2) 1)).submatrix twoBitEquiv twoBitEquiv=swapTwo := by
  decide +kernel

 theorem swapLocalCircuit_matrix :
    constraintCircuitMatrix swapLocalCircuit=(8:ℚ) • wireMatrix (Equiv.swap (0:Fin 2) 1) := by
  ext x y
  obtain ⟨a,rfl⟩ := twoBitEquiv.surjective x
  obtain ⟨b,rfl⟩ := twoBitEquiv.surjective y
  have h := congrFun (congrFun swapLocalCircuit_basis a) b
  have hs := congrFun (congrFun wireSwap_basis a) b
  change _ = (8:ℚ) * _
  simpa only [Matrix.submatrix_apply,Matrix.smul_apply,smul_eq_mul,← hs] using h

/-- Exact scalar programs retain normalization factors of gate macros. -/
structure ConstraintProgram (n : ℕ) where
  scalar : ℚ
  gates : List (ConstraintGate n)

def ConstraintProgram.matrix {n : ℕ} (p : ConstraintProgram n) : Matrix (CodeBits n) (CodeBits n) ℚ :=
  p.scalar • constraintCircuitMatrix p.gates

def swapLocalProgram : ConstraintProgram 2 := ⟨1/8,swapLocalCircuit⟩

 theorem swapLocalProgram_matrix : swapLocalProgram.matrix=wireMatrix (Equiv.swap (0:Fin 2) 1) := by
  simp only [swapLocalProgram,ConstraintProgram.matrix,swapLocalCircuit_matrix,smul_smul]
  norm_num

end HiddenCircuits.Circuit
