import HiddenCircuits.Complexity.DeltaEncoding
import HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalizeModel

/-! Bit-size bounds for native Delta oracle answers, derived directly from
integer tensor-local matrices after clearing one factor of two per gate. -/
namespace HiddenCircuits.Circuit.Runtime.DeltaValues
open Complexity BinaryArithmetic
open scoped BigOperators

def one (g : OneGate) : Matrix (Fin 2) (Fin 2) ℤ := match g with
  | .reset=>!![2,0;2,0]
  | .copy=>!![2,2;0,0]
  | .scale=>!![4,0;0,2]
  | .signScale=>!![-2,0;0,1]
  | .swap=>!![0,2;2,0]
  | .hadamard=>!![2,2;2,-2]
  | .mix=>!![-4,8;8,16]
  | .encodedSwap=>!![0,16;16,0]
def diagonal : Matrix (Fin 4) (Fin 4) ℤ := Matrix.diagonal ![-4,-6,4,2]
def gate {n : ℕ} : DeltaGate n→Matrix (CodeBits n) (CodeBits n) ℤ
  | .one p g=>p.lift ((one g).submatrix oneBitEquiv.symm oneBitEquiv.symm)
  | .constraint p=>p.lift (diagonal.submatrix twoBitEquiv.symm twoBitEquiv.symm)
lemma one_cast (g : OneGate) (x y : Fin 2) : (one g x y:ℚ)=2*g.matrix x y := by
  cases g <;> fin_cases x <;> fin_cases y <;> norm_num [one,OneGate.matrix]
lemma one_abs (g : OneGate) (x y : Fin 2) : (one g x y).natAbs ≤ 16 := by
  cases g <;> fin_cases x <;> fin_cases y <;> norm_num [one]
lemma diagonal_cast (x y : Fin 4) : (diagonal x y:ℚ)=2*delta x y := by
  fin_cases x <;> fin_cases y <;> norm_num [diagonal,delta,Matrix.diagonal_apply]
lemma diagonal_abs (x y : Fin 4) : (diagonal x y).natAbs ≤ 16 := by
  fin_cases x <;> fin_cases y <;> norm_num [diagonal,Matrix.diagonal_apply]
lemma gate_cast {n : ℕ} (a : DeltaGate n) (x y : CodeBits n) :
    (gate a x y:ℚ)=2*a.matrix x y := by
  cases a with
  | one p g=>
    simp only [gate,DeltaGate.matrix,OneGate.logical,Placement.lift,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.one_apply]
    split_ifs <;> simp [one_cast]
  | constraint p=>
    simp only [gate,DeltaGate.matrix,logicalDelta,Placement.lift,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.one_apply]
    split_ifs <;> simp [diagonal_cast]
lemma gate_abs {n : ℕ} (a : DeltaGate n) (x y : CodeBits n) : (gate a x y).natAbs ≤ 16 := by
  cases a with
  | one p g=>
    simp only [gate,Placement.lift,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.one_apply]
    split_ifs <;> simpa using one_abs g (oneBitEquiv.symm (p.equiv.symm x).2.1) (oneBitEquiv.symm (p.equiv.symm y).2.1)
  | constraint p=>
    simp only [gate,Placement.lift,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.one_apply]
    split_ifs <;> simpa using diagonal_abs (twoBitEquiv.symm (p.equiv.symm x).2.1) (twoBitEquiv.symm (p.equiv.symm y).2.1)

def integerMatrix {n : ℕ} (w : List (DeltaGate n)) : Matrix (CodeBits n) (CodeBits n) ℤ := (w.map gate).prod
lemma integer_cast {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) :
    (integerMatrix w x y:ℚ)=(2:ℚ)^w.length*deltaCircuitMatrix w x y := by
  induction w generalizing x y with
  | nil=>simp [integerMatrix,deltaCircuitMatrix,Matrix.one_apply]
  | cons a w ih=>
    simp only [integerMatrix,deltaCircuitMatrix,List.map_cons,List.prod_cons,Matrix.mul_apply,Int.cast_sum,Int.cast_mul,List.length_cons,pow_succ]
    change ∑ z, (gate a x z:ℚ)*(integerMatrix w z y:ℚ) = _
    simp only [gate_cast,ih]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz;dsimp only [deltaCircuitMatrix];ring
end HiddenCircuits.Circuit.Runtime.DeltaValues
