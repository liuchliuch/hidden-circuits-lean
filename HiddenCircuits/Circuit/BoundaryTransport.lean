import HiddenCircuits.Circuit.BoundaryPrograms

/-! Arbitrary logical input/output entries reduce to zero boundaries by literal
one-bit X gates. No chosen basis-changing circuit is supplied as input. -/
namespace HiddenCircuits.Circuit
open scoped Kronecker BigOperators

def boundaryProgram : (n : ℕ)→CodeBits n→ConstraintProgram n
  | 0,_=>.identity 0
  | n+1,x=>(if x.1=0 then ConstraintProgram.identity (n+1)
      else ⟨1,[.one (headPlacement n) .swap]⟩).compose
        ((boundaryProgram n x.2).lift (tailPlacement n))
def boundaryMatrix : (n : ℕ)→CodeBits n→Matrix (CodeBits n) (CodeBits n) ℚ
  | 0,_=>1
  | n+1,x=>(if x.1=0 then (1:Matrix (Fin 2) (Fin 2) ℚ) else OneGate.swap.matrix) ⊗ₖ boundaryMatrix n x.2

lemma boundaryProgram_scalar (n : ℕ) (x : CodeBits n) : (boundaryProgram n x).scalar=1 := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rcases x with ⟨i,x⟩
    simp only [boundaryProgram,ConstraintProgram.compose,ConstraintProgram.lift,ih]
    split_ifs <;> simp [ConstraintProgram.identity]
lemma boundaryProgram_length (n : ℕ) (x : CodeBits n) : (boundaryProgram n x).gates.length ≤ n := by
  induction n with
  | zero=>simp [boundaryProgram,ConstraintProgram.identity]
  | succ n ih=>
    rcases x with ⟨i,x⟩
    have ht:=ih x
    simp only [boundaryProgram,ConstraintProgram.compose,ConstraintProgram.lift,List.length_append,List.length_map]
    split_ifs <;> simp only [ConstraintProgram.identity,List.length_nil,List.length_cons] <;> omega
lemma boundaryProgram_matrix (n : ℕ) (x : CodeBits n) : (boundaryProgram n x).matrix=boundaryMatrix n x := by
  induction n with
  | zero=>exact ConstraintProgram.identity_matrix 0
  | succ n ih=>
    rcases x with ⟨i,x⟩
    rw [boundaryProgram,ConstraintProgram.compose_matrix,ConstraintProgram.lift_matrix,ih,tailPlacement_lift]
    by_cases hi:i=0
    · simp only [hi,↓reduceIte,ConstraintProgram.identity_matrix,one_mul,boundaryMatrix]
    · have hh : (show ConstraintProgram (n+1) from ⟨1,[.one (headPlacement n) .swap]⟩).matrix=
          OneGate.swap.matrix ⊗ₖ (1:Matrix (CodeBits n) (CodeBits n) ℚ) := by
        simp only [ConstraintProgram.matrix,constraintCircuitMatrix,List.map_cons,List.map_nil,List.prod_cons,
          List.prod_nil,mul_one,one_smul,ConstraintGate.matrix,headPlacement_lift]
      simp only [hi,↓reduceIte,hh,boundaryMatrix]
      rw [←Matrix.mul_kronecker_mul,mul_one,one_mul]
lemma boundaryMatrix_row (n : ℕ) (x y : CodeBits n) :
    boundaryMatrix n x (zeroBits n) y=if x=y then 1 else 0 := by
  induction n with
  | zero=>cases x;cases y;rfl
  | succ n ih=>
    rcases x with ⟨i,x⟩;rcases y with ⟨j,y⟩
    simp only [boundaryMatrix,zeroBits,Matrix.kroneckerMap_apply,ih,Prod.mk.injEq]
    fin_cases i <;> fin_cases j <;> simp [OneGate.matrix,Matrix.one_apply,CodeBits,Prod.mk.injEq]
lemma boundaryMatrix_column (n : ℕ) (x y : CodeBits n) :
    boundaryMatrix n x y (zeroBits n)=if y=x then 1 else 0 := by
  induction n with
  | zero=>cases x;cases y;rfl
  | succ n ih=>
    rcases x with ⟨i,x⟩;rcases y with ⟨j,y⟩
    simp only [boundaryMatrix,zeroBits,Matrix.kroneckerMap_apply,ih,Prod.mk.injEq]
    fin_cases i <;> fin_cases j <;> simp [OneGate.matrix,Matrix.one_apply,CodeBits,Prod.mk.injEq]

def zeroBoundaryCircuit {n : ℕ} (w : List (ConstraintGate n)) (x y : CodeBits n) : List (ConstraintGate n) :=
  (boundaryProgram n x).gates++w++(boundaryProgram n y).gates
lemma zeroBoundaryCircuit_length {n : ℕ} (w : List (ConstraintGate n)) (x y : CodeBits n) :
    (zeroBoundaryCircuit w x y).length ≤ 2*n+w.length := by
  have hx:=boundaryProgram_length n x;have hy:=boundaryProgram_length n y
  simp only [zeroBoundaryCircuit,List.length_append];omega
lemma boundary_gates_matrix (n : ℕ) (x : CodeBits n) :
    constraintCircuitMatrix (boundaryProgram n x).gates=boundaryMatrix n x := by
  have h:=boundaryProgram_matrix n x
  simpa only [ConstraintProgram.matrix,boundaryProgram_scalar,one_smul] using h
lemma zeroBoundaryCircuit_correct {n : ℕ} (w : List (ConstraintGate n)) (x y : CodeBits n) :
    constraintCircuitMatrix (zeroBoundaryCircuit w x y) (zeroBits n) (zeroBits n)=constraintCircuitMatrix w x y := by
  simp only [zeroBoundaryCircuit,constraintCircuitMatrix,List.map_append,List.prod_append]
  change (constraintCircuitMatrix (boundaryProgram n x).gates * constraintCircuitMatrix w *
    constraintCircuitMatrix (boundaryProgram n y).gates) (zeroBits n) (zeroBits n)=_
  rw [boundary_gates_matrix,boundary_gates_matrix]
  simp only [Matrix.mul_apply,boundaryMatrix_row,boundaryMatrix_column]
  simp
  rfl
end HiddenCircuits.Circuit
