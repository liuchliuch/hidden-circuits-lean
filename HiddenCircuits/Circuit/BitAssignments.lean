import HiddenCircuits.Circuit.ConstraintReduction
import HiddenCircuits.Complexity.GraphEncoding

namespace HiddenCircuits.Circuit
open scoped BigOperators Kronecker

/-- The actual one-bit value correspondence,0=false and1=true. -/
def finBitBool : Fin 2 ≃ Bool where
  toFun i := decide (i=1)
  invFun b := if b then 1 else 0
  left_inv i := by fin_cases i <;> rfl
  right_inv b := by cases b <;> rfl

def bitsToAssignment : (n : ℕ) → CodeBits n → (Fin n → Bool)
  | 0,_,i => Fin.elim0 i
  | n+1,x,i => Fin.cases (finBitBool x.1) (bitsToAssignment n x.2) i

def assignmentToBits : (n : ℕ) → (Fin n → Bool) → CodeBits n
  | 0,_ => PUnit.unit
  | n+1,x => (finBitBool.symm (x 0),assignmentToBits n (fun i => x i.succ))

 theorem assignment_bits_inverse (n : ℕ) (x : Fin n → Bool) :
    bitsToAssignment n (assignmentToBits n x)=x := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [bitsToAssignment,assignmentToBits]
    · exact congrFun (ih (fun i => x i.succ)) j

 theorem bits_assignment_inverse (n : ℕ) (x : CodeBits n) :
    assignmentToBits n (bitsToAssignment n x)=x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    rcases x with ⟨a,x⟩
    change (finBitBool.symm (finBitBool a),assignmentToBits n (bitsToAssignment n x))=(a,x)
    rw [Equiv.symm_apply_apply,ih x]

/-- Canonical logical tuples enumerate every source graph assignment exactly once. -/
def assignmentEquiv (n : ℕ) : CodeBits n ≃ (Fin n → Bool) where
  toFun := bitsToAssignment n
  invFun := assignmentToBits n
  left_inv := bits_assignment_inverse n
  right_inv := assignment_bits_inverse n

/-- Literal all-zero input/output string. -/
def zeroBits : (n : ℕ) → CodeBits n
  | 0 => PUnit.unit
  | n+1 => (0,zeroBits n)

@[simp] theorem zeroBits_assignment (n : ℕ) : bitsToAssignment n (zeroBits n)=fun _ => false := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun ih j

/-- The literal tensor of available E₀ operations. -/
def preparationMatrix : (n : ℕ) → Matrix (CodeBits n) (CodeBits n) ℚ
  | 0 => 1
  | n+1 => OneGate.copy.matrix ⊗ₖ preparationMatrix n

/-- The literal tensor of available R₀ reset operations. -/
def resetMatrix : (n : ℕ) → Matrix (CodeBits n) (CodeBits n) ℚ
  | 0 => 1
  | n+1 => OneGate.reset.matrix ⊗ₖ resetMatrix n

 theorem preparation_zero_row (n : ℕ) (x : CodeBits n) : preparationMatrix n (zeroBits n) x=1 := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    rcases x with ⟨a,x⟩
    change OneGate.copy.matrix 0 a * preparationMatrix n (zeroBits n) x=1
    rw [ih x]
    fin_cases a <;> norm_num [OneGate.matrix]

 theorem reset_zero_column (n : ℕ) (x : CodeBits n) : resetMatrix n x (zeroBits n)=1 := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    rcases x with ⟨a,x⟩
    change OneGate.reset.matrix a 0 * resetMatrix n x (zeroBits n)=1
    rw [ih x]
    fin_cases a <;> norm_num [OneGate.matrix]

/-- State preparation and final reset sum every surviving coefficient exactly once. -/
theorem preparation_reset_sum (n : ℕ) (weight : CodeBits n → ℚ) :
    (preparationMatrix n * Matrix.diagonal weight * resetMatrix n) (zeroBits n) (zeroBits n)=∑ x, weight x := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.mul_diagonal,preparation_zero_row,reset_zero_column,one_mul,mul_one]

/-- Actual independent-assignment predicate of the binary source graph representation. -/
def codeIndependent {n : ℕ} (G : Complexity.MatrixGraph n) (x : CodeBits n) : Prop :=
  G.ValidIndependent (bitsToAssignment n x)

noncomputable instance {n : ℕ} (G : Complexity.MatrixGraph n) (x : CodeBits n) : Decidable (codeIndependent G x) :=
  inferInstanceAs (Decidable (G.ValidIndependent (bitsToAssignment n x)))

noncomputable def independentCodeEquiv {n : ℕ} (G : Complexity.MatrixGraph n) :
    {x : CodeBits n // codeIndependent G x} ≃ G.IndependentCertificate where
  toFun x := ⟨assignmentEquiv n x.val,x.property⟩
  invFun x := ⟨(assignmentEquiv n).symm x.val,by
    change G.ValidIndependent (assignmentEquiv n ((assignmentEquiv n).symm x.val))
    simpa using x.property⟩
  left_inv x := by apply Subtype.ext; exact (assignmentEquiv n).symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact (assignmentEquiv n).apply_symm_apply x.val

/-- The assignment indicator sums to the count of actual independent vertex sets. -/
theorem independent_indicator_sum {n : ℕ} (G : Complexity.MatrixGraph n) :
    (∑ x : CodeBits n, if codeIndependent G x then (1:ℚ) else 0)=G.independentCount := by
  classical
  have he := Fintype.card_congr (independentCodeEquiv G)
  rw [← G.independentCount_eq_certificates] at he
  calc
    (∑ x : CodeBits n, if codeIndependent G x then (1:ℚ) else 0) =
        (Fintype.card {x : CodeBits n // codeIndependent G x} : ℚ) := by
      simp [Fintype.card_subtype]
    _ = _ := by rw [he]

/-- Section8's counting sandwich on actual Boolean assignments and an actual source graph. -/
theorem independent_counting_sandwich {n : ℕ} (G : Complexity.MatrixGraph n) :
    (preparationMatrix n * Matrix.diagonal (fun x => if codeIndependent G x then (1:ℚ) else 0) * resetMatrix n)
      (zeroBits n) (zeroBits n)=G.independentCount := by
  rw [preparation_reset_sum,independent_indicator_sum]

end HiddenCircuits.Circuit
