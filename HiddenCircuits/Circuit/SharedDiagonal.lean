import HiddenCircuits.Circuit.DiagonalFamily

namespace HiddenCircuits.Circuit
open Polynomial
open scoped BigOperators

/-- The paper's finite available one-bit operations, including raw encoded T = 8X,
normalized X and H, and the auxiliary mixing gate. -/
inductive OneGate where
  | reset | copy | scale | signScale | swap | hadamard | mix | encodedSwap
  deriving DecidableEq, Fintype

def OneGate.matrix : OneGate → Matrix (Fin 2) (Fin 2) ℚ
  | .reset => !![1,0;1,0]
  | .copy => !![1,1;0,0]
  | .scale => !![2,0;0,1]
  | .signScale => !![-1,0;0,1/2]
  | .swap => !![0,1;1,0]
  | .hadamard => !![1,1;1,-1]
  | .mix => !![-2,4;4,8]
  | .encodedSwap => !![0,8;8,0]

def OneGate.logical (g : OneGate) : Matrix (CodeBits 1) (CodeBits 1) ℚ :=
  g.matrix.submatrix oneBitEquiv.symm oneBitEquiv.symm

/-- An explicitly placed circuit over the available one-bit basis and Δ constraints. -/
inductive DeltaGate (n : ℕ) where
  | one (p : Placement n 1) (g : OneGate)
  | constraint (p : Placement n 2)

def DeltaGate.matrix {n : ℕ} : DeltaGate n → Matrix (CodeBits n) (CodeBits n) ℚ
  | .one p g => p.lift g.logical
  | .constraint p => p.lift logicalDelta

def DeltaGate.mark {n : ℕ} : DeltaGate n → ℕ
  | .one _ _ => 0
  | .constraint _ => 1

def deltaOccurrences {n : ℕ} (w : List (DeltaGate n)) : ℕ := (w.map DeltaGate.mark).sum

def deltaCircuitMatrix {n : ℕ} (w : List (DeltaGate n)) : Matrix (CodeBits n) (CodeBits n) ℚ :=
  (w.map DeltaGate.matrix).prod

noncomputable section

/-- Every Δ position uses the same single indeterminate, regardless of intervening gates. -/
def DeltaGate.polynomial {n : ℕ} : DeltaGate n → Matrix (CodeBits n) (CodeBits n) ℚ[X]
  | .one p g => constantMatrix (p.lift g.logical)
  | .constraint p => p.lift logicalGPolynomial

 theorem DeltaGate.polynomial_zero {n : ℕ} (g : DeltaGate n) :
    evaluateMatrix 0 g.polynomial=g.matrix := by
  cases g with
  | one p g => exact evaluateMatrix_constant 0 _
  | constraint p => rw [polynomial,evaluate_lift,logicalGPolynomial_zero]; rfl

 theorem DeltaGate.polynomial_degree {n : ℕ} (g : DeltaGate n) :
    PolynomialMatrixDegree g.polynomial (2*g.mark) := by
  cases g with
  | one p g => exact PolynomialMatrixDegree.constant _
  | constraint p => exact p.lift_degree _ logicalGPolynomial_degree

/-- The entire original circuit, as one matrix of rational polynomials. -/
def deltaCircuitPolynomial {n : ℕ} (w : List (DeltaGate n)) : Matrix (CodeBits n) (CodeBits n) ℚ[X] :=
  (w.map DeltaGate.polynomial).prod

 theorem deltaCircuitPolynomial_zero {n : ℕ} (w : List (DeltaGate n)) :
    evaluateMatrix 0 (deltaCircuitPolynomial w)=deltaCircuitMatrix w := by
  induction w with
  | nil => exact evaluateMatrix_one 0
  | cons g w ih =>
    change evaluateMatrix 0 (g.polynomial * deltaCircuitPolynomial w)=g.matrix*deltaCircuitMatrix w
    rw [evaluateMatrix_mul,DeltaGate.polynomial_zero,ih]

/-- The exact degree bound2h holds with arbitrary interleaving of the fixed gates. -/
theorem deltaCircuitPolynomial_degree {n : ℕ} (w : List (DeltaGate n)) :
    PolynomialMatrixDegree (deltaCircuitPolynomial w) (2*deltaOccurrences w) := by
  induction w with
  | nil => exact PolynomialMatrixDegree.one
  | cons g w ih =>
    have h := g.polynomial_degree.mul ih
    simpa only [deltaCircuitPolynomial,deltaOccurrences,List.map_cons,List.prod_cons,List.sum_cons,Nat.mul_add] using h

/-- Actual sampled replacement is the fixed G conjugated by two copies of K(2^u). -/
def DeltaGate.sample {n : ℕ} (u : ℕ) : DeltaGate n → Matrix (CodeBits n) (CodeBits n) ℚ
  | .one p g => p.lift g.logical
  | .constraint p => p.lift
      ((conjugatingDiagonal ((2:ℚ)^u)⁻¹ * G * conjugatingDiagonal ((2:ℚ)^u)).submatrix
        twoBitEquiv.symm twoBitEquiv.symm)

 theorem DeltaGate.polynomial_sample {n : ℕ} (u : ℕ) (g : DeltaGate n) :
    evaluateMatrix ((2:ℚ)^u) g.polynomial=g.sample u := by
  cases g with
  | one p g => exact evaluateMatrix_constant _ _
  | constraint p =>
    rw [polynomial,evaluate_lift]
    unfold sample
    congr 1
    ext x y
    exact congrFun (congrFun (GPolynomial_conjugate ((2:ℚ)^u) (by positivity))
      (twoBitEquiv.symm x)) (twoBitEquiv.symm y)

 def sampledDeltaCircuit {n : ℕ} (w : List (DeltaGate n)) (u : ℕ) : Matrix (CodeBits n) (CodeBits n) ℚ :=
  (w.map (DeltaGate.sample u)).prod

 theorem deltaCircuitPolynomial_sample {n : ℕ} (w : List (DeltaGate n)) (u : ℕ) :
    evaluateMatrix ((2:ℚ)^u) (deltaCircuitPolynomial w)=sampledDeltaCircuit w u := by
  induction w with
  | nil => exact evaluateMatrix_one _
  | cons g w ih =>
    change evaluateMatrix ((2:ℚ)^u) (g.polynomial*deltaCircuitPolynomial w)=g.sample u*sampledDeltaCircuit w u
    rw [evaluateMatrix_mul,DeltaGate.polynomial_sample,ih]

/-- The paper's2^u nodes are genuinely distinct rationals. -/
def geometricNode {d : ℕ} (i : Fin (d+1)) : ℚ := (2:ℚ)^i.val

 theorem geometricNode_injective (d : ℕ) : Function.Injective (@geometricNode d) := by
  intro i j h
  exact Fin.ext ((pow_right_strictMono₀ (by norm_num : (1:ℚ)<2)).injective h)

 def geometricInterpolate (d : ℕ) (f : Fin (d+1) → ℚ) : ℚ[X] :=
  Lagrange.interpolate Finset.univ geometricNode f

 theorem geometricInterpolate_correct (d : ℕ) (p : ℚ[X]) (hp : p.natDegree≤d) :
    geometricInterpolate d (fun i => p.eval (geometricNode i))=p := by
  apply Lagrange.interpolate_poly_eq_self
  · exact (geometricNode_injective d).injOn
  · simp only [Finset.card_univ,Fintype.card_fin]
    exact lt_of_le_of_lt p.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hp)

/-- Exact shared-parameter recovery for an actual placed Δ circuit using only2h+1 sampled entries.
Expansion into WordEval and binary-time compilation are separate subsequent steps. -/
theorem recover_deltaCircuit {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) :
    (geometricInterpolate (2*deltaOccurrences w)
      (fun u => sampledDeltaCircuit w u.val x y)).eval 0 = deltaCircuitMatrix w x y := by
  have hi := geometricInterpolate_correct (2*deltaOccurrences w) (deltaCircuitPolynomial w x y)
    (deltaCircuitPolynomial_degree w x y)
  have hs : (fun u : Fin (2*deltaOccurrences w+1) =>
      (deltaCircuitPolynomial w x y).eval (geometricNode u)) =
      (fun u => sampledDeltaCircuit w u.val x y) := by
    funext u
    exact congrFun (congrFun (deltaCircuitPolynomial_sample w u.val) x) y
  rw [hs] at hi
  rw [hi]
  exact congrFun (congrFun (deltaCircuitPolynomial_zero w) x) y

end
end HiddenCircuits.Circuit
