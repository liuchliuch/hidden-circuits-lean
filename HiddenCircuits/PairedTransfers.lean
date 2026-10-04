import HiddenCircuits.BlockDual
import HiddenCircuits.TracePotential

namespace HiddenCircuits
open scoped BigOperators

namespace State
/-- Complement as an actual involution of half-filled subset states. -/
def halfComplement {p : ℕ} (S : State (2*p) p) : State (2*p) p :=
  castParticles (by omega) S.complement

@[simp] theorem halfComplement_val {p : ℕ} (S : State (2*p) p) :
    S.halfComplement.val=S.valᶜ := rfl

@[simp] theorem halfComplement_halfComplement {p : ℕ} (S : State (2*p) p) :
    S.halfComplement.halfComplement=S := by
  apply Subtype.ext
  simp

 def halfComplementEquiv (p : ℕ) : State (2*p) p ≃ State (2*p) p where
  toFun := halfComplement
  invFun := halfComplement
  left_inv := halfComplement_halfComplement
  right_inv := halfComplement_halfComplement

 theorem halfComplement_injective (p : ℕ) : Function.Injective (halfComplement (p:=p)) :=
  (halfComplementEquiv p).injective
end State

/-- The literal complement matrix J at half filling. -/
def complementMatrix (p : ℕ) : Matrix (State (2*p) p) (State (2*p) p) ℚ :=
  fun S T => if T=S.halfComplement then 1 else 0

 theorem complementMatrix_mul {p : ℕ} (M : Matrix (State (2*p) p) (State (2*p) p) ℚ)
    (S T : State (2*p) p) : (complementMatrix p * M) S T=M S.halfComplement T := by
  simp [Matrix.mul_apply,complementMatrix]

 theorem mul_complementMatrix {p : ℕ} (M : Matrix (State (2*p) p) (State (2*p) p) ℚ)
    (S T : State (2*p) p) : (M * complementMatrix p) S T=M S T.halfComplement := by
  have hc : ∀ U : State (2*p) p, T=U.halfComplement ↔ U=T.halfComplement := by
    intro U
    constructor
    · intro h
      simpa only [State.halfComplement_halfComplement] using (congrArg State.halfComplement h).symm
    · intro h
      rw [h,State.halfComplement_halfComplement]
  simp [Matrix.mul_apply,complementMatrix,hc]

@[simp] theorem complementMatrix_square (p : ℕ) : complementMatrix p * complementMatrix p=1 := by
  ext S T
  rw [complementMatrix_mul]
  simp [complementMatrix,Matrix.one_apply,eq_comm]

/-- Complement-transpose is the actual dual operation on the same half-filled state space. -/
def halfDual {p : ℕ} (M : Matrix (State (2*p) p) (State (2*p) p) ℚ) :
    Matrix (State (2*p) p) (State (2*p) p) ℚ := fun S T => M T.halfComplement S.halfComplement

 theorem halfDual_eq {p : ℕ} (M : Matrix (State (2*p) p) (State (2*p) p) ℚ) :
    halfDual M = complementMatrix p * M.transpose * complementMatrix p := by
  ext S T
  rw [mul_complementMatrix,complementMatrix_mul]
  rfl

@[simp] theorem halfDual_one (p : ℕ) : halfDual (1 : Matrix (State (2*p) p) (State (2*p) p) ℚ)=1 := by
  ext S T
  simp [halfDual,Matrix.one_apply,(State.halfComplement_injective p).eq_iff,eq_comm]

 theorem halfDual_mul {p : ℕ} (M N : Matrix (State (2*p) p) (State (2*p) p) ℚ) :
    halfDual (M*N)=halfDual N * halfDual M := by
  rw [halfDual_eq,Matrix.transpose_mul,halfDual_eq,halfDual_eq]
  have hJ := complementMatrix_square p
  calc
    complementMatrix p * (N.transpose*M.transpose) * complementMatrix p =
      complementMatrix p * N.transpose * (complementMatrix p*complementMatrix p) * M.transpose * complementMatrix p := by
        rw [hJ,mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

@[simp] theorem halfDual_involution {p : ℕ}
    (M : Matrix (State (2*p) p) (State (2*p) p) ℚ) : halfDual (halfDual M)=M := by
  ext S T
  simp [halfDual]

 theorem compound_transpose {n q : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    compound (q:=q) M.transpose=(compound M).transpose := by
  ext S T
  exact Matrix.permanent_transpose (M.submatrix T.track S.track)

/-- Transfer of one independent-layer cut, including the outgoing-state complement. -/
def layerTransfer {p : ℕ} (M : Matrix (Fin (2*p)) (Fin (2*p)) ℚ) :
    Matrix (State (2*p) p) (State (2*p) p) ℚ := compound M * complementMatrix p

 theorem layerTransfer_apply {p : ℕ} (M : Matrix (Fin (2*p)) (Fin (2*p)) ℚ)
    (S T : State (2*p) p) : layerTransfer M S T=compound M S T.halfComplement :=
  mul_complementMatrix _ S T

/-- A genuine pair of consecutive cut transfers. -/
def pairedTransfer {p : ℕ} (M H : Matrix (Fin (2*p)) (Fin (2*p)) ℚ) :=
  layerTransfer M * layerTransfer H

 theorem pairedTransfer_transpose {p : ℕ} (M H : Matrix (Fin (2*p)) (Fin (2*p)) ℚ) :
    pairedTransfer M H.transpose=compound M * halfDual (compound H) := by
  unfold pairedTransfer layerTransfer
  rw [compound_transpose,halfDual_eq]
  simp only [Matrix.mul_assoc]

/-- The unperturbed paired transfer W=A_U A_L. -/
def pairedBackground (p : ℕ) := pairedTransfer (upper (2*p)) (upper (2*p)).transpose

/-- Explicit inverse derived from the two concrete normalized background factors. -/
def pairedInverse (p : ℕ) := halfDual (upperInverse (2*p) p) * upperInverse (2*p) p

 theorem pairedInverse_mul (p : ℕ) : pairedInverse p * pairedBackground p=1 := by
  unfold pairedInverse pairedBackground
  rw [pairedTransfer_transpose]
  calc
    halfDual (upperInverse (2*p) p) * upperInverse (2*p) p *
        (compound (upper (2*p)) * halfDual (compound (upper (2*p)))) =
      halfDual (upperInverse (2*p) p) * (upperInverse (2*p) p*compound (upper (2*p))) *
        halfDual (compound (upper (2*p))) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [upperInverse_mul,mul_one,← halfDual_mul,mul_upperInverse,halfDual_one]

 theorem mul_pairedInverse (p : ℕ) : pairedBackground p * pairedInverse p=1 := by
  unfold pairedInverse pairedBackground
  rw [pairedTransfer_transpose]
  calc
    compound (upper (2*p)) * halfDual (compound (upper (2*p))) *
        (halfDual (upperInverse (2*p) p) * upperInverse (2*p) p) =
      compound (upper (2*p)) * (halfDual (compound (upper (2*p)))*halfDual (upperInverse (2*p) p)) *
        upperInverse (2*p) p := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [← halfDual_mul,upperInverse_mul,halfDual_one,mul_one,mul_upperInverse]

/-- First-side perturbations normalize to their literal permanental operation. -/
theorem paired_normalize_left {p : ℕ} (M : Matrix (Fin (2*p)) (Fin (2*p)) ℚ) :
    pairedTransfer M (upper (2*p)).transpose * pairedInverse p =
      compound M * upperInverse (2*p) p := by
  rw [pairedTransfer_transpose,pairedInverse]
  calc
    compound M * halfDual (compound (upper (2*p))) *
        (halfDual (upperInverse (2*p) p) * upperInverse (2*p) p) =
      compound M * (halfDual (compound (upper (2*p)))*halfDual (upperInverse (2*p) p)) *
        upperInverse (2*p) p := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← halfDual_mul,upperInverse_mul,halfDual_one,mul_one]

/-- Second-side perturbations normalize to the exact complementary transpose operation. -/
theorem paired_normalize_right {p : ℕ} (M : Matrix (Fin (2*p)) (Fin (2*p)) ℚ) :
    pairedInverse p * pairedTransfer (upper (2*p)) M.transpose =
      halfDual (compound M * upperInverse (2*p) p) := by
  rw [pairedTransfer_transpose,pairedInverse,halfDual_mul]
  calc
    halfDual (upperInverse (2*p) p) * upperInverse (2*p) p *
        (compound (upper (2*p)) * halfDual (compound M)) =
      halfDual (upperInverse (2*p) p) * (upperInverse (2*p) p*compound (upper (2*p))) *
        halfDual (compound M) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [upperInverse_mul,mul_one]

 theorem halfDual_rise (p : ℕ) (i : Fin (2*p-1)) : halfDual (rise (2*p) p i)=dualRise (2*p) p i := by
  ext S T
  change rise (2*p) p i (State.castParticles _ T.complement) (State.castParticles _ S.complement) = _
  rw [rise_castParticles]
  rfl

 theorem halfDual_drop (p : ℕ) (i : Fin (2*p-1)) : halfDual (drop (2*p) p i)=dualDrop (2*p) p i := by
  ext S T
  change drop (2*p) p i (State.castParticles _ T.complement) (State.castParticles _ S.complement) = _
  rw [drop_castParticles]
  rfl

end HiddenCircuits
