import HiddenCircuits.ProjectionRank
import Mathlib.Tactic

/-! Finite rank-complete encoding of an actual idempotent matrix. -/
namespace HiddenCircuits
variable {ι κ K : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Field K] [CharZero K]

lemma matrix_eq_zero_of_rank_zero (A : Matrix ι ι K) (h : A.rank=0) : A=0 := by
  have hr : Module.finrank K (LinearMap.range A.toLin')=0 := h
  have hz : LinearMap.range A.toLin'=⊥ := Submodule.finrank_eq_zero.mp hr
  have hf : A.toLin'=0 := LinearMap.range_eq_bot.mp hz
  apply Matrix.toLin'.injective
  simpa using hf

/-- A normalized d-dimensional retract exhausts an idempotent of rank d. -/
theorem projection_factorization (P : Matrix ι ι K) (L : Matrix ι κ K) (E : Matrix κ ι K)
    (hP : P*P=P) (hPL : P*L=L) (hEP : E*P=E) (hEL : E*L=1)
    (hrank : P.rank=Fintype.card κ) : L*E=P := by
  have hQ : (L*E)*(L*E)=L*E := by
    calc
      _ = L*(E*L)*E := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hEL,Matrix.mul_one]
  have hPQ : P*(L*E)=L*E := by rw [← Matrix.mul_assoc,hPL]
  have hQP : (L*E)*P=L*E := by rw [Matrix.mul_assoc,hEP]
  have hid : (P-L*E)*(P-L*E)=P-L*E := by
    rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,hP,hPQ,hQP,hQ]
    abel
  have ht : (P-L*E).trace=0 := by
    rw [Matrix.trace_sub,idempotent_matrix_trace_eq_rank P hP,hrank,
      Matrix.trace_mul_comm L E,hEL,Matrix.trace_one]
    simp
  have hz := matrix_eq_zero_of_rank_zero (P-L*E)
    (idempotent_matrix_rank_of_trace (P-L*E) hid 0 (by simpa using ht))
  exact (sub_eq_zero.mp hz).symm

/-- Raw code columns with CᵀPC=I give the complete projector factorization. -/
theorem projection_code_factorization (P : Matrix ι ι K) (C : Matrix ι κ K)
    (hP : P*P=P) (hC : C.transpose*P*C=1) (hrank : P.rank=Fintype.card κ) :
    (P*C)*(C.transpose*P)=P ∧ (C.transpose*P)*(P*C)=1 := by
  have hPL : P*(P*C)=P*C := by rw [← Matrix.mul_assoc,hP]
  have hEP : (C.transpose*P)*P=C.transpose*P := by rw [Matrix.mul_assoc,hP]
  have hEL : (C.transpose*P)*(P*C)=1 := by
    calc
      _ = C.transpose*(P*P)*C := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP]; exact hC
  exact ⟨projection_factorization P (P*C) (C.transpose*P) hP hPL hEP hEL hrank,hEL⟩

/-- The physical word includes a projection at every interface. -/
def projectedWord (P : Matrix ι ι K) : List (Matrix ι ι K) → Matrix ι ι K
  | [] => P
  | A::w => P*A*projectedWord P w

lemma projectedWord_left (P : Matrix ι ι K) (hP : P*P=P) (w : List (Matrix ι ι K)) :
    P*projectedWord P w=projectedWord P w := by
  cases w with
  | nil => exact hP
  | cons A w => simp only [projectedWord,← Matrix.mul_assoc,hP]

/-- Encoded multiplication composes exactly through the actual intermediate projector. -/
theorem encoded_word_composition (P : Matrix ι ι K) (L : Matrix ι κ K) (E : Matrix κ ι K)
    (hP : P*P=P) (hEP : E*P=E) (hEL : E*L=1) (hLE : L*E=P)
    (w : List (Matrix ι ι K)) :
    E*projectedWord P w*L=(w.map (fun A => E*A*L)).prod := by
  induction w with
  | nil => simpa only [projectedWord,List.map_nil,List.prod_nil,hEP] using hEL
  | cons A w ih =>
    simp only [projectedWord,List.map_cons,List.prod_cons]
    rw [← ih]
    calc
      E*(P*A*projectedWord P w)*L = E*A*projectedWord P w*L := by
        simp only [← Matrix.mul_assoc,hEP]
      _ = E*A*(P*projectedWord P w)*L := by rw [projectedWord_left P hP]
      _ = (E*A*L)*(E*projectedWord P w*L) := by rw [← hLE]; simp only [Matrix.mul_assoc]

end HiddenCircuits
