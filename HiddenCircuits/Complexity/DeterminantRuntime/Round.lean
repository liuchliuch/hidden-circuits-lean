import HiddenCircuits.Complexity.DeterminantRuntime.RoundStages
import HiddenCircuits.Complexity.DeterminantRuntime.RoundCleanup
import HiddenCircuits.Complexity.DeterminantRuntime.RoundBounds
import HiddenCircuits.Complexity.DeterminantRuntime.ScalarDiagonal

/-! One literal Faddeev–LeVerrier round, with all mathematical obligations and
storage assumptions discharged for every prefix of the original input. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.Round
open OracleBlock BinaryArithmetic Polynomial
variable {n : ℕ}

noncomputable def scalarStage : OracleBlock 30 := ScalarDiagonal.on scalarPorts
noncomputable def program : OracleBlock 30 := seq productStage
  (seq traceStage (seq coefficientStage (seq scalarStage cleanup)))

theorem scalarStage_executes (g : BitString → ℕ) (C : Matrix (Fin n) (Fin n) ℤ)
    (a b c trace : BitString) (k clock : ℕ) (next : ℤ) :
    ∃ t, scalarStage.Executes g
      (state n a b c k clock (encodeBitList (matrixWords C)) trace (signedBits next) [])
      (state n a b c k clock (encodeBitList (matrixWords C)) trace (signedBits next)
        (encodeBitList (matrixWords (C+Matrix.scalar (Fin n) next)))) t ∧
      t ≤ ScalarDiagonal.time.eval (n+(encodeBitList (matrixWords C)).length+(signedBits next).length+1) := by
  obtain ⟨t,ht,hb⟩ := ScalarDiagonal.on_executes scalarPorts g C next
    (state n a b c k clock (encodeBitList (matrixWords C)) trace (signedBits next) [])
    (by funext q; fin_cases q <;> rfl)
  have he : Function.update (state n a b c k clock (encodeBitList (matrixWords C)) trace (signedBits next) [])
      (scalarPorts 7) (encodeBitList (matrixWords (C+Matrix.scalar (Fin n) next))) =
      state n a b c k clock (encodeBitList (matrixWords C)) trace (signedBits next)
        (encodeBitList (matrixWords (C+Matrix.scalar (Fin n) next))) := by
    funext q; fin_cases q <;> rfl
  rw [he] at ht
  exact ⟨t,ht,hb⟩

noncomputable def timePolynomial : Polynomial ℕ :=
  MatrixProduct.timePolynomial.comp (3*X+1)+Trace.timePolynomial.comp (2*X+1)+
  Coefficient.timePolynomial.comp (2*X+1)+ScalarDiagonal.time.comp (3*X+1)+16*X+32

theorem executes (g : BitString → ℕ) (A B : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) (k clock N : ℕ)
    (hdiv : ((k+1 : ℕ) : ℤ) ∣ -(A*B).trace)
    (hbounds : n ≤ N ∧ k ≤ N ∧
      (encodeBitList (matrixWords A)).length ≤ N ∧ (encodeBitList (matrixWords B)).length ≤ N ∧
      (signedBits c).length ≤ N ∧ (encodeBitList (matrixWords (A*B))).length ≤ N ∧
      (signedBits (A*B).trace).length ≤ N ∧ (signedBits (nextCoefficient A B k)).length ≤ N ∧
      (encodeBitList (matrixWords (A*B+Matrix.scalar (Fin n) (nextCoefficient A B k)))).length ≤ N) :
    ∃ t, program.Executes g (store n (encodeBitList (matrixWords A)) (encodeBitList (matrixWords B)) (signedBits c) k clock)
      (store n (encodeBitList (matrixWords A))
        (encodeBitList (matrixWords (A*B+Matrix.scalar (Fin n) (nextCoefficient A B k))))
        (signedBits (nextCoefficient A B k)) k clock) t ∧ t ≤ timePolynomial.eval N := by
  obtain ⟨p,hp,hpb⟩ := productStage_executes g A B (signedBits c) k clock
  obtain ⟨r,hr,hrb⟩ := traceStage_executes g (A*B) (encodeBitList (matrixWords A))
    (encodeBitList (matrixWords B)) (signedBits c) k clock
  obtain ⟨d,hd,hdb⟩ := coefficientStage_executes g n (encodeBitList (matrixWords A))
    (encodeBitList (matrixWords B)) (signedBits c) (encodeBitList (matrixWords (A*B))) k clock (A*B).trace hdiv
  obtain ⟨s,hs,hsb⟩ := scalarStage_executes g (A*B) (encodeBitList (matrixWords A))
    (encodeBitList (matrixWords B)) (signedBits c) (signedBits (A*B).trace) k clock (nextCoefficient A B k)
  have hf := cleanup_executes g n (encodeBitList (matrixWords A)) (encodeBitList (matrixWords B)) (signedBits c)
    k clock (encodeBitList (matrixWords (A*B))) (signedBits (A*B).trace) (signedBits (nextCoefficient A B k))
    (encodeBitList (matrixWords (A*B+Matrix.scalar (Fin n) (nextCoefficient A B k))))
  have h := seq_executes _ _ g hp (seq_executes _ _ g hr (seq_executes _ _ g hd (seq_executes _ _ g hs hf)))
  refine ⟨_,h,?_⟩
  obtain ⟨hn,hk,hA,hB,hc,hP,htr,hnc,hnm⟩ := hbounds
  have hm1 := polynomial_nat_eval_mono MatrixProduct.timePolynomial
    (show MatrixProduct.inputSize A B ≤ 3*N+1 by unfold MatrixProduct.inputSize;omega)
  have hm2 := polynomial_nat_eval_mono Trace.timePolynomial
    (show n+(encodeBitList (matrixWords (A*B))).length+1 ≤ 2*N+1 by omega)
  have hm3 := polynomial_nat_eval_mono Coefficient.timePolynomial
    (show k+(signedBits (A*B).trace).length+1 ≤ 2*N+1 by omega)
  have hm4 := polynomial_nat_eval_mono ScalarDiagonal.time
    (show n+(encodeBitList (matrixWords (A*B))).length+(signedBits (nextCoefficient A B k)).length+1 ≤ 3*N+1 by omega)
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  dsimp only at hm1 hm2 hm3 hm4
  omega

/-- Canonical round theorem: all divisor and bit-size conditions come from A. -/
theorem prefix_executes (g : BitString → ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (k clock : ℕ) (hk : k < n) :
    ∃ t, program.Executes g
      (store n (encodeBitList (matrixWords A)) (encodeBitList (matrixWords (faddeevState A k).1))
        (signedBits (faddeevState A k).2) k clock)
      (store n (encodeBitList (matrixWords A)) (encodeBitList (matrixWords (faddeevState A (k+1)).1))
        (signedBits (faddeevState A (k+1)).2) k clock) t ∧
      t ≤ timePolynomial.eval (roundSizeBound A) := by
  have hbounds := prefix_round_bounds A k hk
  have hdiv := faddeevState_divisible A k hk
  simpa only [faddeevState,faddeevStep] using
    executes g A (faddeevState A k).1 (faddeevState A k).2 k clock (roundSizeBound A) hdiv
      (by simpa only [faddeevState,faddeevStep] using hbounds)

theorem queryFree : program.QueryFree := seq_queryFree _ _ (MatrixProduct.on_queryFree _)
  (seq_queryFree _ _ (Trace.on_queryFree _) (seq_queryFree _ _ (Coefficient.on_queryFree _)
    (seq_queryFree _ _ (ScalarDiagonal.on_queryFree _) cleanup_queryFree)))

end HiddenCircuits.Complexity.DeterminantRuntime.Round
