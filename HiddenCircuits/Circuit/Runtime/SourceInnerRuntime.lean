import HiddenCircuits.Circuit.Runtime.SourceInnerLoop
import HiddenCircuits.Circuit.Runtime.SourceQueryStorage

/-! Discharge the geometric-loop storage premises with the
actual query/accumulator bit bounds, yielding an unconditional polynomial charge. -/
namespace HiddenCircuits.Circuit.Runtime.SourceInner
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial SourceQueryRecovery

noncomputable def time (p : Polynomial ℕ) : Polynomial ℕ :=
  (SourceQueryBounds.degreeSize+1)*((SourceSample.time p).comp SourceQueryStorage.boundedStorageSize+5)+6*SourceQueryBounds.degreeSize+12

theorem program_executes_polynomial {k : ℕ} (W : OracleBlock k) (g : BitString → ℕ) (p : Polynomial ℕ)
    (hW : SourceWordCall.WordSolverSpec W g p) {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (acc : RationalAccumulator.Ratio) (tail : List RationalAccumulator.Ratio) (C : ℕ)
    (hbit : RationalAccumulator.BitBound C acc (SourceSampleIntegers.rowItems hn a w r s++tail)) :
    ∃c,(program W).Executes g (state (k:=k) w a r s 0 acc)
      (state (k:=k) w a r s 0 (RationalAccumulator.run acc (SourceSampleIntegers.rowItems hn a w r s))) c ∧
      c≤(time p).eval ((circuitBits n w).length+a+C) ∧
      RationalAccumulator.BitBound C (RationalAccumulator.run acc (SourceSampleIntegers.rowItems hn a w r s)) tail := by
  obtain ⟨c,hc,hb,hv⟩:=program_executes W g p hW hn a w r s acc tail C
    (SourceQueryStorage.boundedStorageSize.eval ((circuitBits n w).length+a+C)) hbit
    (fun u acc ha=>SourceQueryStorage.polynomial_state_bound w a C r s u acc ha)
  refine ⟨c,hc,?_,hv⟩
  have hd:=(SourceQueryBounds.degree_bound w a r s).trans
    (polynomial_nat_eval_mono SourceQueryBounds.degreeSize (Nat.le_add_right ((circuitBits n w).length+a) C))
  dsimp only at hd
  have hm:=Nat.mul_le_mul_right ((SourceSample.time p).eval (SourceQueryStorage.boundedStorageSize.eval ((circuitBits n w).length+a+C))+5)
    (Nat.add_le_add_right hd 1)
  simp only [time,eval_add,eval_mul,eval_comp,eval_ofNat,eval_one]
  omega
end HiddenCircuits.Circuit.Runtime.SourceInner
