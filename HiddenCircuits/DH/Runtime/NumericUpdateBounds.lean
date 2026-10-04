import HiddenCircuits.DH.Runtime.NumericUpdatePorts

/-! One graph-size polynomial bounds every public
source word, and operational stack growth bounds the newly generated row. -/
namespace HiddenCircuits.DH.Runtime.NumericUpdate
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic NumericStateModel NumericEncoding Polynomial

lemma base_bounds {n : ℕ} (s : NumericStateModel.State n) (h : Safe s) :
    n+1≤ basePolynomial.eval n ∧ (PairCheck.liveBits s.alive).length≤ basePolynomial.eval n ∧
      (sizeBits s).length≤ basePolynomial.eval n ∧ (tableBits s).length≤ basePolynomial.eval n ∧
      ∀v:Fin n,(rowBits s.rows[v.val]).length≤ basePolynomial.eval n := by
  have hL:=live_length s.alive
  have hS:=safe_sizes_bound h
  have hT:=safe_table_bound h
  have hR:=safe_row_bound h
  simp only [basePolynomial,eval_mul,eval_pow,eval_add,eval_X,eval_ofNat,eval_one]
  simp only [sizesBound,tableBound,rowBound] at hS hT hR
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals try nlinarith [Nat.zero_le (n^4),Nat.zero_le (n^3),Nat.zero_le (n^2)]
  intro v
  have hh:=hR v
  nlinarith [Nat.zero_le (n^4),Nat.zero_le (n^3),Nat.zero_le (n^2)]
lemma envelope_base (n : ℕ) : basePolynomial.eval n+1≤ envelope.eval n:=by
  simp only [envelope,eval_add,eval_one];omega
lemma envelope_rowTime (n : ℕ) : basePolynomial.eval n+CoefficientRowRuntime.time.eval (3*basePolynomial.eval n)+1=envelope.eval n:=by
  simp [envelope]
lemma lookup_bound (L j D : ℕ) (hL:L≤ D) (hj:j≤ D) (hD:1≤ D) :
    GraphReduction.Runtime.lookupBound L j≤ 400*D^2:=by
  unfold GraphReduction.Runtime.lookupBound
  have hh:(j+1)*(6*L+14)≤(D+1)*(6*D+14):=Nat.mul_le_mul (by omega) (by omega)
  nlinarith
lemma update_bound (L j W E : ℕ) (hL:L≤ E) (hj:j≤ E) (hW:W≤ 2*E) (hE:1≤ E) :
    WordArray.updateBound L j W≤ 2500*E^2:=by
  apply (WordArray.updateBound_polynomial _ _ _).trans
  have hx:L+j+W+1≤ 5*E:=by omega
  have hh:=Nat.pow_le_pow_left hx 2
  nlinarith
end HiddenCircuits.DH.Runtime.NumericUpdate
