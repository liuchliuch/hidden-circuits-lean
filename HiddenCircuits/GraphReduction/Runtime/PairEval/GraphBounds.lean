import HiddenCircuits.GraphReduction.Runtime.PairEval.GraphRecovery

/-! Closed input-byte polynomials for all arbitrary-pair query vertices,
answers, integer interpolation registers and rational accumulator prefixes. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.GraphBounds
open Complexity BinaryArithmetic Polynomial WordGraph GraphRecovery

noncomputable def degreeP : Polynomial ℕ := 2*X^2
noncomputable def vertexP : Polynomial ℕ := 8*X*X*(X+2)
noncomputable def answerP : Polynomial ℕ := (vertexP+1)^2+2
noncomputable def termP : Polynomial ℕ := (vertexP+1)^2+2*degreeP^2+4*degreeP^2*(2*X+1)+2
noncomputable def componentP : Polynomial ℕ := termP+2
noncomputable def accumulatorP : Polynomial ℕ := 1+(termP+1)*(degreeP+1)+termP+2

def vertexBound (L : ℕ) : ℕ := 8*L*L*(L+2)
def termExponent (L : ℕ) : ℕ := (vertexBound L+1)^2+2*(2*L^2)^2+4*(2*L^2)^2*(2*L+1)+2
@[simp] lemma degreeP_eval (L : ℕ) : degreeP.eval L=2*L^2 := by simp [degreeP]
@[simp] lemma vertexP_eval (L : ℕ) : vertexP.eval L=vertexBound L := by simp [vertexP,vertexBound]
@[simp] lemma answerP_eval (L : ℕ) : answerP.eval L=(vertexBound L+1)^2+2 := by simp [answerP]
@[simp] lemma termP_eval (L : ℕ) : termP.eval L=termExponent L := by simp [termP,termExponent]
@[simp] lemma componentP_eval (L : ℕ) : componentP.eval L=termExponent L+2 := by simp [componentP]
@[simp] lemma accumulatorP_eval (L : ℕ) : accumulatorP.eval L=1+(termExponent L+1)*(2*L^2+1)+termExponent L+2 := by simp [accumulatorP]

lemma parameter_bounds (w : PairInput) : w.particles≤(pairInputBits w).length ∧
    w.pairs.length≤(pairInputBits w).length ∧ degree w≤degreeP.eval (pairInputBits w).length := by
  have hi:=pairInputBits_length_lower w
  have hp:w.particles≤(pairInputBits w).length:=by omega
  have hh:w.pairs.length≤(pairInputBits w).length:=by omega
  refine ⟨hp,hh,?_⟩
  rw [degreeP_eval]
  unfold GraphRecovery.degree
  nlinarith [Nat.mul_le_mul hp hh]
lemma index_bound (w : PairInput) (s : Index w) : s.val≤degreeP.eval (pairInputBits w).length := by
  have h:=(parameter_bounds w).2.2
  have hs:=s.isLt
  omega
lemma query_size (kind : Kind) (w : PairInput) (s : Index w) :
    (query kind w s).1≤vertexP.eval (pairInputBits w).length := by
  have hh:0<w.pairs.length:=List.length_pos_iff.mpr w.nonempty
  have hbound:(query kind w s).1≤8*w.particles*w.pairs.length*(w.pairs.length+2) := by
    cases kind with
    | none =>
      change (monotoneEnumeration w.source w.target s.val).labels.length≤_
      rw [Enumeration.length_eq_card]
      exact (monotoneProbe_query_size hh w.source w.target s).trans (by gcongr <;> omega)
    | some b =>
      cases b with
      | false =>
        change (unitEnumeration w.source w.target (2*s.val)).labels.length≤_
        rw [Enumeration.length_eq_card]
        exact (unitIntervalProbe_query_size hh w.source w.target s).trans (by gcongr <;> norm_num)
      | true =>
        change (privateEnumeration w.source w.target (2*s.val)).labels.length≤_
        rw [Enumeration.length_eq_card]
        exact (PrivateProbe.sampleQuery_size_bound hh w.source w.target s).trans (by gcongr <;> omega)
  apply hbound.trans
  rw [vertexP_eval]
  unfold vertexBound
  have hp:=(parameter_bounds w).1
  have hn:=(parameter_bounds w).2.1
  gcongr
lemma query_answer_bound (kind : Kind) (w : PairInput) (s : Index w) :
    (perfectMatchingCount (query kind w s).2.graph:ℤ).natAbs≤2^((vertexBound (pairInputBits w).length+1)^2) := by
  simp only [Int.natAbs_natCast]
  have h:=perfectMatchingCount_bound (query kind w s).2.graph
  simp only [Fintype.card_fin] at h
  have hn:=query_size kind w s
  rw [vertexP_eval] at hn
  calc
    _≤((query kind w s).1+1)^(query kind w s).1:=h
    _≤(2^((query kind w s).1))^((query kind w s).1):=Nat.pow_le_pow_left (succ_le_two_pow _) _
    _=2^((query kind w s).1^2):=by rw [←pow_mul,pow_two]
    _≤_:=Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left (by omega) 2)
lemma query_answer_length (kind : Kind) (w : PairInput) (s : Index w) :
    (signedBits (perfectMatchingCount (query kind w s).2.graph:ℤ)).length≤answerP.eval (pairInputBits w).length := by
  rw [answerP_eval]
  exact signedBits_length_of_abs_bound (query_answer_bound kind w s)

lemma weights_envelope (kind : Kind) (w : PairInput) (s : Index w) :
    (numerator kind w s).natAbs≤2^(2*(2*(pairInputBits w).length^2)^2+1) ∧
    (denominator kind w s).natAbs≤2^(2*(2*(pairInputBits w).length^2)^2+1) := by
  have hd:degree w≤2*(pairInputBits w).length^2:=by simpa using (parameter_bounds w).2.2
  cases kind with
  | none =>
    have h:=Recovery.weights_envelope s hd
    have he:(2*(pairInputBits w).length^2)^2+1≤2*(2*(pairInputBits w).length^2)^2+1:=by omega
    exact ⟨h.1.trans (Nat.pow_le_pow_right (by decide) he),h.2.trans (Nat.pow_le_pow_right (by decide) he)⟩
  | some b => exact CliqueRecovery.even_weights_envelope s hd

lemma normalization_envelope (kind : Kind) (w : PairInput) (s : Index w) :
    (normalization kind w s).natAbs≤2^(4*(2*(pairInputBits w).length^2)^2*(2*(pairInputBits w).length+1)) := by
  let L:=(pairInputBits w).length
  let D:=2*L^2
  have hs:s.val≤D:=by simpa [D,L] using index_bound w s
  have hh:w.pairs.length≤L:=(parameter_bounds w).2.1
  have hf:s.val.factorial≤2^(4*D^2):=(factorial_le_two_pow_square s.val).trans
    (Nat.pow_le_pow_right (by decide) (by nlinarith [Nat.pow_le_pow_left hs 2]))
  have ho:oddFactorial s.val≤2^(4*D^2):=(CliqueRecovery.oddFactorial_envelope s.val).trans
    (Nat.pow_le_pow_right (by decide) (by gcongr))
  have hp (base ex : ℕ) (hb:base≤2^(4*D^2)) (he:ex≤2*L+1) :
      ((base:ℤ)^ex).natAbs≤2^(4*D^2*(2*L+1)) := by
    simp only [Int.natAbs_pow,Int.natAbs_natCast]
    calc
      _≤(2^(4*D^2))^ex:=Nat.pow_le_pow_left hb _
      _=2^(4*D^2*ex):=(pow_mul _ _ _).symm
      _≤_:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ he)
  cases kind with
  | none => exact hp _ _ hf (by omega)
  | some b => cases b <;> exact hp _ _ ho (by omega)
lemma sign_abs (kind : Kind) (w : PairInput) : (sign kind w).natAbs=1 := by
  cases kind with
  | none => simp [sign,Int.natAbs_pow]
  | some b => cases b <;> simp [sign,Int.natAbs_pow]
lemma ratio_bound (kind : Kind) (w : PairInput) (s : Index w) :
    (term kind w s).1.natAbs≤2^(termExponent (pairInputBits w).length) ∧
    (term kind w s).2.natAbs≤2^(termExponent (pairInputBits w).length) := by
  have hw:=weights_envelope kind w s
  have hn:=normalization_envelope kind w s
  have ha:=query_answer_bound kind w s
  constructor
  · have h:=Nat.mul_le_mul ha hw.1
    simp only [←pow_add] at h
    simp only [term,ratio,Int.natAbs_mul,sign_abs,one_mul]
    exact h.trans (Nat.pow_le_pow_right (by decide) (by unfold termExponent;omega))
  · have h:=Nat.mul_le_mul hw.2 hn
    simp only [←pow_add] at h
    simp only [term,ratio,Int.natAbs_mul]
    exact h.trans (Nat.pow_le_pow_right (by decide) (by unfold termExponent;omega))
lemma ratio_length (kind : Kind) (w : PairInput) (s : Index w) :
    (signedBits (term kind w s).1).length≤componentP.eval (pairInputBits w).length ∧
    (signedBits (term kind w s).2).length≤componentP.eval (pairInputBits w).length := by
  rw [componentP_eval]
  exact ⟨signedBits_length_of_abs_bound (ratio_bound kind w s).1,signedBits_length_of_abs_bound (ratio_bound kind w s).2⟩
lemma registers_bounded (kind : Kind) (w : PairInput) (s : Index w) :
    RegisterMachine.Bounded (componentP.eval (pairInputBits w).length)
      (RatioCombine.registers (sign kind w) (perfectMatchingCount (query kind w s).2.graph:ℤ)
        1 (numerator kind w s) 1 (denominator kind w s) (normalization kind w s)) := by
  let L:=(pairInputBits w).length
  have hw:=weights_envelope kind w s
  have hn:=normalization_envelope kind w s
  have ha:=query_answer_bound kind w s
  have hA:(vertexBound L+1)^2≤termExponent L:=by unfold termExponent;omega
  have hW:2*(2*L^2)^2+1≤termExponent L:=by unfold termExponent;omega
  have hN:4*(2*L^2)^2*(2*L+1)≤termExponent L:=by unfold termExponent;omega
  have hs:(sign kind w).natAbs≤2^(termExponent L):=by rw [sign_abs];exact Nat.one_le_pow _ _ (by decide)
  have hone:(1:ℤ).natAbs≤2^(termExponent L):=Nat.one_le_pow _ _ (by decide)
  have ha':=ha.trans (Nat.pow_le_pow_right (by decide) hA)
  have hu':=hw.1.trans (Nat.pow_le_pow_right (by decide) hW)
  have hd':=hw.2.trans (Nat.pow_le_pow_right (by decide) hW)
  have hn':=hn.trans (Nat.pow_le_pow_right (by decide) hN)
  intro i
  rw [componentP_eval]
  apply signedBits_length_of_abs_bound
  fin_cases i <;> dsimp only [RatioCombine.registers]
  · exact hs
  · exact ha'
  · exact hone
  · exact hu'
  · exact hone
  · exact hd'
  · exact hn'
lemma initialBitBound (kind : Kind) (w : PairInput) :
    RationalAccumulator.BitBound (accumulatorP.eval (pairInputBits w).length) (0,1) (terms kind w) := by
  have h:=RationalAccumulator.bitBound_of_abs (0,1) (terms kind w) 1 (termExponent (pairInputBits w).length)
    (by constructor <;> decide) (by
      intro b hb
      obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hb
      exact ratio_bound kind w s)
  apply h.mono
  rw [accumulatorP_eval,terms_length]
  have hd:degree w≤2*(pairInputBits w).length^2:=by simpa using (parameter_bounds w).2.2
  nlinarith
end HiddenCircuits.GraphReduction.Runtime.PairEval.GraphBounds
