import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueRecoveryAlgebra
import HiddenCircuits.GraphReduction.Runtime.WordGraph.RecoveryRegisterBounds

/-! Fresh reconstruction: actual target graph sizes, answers and every integer
interpolation component have polynomial bit bounds in the original word bytes. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueRecovery
open Complexity BinaryArithmetic
open scoped BigOperators

def vertexBound (L : ℕ) : ℕ := 8*L*Recovery.heightBound L*(Recovery.heightBound L+2)
def termExponent (L : ℕ) : ℕ := (vertexBound L+1)^2+(Recovery.outerBound L)^2+2*(Recovery.innerBound L)^2+
  4*(Recovery.innerBound L)^2*(2*Recovery.heightBound L+1)+2

lemma query_size (mode : Bool) (w : WordInstance) (hw : w.word≠[]) (q : Recovery.Index w) :
    (query mode w q).1≤vertexBound (wordBits w).length := by
  have hh : 0<Recovery.height w q.1 := List.length_pos_iff.mpr (pairedQuery_nonempty w.word hw q.1.val)
  have hp : w.particles≤(wordBits w).length := by have := wordBits_length_lower w;omega
  have hH := (Recovery.parameter_bounds w q.1).2.1
  have hs : (query mode w q).1≤8*w.particles*Recovery.height w q.1*(Recovery.height w q.1+2) := by
    cases mode with
    | false =>
      change (unitEnumeration w.source w.target (2*q.2.val)).labels.length≤_
      rw [Enumeration.length_eq_card]
      exact (unitIntervalProbe_query_size hh w.source w.target q.2).trans (by gcongr;norm_num)
    | true =>
      change (privateEnumeration w.source w.target (2*q.2.val)).labels.length≤_
      rw [Enumeration.length_eq_card]
      exact (PrivateProbe.sampleQuery_size_bound hh w.source w.target q.2).trans (by gcongr;omega)
  apply hs.trans
  unfold vertexBound
  gcongr
lemma query_answer_bound (mode : Bool) (w : WordInstance) (hw : w.word≠[]) (q : Recovery.Index w) :
    (perfectMatchingCount (query mode w q).2.graph:ℤ).natAbs≤2^((vertexBound (wordBits w).length+1)^2) := by
  simp only [Int.natAbs_natCast]
  have h := perfectMatchingCount_bound (query mode w q).2.graph
  simp only [Fintype.card_fin] at h
  have hn := query_size mode w hw q
  calc
    _≤((query mode w q).1+1)^(query mode w q).1 := h
    _≤(2^((query mode w q).1))^((query mode w q).1) := Nat.pow_le_pow_left (succ_le_two_pow _) _
    _=2^((query mode w q).1^2) := by rw [←pow_mul,pow_two]
    _≤_ := Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left (by omega) 2)
lemma even_weights_envelope {d D : ℕ} (i : Fin (d+1)) (h : d≤D) :
    (EvenWeights.numerator d i).natAbs≤2^(2*D^2+1) ∧ (EvenWeights.denominator d i).natAbs≤2^(2*D^2+1) := by
  have hpow : 2^(2*d^2+1)≤2^(2*D^2+1) := Nat.pow_le_pow_right (by decide) (by gcongr)
  exact ⟨(EvenWeights.envelope d i).1.trans hpow,(EvenWeights.envelope d i).2.trans hpow⟩
lemma oddFactorial_envelope (s : ℕ) : oddFactorial s≤2^(4*s^2) := by
  have hf : oddFactorial s≤(2*s).factorial := by
    rw [factorial_even_split]
    have h : 1≤2^s*s.factorial := Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero _ (by decide)) (Nat.factorial_ne_zero _))
    nlinarith
  have hb := hf.trans (factorial_le_two_pow_square (2*s))
  convert hb using 1 <;> ring
lemma normalization_envelope (mode : Bool) (w : WordInstance) (q : Recovery.Index w) :
    ((oddFactorial q.2.val:ℤ)^normalizationExponent mode (Recovery.height w q.1)).natAbs≤
      2^(4*(Recovery.innerBound (wordBits w).length)^2*(2*Recovery.heightBound (wordBits w).length+1)) := by
  have hE := (Recovery.parameter_bounds w q.1).2.2
  have hH := (Recovery.parameter_bounds w q.1).2.1
  have hs : q.2.val≤Recovery.innerBound (wordBits w).length := by have := q.2.isLt;omega
  have he : normalizationExponent mode (Recovery.height w q.1)≤2*Recovery.heightBound (wordBits w).length+1 := by
    cases mode with
    | false => change Recovery.height w q.1+1≤2*Recovery.heightBound (wordBits w).length+1;omega
    | true => change 2*Recovery.height w q.1+1≤2*Recovery.heightBound (wordBits w).length+1;omega
  have hf := (oddFactorial_envelope q.2.val).trans
    (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hs 2)))
  simp only [Int.natAbs_pow,Int.natAbs_natCast]
  calc
    _≤(2^(4*(Recovery.innerBound (wordBits w).length)^2))^normalizationExponent mode (Recovery.height w q.1) := Nat.pow_le_pow_left hf _
    _=2^(4*(Recovery.innerBound (wordBits w).length)^2*normalizationExponent mode (Recovery.height w q.1)) := (pow_mul _ _ _).symm
    _≤_ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ he)
lemma ratio_bound (mode : Bool) (w : WordInstance) (hw : w.word≠[]) (q : Recovery.Index w) :
    (ratio mode w q (perfectMatchingCount (query mode w q).2.graph)).1.natAbs≤2^(termExponent (wordBits w).length) ∧
      (ratio mode w q (perfectMatchingCount (query mode w q).2.graph)).2.natAbs≤2^(termExponent (wordBits w).length) := by
  have ho := Recovery.weights_envelope q.1 (Recovery.parameter_bounds w q.1).1
  have hi := even_weights_envelope q.2 (Recovery.parameter_bounds w q.1).2.2
  have hn := normalization_envelope mode w q
  have ha := query_answer_bound mode w hw q
  constructor
  · have hh := Nat.mul_le_mul (Nat.mul_le_mul ha ho.1) hi.1
    simp only [←pow_add] at hh
    simp only [ratio,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_neg,Int.natAbs_one,one_pow,one_mul]
    apply hh.trans
    apply Nat.pow_le_pow_right (by decide)
    unfold termExponent
    omega
  · have hh := Nat.mul_le_mul (Nat.mul_le_mul ho.2 hi.2) hn
    simp only [←pow_add] at hh
    simp only [ratio,Int.natAbs_mul]
    apply hh.trans
    apply Nat.pow_le_pow_right (by decide)
    unfold termExponent
    omega

theorem ratio_registers_bounded (mode : Bool) (w : WordInstance) (hw : w.word≠[]) (q : Recovery.Index w) :
    RegisterMachine.Bounded (termExponent (wordBits w).length+2)
      (RatioCombine.registers ((-1:ℤ)^(signExponent mode w.particles (Recovery.height w q.1)))
        (perfectMatchingCount (query mode w q).2.graph:ℤ)
        (interpolationNegativeNumerator (Recovery.degree w) q.1)
        (EvenWeights.numerator (Recovery.innerDegree w q.1) q.2)
        (interpolationDenominator (Recovery.degree w) q.1)
        (EvenWeights.denominator (Recovery.innerDegree w q.1) q.2)
        ((oddFactorial q.2.val:ℤ)^normalizationExponent mode (Recovery.height w q.1))) := by
  let L := (wordBits w).length
  have ho := Recovery.weights_envelope q.1 (Recovery.parameter_bounds w q.1).1
  have hi := even_weights_envelope q.2 (Recovery.parameter_bounds w q.1).2.2
  have hn := normalization_envelope mode w q
  have ha := query_answer_bound mode w hw q
  have hE : 2*(Recovery.innerBound L)^2+1 ≤ termExponent L := by unfold termExponent;omega
  have hD : (Recovery.outerBound L)^2+1 ≤ termExponent L := by unfold termExponent;omega
  have hA : (vertexBound L+1)^2 ≤ termExponent L := by unfold termExponent;omega
  have hN : 4*(Recovery.innerBound L)^2*(2*Recovery.heightBound L+1) ≤ termExponent L := by unfold termExponent;omega
  have hsign : ((-1:ℤ)^(signExponent mode w.particles (Recovery.height w q.1))).natAbs ≤ 2^(termExponent L) := by
    simp only [Int.natAbs_pow,Int.natAbs_neg,Int.natAbs_one,one_pow]
    exact Nat.one_le_pow _ _ (by decide)
  have hnb := hn.trans (Nat.pow_le_pow_right (by decide) hN)
  have hab := ha.trans (Nat.pow_le_pow_right (by decide) hA)
  have hnt := ho.1.trans (Nat.pow_le_pow_right (by decide) hD)
  have hdt := ho.2.trans (Nat.pow_le_pow_right (by decide) hD)
  have hns := hi.1.trans (Nat.pow_le_pow_right (by decide) hE)
  have hds := hi.2.trans (Nat.pow_le_pow_right (by decide) hE)
  intro i
  apply signedBits_length_of_abs_bound
  fin_cases i <;> dsimp only [RatioCombine.registers]
  · exact hsign
  · exact hab
  · exact hnt
  · exact hns
  · exact hdt
  · exact hds
  · exact hnb
end HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueRecovery
