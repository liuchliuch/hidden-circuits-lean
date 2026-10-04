import HiddenCircuits.GraphReduction.Runtime.WordGraph.RecoveryAlgebra
import HiddenCircuits.Complexity.RecoveryBitBounds

/-! Fresh reconstruction: explicit polynomial size and integer magnitude bounds
for every actual monotone graph query and interpolation ratio. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Recovery
open Complexity BinaryArithmetic
open scoped BigOperators

def outerBound (L : ℕ) : ℕ := L^3
def heightBound (L : ℕ) : ℕ := L*(outerBound L+1)
def innerBound (L : ℕ) : ℕ := 2*L*heightBound L
def vertexBound (L : ℕ) : ℕ := 4*L*heightBound L*(heightBound L+1)
def queryCountBound (L : ℕ) : ℕ := (outerBound L+1)*(innerBound L+1)
def termExponent (L : ℕ) : ℕ := (vertexBound L+1)^2+(outerBound L)^2+(innerBound L)^2+
  (innerBound L)^2*heightBound L+2

lemma parameter_bounds (w : WordInstance) (t : Fin (degree w+1)) :
    degree w ≤ outerBound (wordBits w).length ∧ height w t ≤ heightBound (wordBits w).length ∧
      innerDegree w t ≤ innerBound (wordBits w).length := by
  let L := (wordBits w).length
  have hin := wordBits_length_lower w
  have hp : w.particles ≤ L := by dsimp [L];omega
  have hw : w.word.length ≤ L := by dsimp [L];omega
  have hd : degree w ≤ outerBound L := by
    unfold degree outerBound
    have hh := Nat.mul_le_mul hw (Nat.pow_le_pow_left hp 2)
    nlinarith
  have ht : t.val+1 ≤ outerBound L+1 := by have := t.isLt;omega
  have hh : height w t ≤ heightBound L := by
    simp only [height,sampleWord_length,heightBound]
    exact Nat.mul_le_mul hw ht
  exact ⟨hd,hh,Nat.mul_le_mul (Nat.mul_le_mul_left 2 hp) hh⟩

lemma query_size (w : WordInstance) (hw : w.word≠[]) (q : Index w) :
    (query w q).1 ≤ vertexBound (wordBits w).length := by
  have hh : 0<height w q.1 := List.length_pos_iff.mpr (pairedQuery_nonempty w.word hw q.1.val)
  have hsize : (query w q).1 ≤ 4*w.particles*height w q.1*(height w q.1+1) := by
    change (monotoneEnumeration w.source w.target q.2.val).labels.length ≤ _
    rw [Enumeration.length_eq_card]
    exact monotoneProbe_query_size hh w.source w.target q.2
  apply hsize.trans
  have hp : w.particles ≤ (wordBits w).length := by have := wordBits_length_lower w;omega
  have hH := (parameter_bounds w q.1).2.1
  unfold vertexBound
  gcongr

lemma query_answer_bound (w : WordInstance) (hw : w.word≠[]) (q : Index w) :
    (perfectMatchingCount (query w q).2.graph:ℤ).natAbs ≤ 2^((vertexBound (wordBits w).length+1)^2) := by
  simp only [Int.natAbs_natCast]
  have h := perfectMatchingCount_bound (query w q).2.graph
  simp only [Fintype.card_fin] at h
  have hn := query_size w hw q
  calc
    _ ≤ ((query w q).1+1)^(query w q).1 := h
    _ ≤ (2^((query w q).1))^((query w q).1) :=
      Nat.pow_le_pow_left (succ_le_two_pow _) _
    _=2^((query w q).1^2) := by rw [←pow_mul,pow_two]
    _ ≤ 2^((vertexBound (wordBits w).length+1)^2) :=
      Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left (by omega) 2)

lemma terms_length_bound (w : WordInstance) : (terms w).length ≤ queryCountBound (wordBits w).length := by
  simp only [terms,List.length_map,indices,List.sigma,List.length_flatMap,List.map_map,Function.comp_def,List.length_map,List.length_finRange]
  change ((List.finRange (degree w+1)).map (fun t => innerDegree w t+1)).sum ≤ _
  rw [←Fin.sum_univ_def]
  calc
    _ ≤ ∑ _t : Fin (degree w+1), (innerBound (wordBits w).length+1) :=
      Finset.sum_le_sum (fun t _ => by have := (parameter_bounds w t).2.2;omega)
    _=(degree w+1)*(innerBound (wordBits w).length+1) := by simp
    _ ≤ queryCountBound (wordBits w).length := Nat.mul_le_mul_right _ (by
      have := (parameter_bounds w ⟨0,by omega⟩).1;omega)
lemma weights_envelope {d D : ℕ} (i : Fin (d+1)) (h : d ≤ D) :
    (interpolationNegativeNumerator d i).natAbs ≤ 2^(D^2+1) ∧
      (interpolationDenominator d i).natAbs ≤ 2^(D^2+1) := by
  have hd : d^2+1 ≤ D^2+1 := Nat.add_le_add_right (Nat.pow_le_pow_left h 2) 1
  exact ⟨(interpolationNegativeNumerator_envelope d i).trans (Nat.pow_le_pow_right (by decide) hd),
    (interpolationDenominator_envelope d i).trans (Nat.pow_le_pow_right (by decide) hd)⟩

lemma normalization_envelope (w : WordInstance) (q : Index w) :
    ((q.2.val.factorial:ℤ)^(height w q.1)).natAbs ≤
      2^((innerBound (wordBits w).length)^2*heightBound (wordBits w).length) := by
  have hE := (parameter_bounds w q.1).2.2
  have hH := (parameter_bounds w q.1).2.1
  have hs : q.2.val ≤ innerBound (wordBits w).length := by have := q.2.isLt;omega
  have hf : q.2.val.factorial ≤ 2^((innerBound (wordBits w).length)^2) :=
    (factorial_le_two_pow_square _).trans (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left hs 2))
  simp only [Int.natAbs_pow,Int.natAbs_natCast]
  calc
    _ ≤ (2^((innerBound (wordBits w).length)^2))^(height w q.1) := Nat.pow_le_pow_left hf _
    _ = 2^((innerBound (wordBits w).length)^2*height w q.1) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hH)

lemma ratio_bound (w : WordInstance) (hw : w.word≠[]) (q : Index w) :
    (ratio w q (perfectMatchingCount (query w q).2.graph)).1.natAbs ≤ 2^(termExponent (wordBits w).length) ∧
      (ratio w q (perfectMatchingCount (query w q).2.graph)).2.natAbs ≤ 2^(termExponent (wordBits w).length) := by
  let L := (wordBits w).length
  have ho := weights_envelope q.1 (parameter_bounds w q.1).1
  have hi := weights_envelope q.2 (parameter_bounds w q.1).2.2
  have hn := normalization_envelope w q
  have ha := query_answer_bound w hw q
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
    change _ ≤ 2^(termExponent L)
    simp only [ratio,Int.natAbs_mul]
    apply hh.trans
    apply Nat.pow_le_pow_right (by decide)
    dsimp only [L]
    unfold termExponent
    omega

lemma accumulator_prefix_bound (w : WordInstance) (hw : w.word≠[]) :
    RationalAccumulator.BitBound
      (1+(termExponent (wordBits w).length+1)*queryCountBound (wordBits w).length+
        termExponent (wordBits w).length+2) (0,1) (terms w) := by
  have h := RationalAccumulator.bitBound_of_abs (0,1) (terms w) 1 (termExponent (wordBits w).length)
    (by constructor <;> decide) (by
      intro b hb
      obtain ⟨q,_,rfl⟩ := List.mem_map.mp hb
      exact ratio_bound w hw q)
  apply h.mono
  have hn := terms_length_bound w
  gcongr

end HiddenCircuits.GraphReduction.Runtime.WordGraph.Recovery
