import HiddenCircuits.Circuit.Runtime.SpectralBasisCorrectness
import HiddenCircuits.Circuit.Runtime.SpectralVectorCombineCell
import HiddenCircuits.Circuit.SpectralWeightData

/-! Exact prefix invariants for the concrete common-denominator spectral
weight loop. Bounds apply to every intermediate prefix, not just its output. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralWeights
open scoped BigOperators
open HiddenCircuits.Complexity HiddenCircuits.Complexity.BinaryArithmetic
open IntegerRatioAccumulator

def denominator (g : ℕ) : ℤ :=
  commonDenominator (spectralIndices g) (spectralBasisDenominator g)
def target (g : ℕ) (z : ℤ) (i : SpectralIndex g) : ℤ := z^(g-i.1.val-i.2.val)
def scale (g : ℕ) (z : ℤ) (i : SpectralIndex g) : ℤ :=
  target g z i * (denominator g / spectralBasisDenominator g i)
def term (g : ℕ) (z : ℤ) (i : SpectralIndex g) (k : ℕ) : ℤ :=
  scale g z i * spectralBasisNumerator g i k
def vector (g : ℕ) (z : ℤ) (done : List (SpectralIndex g)) : List ℤ :=
  List.ofFn (fun k : Fin (Fintype.card (SpectralIndex g)) =>
    (done.map (fun i => term g z i k.val)).sum)

theorem denominator_ne_zero (g : ℕ) : denominator g≠0 :=
  commonDenominator_ne_zero _ _ (spectralBasisDenominator_ne_zero g)

theorem denominator_factor (g : ℕ) (i : SpectralIndex g) :
    denominator g = spectralBasisDenominator g i *
      (((spectralIndices g).filter (fun j => j≠i)).map (spectralBasisDenominator g)).prod := by
  rw [denominator,commonDenominator_eq _ (spectralIndices_nodup g) (mem_spectralIndices g),
    list_prod_except _ (spectralIndices_nodup g) (mem_spectralIndices g)]
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

theorem denominator_divisible (g : ℕ) (i : SpectralIndex g) :
    spectralBasisDenominator g i ∣ denominator g :=
  ⟨_,denominator_factor g i⟩

theorem denominator_quotient (g : ℕ) (i : SpectralIndex g) :
    denominator g / spectralBasisDenominator g i =
      (((spectralIndices g).filter (fun j => j≠i)).map (spectralBasisDenominator g)).prod := by
  rw [denominator_factor g i]
  simp [spectralBasisDenominator_ne_zero g i]

@[simp] theorem vector_length (g : ℕ) (z : ℤ) (done : List (SpectralIndex g)) :
    (vector g z done).length=Fintype.card (SpectralIndex g) := by simp [vector]

theorem vector_get (g : ℕ) (z : ℤ) (done : List (SpectralIndex g))
    (k : ℕ) (hk : k<Fintype.card (SpectralIndex g)) :
    (vector g z done)[k]'(by simpa using hk) = (done.map (fun i => term g z i k)).sum := by
  simp [vector]

@[simp] theorem vector_nil (g : ℕ) (z : ℤ) :
    vector g z []=List.replicate (Fintype.card (SpectralIndex g)) 0 := by
  simp [vector,List.ofFn_const]

theorem coefficient_get (g : ℕ) (i : SpectralIndex g) (k : ℕ)
    (hk : k<Fintype.card (SpectralIndex g)) :
    (SpectralBasis.coefficientVector g i)[k]'(by simpa [SpectralBasis.coefficientVector_length] using hk)=
      spectralBasisNumerator g i k := by
  have h := SpectralBasis.coefficientVector_get g i k
  have hlen : k<(SpectralBasis.coefficientVector g i).length := by
    simpa [SpectralBasis.coefficientVector_length] using hk
  rw [List.getElem?_eq_getElem hlen] at h
  exact h

/-- The prefix expression is precisely one literal streamed vector update. -/
theorem vector_append (g : ℕ) (z : ℤ) (done : List (SpectralIndex g)) (i : SpectralIndex g) :
    vector g z (done++[i]) = SpectralVectorCombine.output (scale g z i)
      ((SpectralBasis.coefficientVector g i).zip (vector g z done)) := by
  apply List.ext_getElem
  · simp [SpectralVectorCombine.output,SpectralBasis.coefficientVector_length]
  · intro k hk hk'
    have h : k<Fintype.card (SpectralIndex g) := by simpa using hk
    simp only [vector_get g z _ k h,List.map_append,List.sum_append,List.map_cons,
      List.map_nil,List.sum_cons,List.sum_nil,add_zero,SpectralVectorCombine.output,
      List.getElem_map,List.getElem_zip,SpectralVectorCombine.value]
    rw [coefficient_get g i k h]
    rfl

theorem vector_append_zipWith (g : ℕ) (z : ℤ) (done : List (SpectralIndex g)) (i : SpectralIndex g) :
    vector g z (done++[i]) = List.zipWith (fun a v => v+scale g z i*a)
      (SpectralBasis.coefficientVector g i) (vector g z done) := by
  rw [vector_append]
  apply List.ext_getElem
  · simp [SpectralVectorCombine.output]
  · intro k hk hk'
    simp [SpectralVectorCombine.output,SpectralVectorCombine.value]

theorem term_eq (g : ℕ) (z : ℤ) (i : SpectralIndex g) (k : ℕ) :
    term g z i k = spectralWeightedNumerator g z k i *
      (((spectralIndices g).filter (fun j => j≠i)).map (spectralBasisDenominator g)).prod := by
  rw [term,scale,denominator_quotient,spectralWeightedNumerator,spectralBasisArray_read]
  unfold target
  ring

/-- The completed vector contains the exact numerators of the original
mathematical interpolation weights, in coefficient order. -/
theorem vector_complete (g : ℕ) (z : ℤ) :
    vector g z (spectralIndices g) = List.ofFn
      (fun k : Fin (Fintype.card (SpectralIndex g)) => (spectralWeightData g z k.val).1) := by
  unfold vector
  congr 1
  funext k
  simp only [spectralWeightData,commonNumerator,term_eq]

theorem denominator_data (g : ℕ) (z : ℤ) (k : ℕ) :
    denominator g=(spectralWeightData g z k).2 := rfl

def denominatorExponent (g : ℕ) : ℕ := spectralBasisBitBound g*(g+1)^2
def termExponent (g : ℕ) : ℕ := denominatorExponent g+spectralBasisBitBound g
def vectorBitBound (g : ℕ) : ℕ := termExponent g+(g+1)^2+2

theorem denominator_envelope (g : ℕ) : (denominator g).natAbs≤2^(denominatorExponent g) := by
  have h := int_prod_envelope Finset.univ (spectralBasisDenominator g) (spectralBasisBitBound g)
    (fun i _ => spectralBasisDenominator_envelope g i)
  rw [denominator,commonDenominator_eq _ (spectralIndices_nodup g) (mem_spectralIndices g)]
  apply h.trans
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.mul_le_mul_left _ (spectralIndex_card_bound g)

theorem target_envelope (g : ℕ) (z : ℤ) (hz : z.natAbs≤1) (i : SpectralIndex g) :
    (target g z i).natAbs≤1 := by
  simpa [target,Int.natAbs_pow] using Nat.pow_le_pow_left hz (g-i.1.val-i.2.val)

theorem scale_envelope (g : ℕ) (z : ℤ) (hz : z.natAbs≤1) (i : SpectralIndex g) :
    (scale g z i).natAbs≤2^(denominatorExponent g) := by
  rw [scale,Int.natAbs_mul]
  calc
    _ ≤ 1*(denominator g).natAbs := Nat.mul_le_mul (target_envelope g z hz i)
      (Int.natAbs_ediv_le_natAbs _ _)
    _ ≤ _ := by simpa using denominator_envelope g

theorem term_envelope (g : ℕ) (z : ℤ) (hz : z.natAbs≤1) (i : SpectralIndex g) (k : ℕ) :
    (term g z i k).natAbs≤2^(termExponent g) := by
  simpa only [term,termExponent,Int.natAbs_mul,pow_add] using
    Nat.mul_le_mul (scale_envelope g z hz i) (spectralBasisNumerator_envelope g i k)

theorem list_sum_envelope {α : Type*} (xs : List α) (f : α → ℤ) (B : ℕ)
    (hf : ∀ x∈xs,(f x).natAbs≤2^B) : (xs.map f).sum.natAbs≤2^(B+xs.length) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hf a (by simp)
    have ht := ih (fun x hx => hf x (by simp [hx]))
    have hpow : 2^B≤2^(B+xs.length) := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      _ ≤ (f a).natAbs+(xs.map f).sum.natAbs := by
        simpa only [List.map_cons,List.sum_cons] using Int.natAbs_add_le (f a) (xs.map f).sum
      _ ≤ 2^(B+xs.length)+2^(B+xs.length) := Nat.add_le_add (ha.trans hpow) ht
      _ = _ := by simp only [List.length_cons,Nat.add_succ,pow_succ];omega

/-- All coefficients of all prefixes satisfy a polynomial bound, whether or
not a prefix happens to cancel to zero. -/
theorem vector_member_bits (g : ℕ) (z : ℤ) (hz : z.natAbs≤1)
    (done : List (SpectralIndex g)) (hd : done.length≤(g+1)^2) (c : ℤ) (hc : c∈vector g z done) :
    (signedBits c).length≤vectorBitBound g := by
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hc
  have h := list_sum_envelope done (fun i => term g z i k.val) (termExponent g)
    (fun i _ => term_envelope g z hz i k.val)
  exact (signedBits_length_of_abs_bound h).trans (by unfold vectorBitBound;omega)

theorem vector_stream_bound (g : ℕ) (z : ℤ) (hz : z.natAbs≤1)
    (done : List (SpectralIndex g)) (hd : done.length≤(g+1)^2) :
    (encodeBitList ((vector g z done).map signedBits)).length≤(g+1)^2*(2*vectorBitBound g+2) := by
  have h := encodedWords_length_le ((vector g z done).map signedBits) (vectorBitBound g) (by
    intro w hw
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hw
    exact vector_member_bits g z hz done hd c hc)
  simp only [List.length_map,vector_length] at h
  exact h.trans (Nat.mul_le_mul_right _ (spectralIndex_card_bound g))

end HiddenCircuits.Circuit.Runtime.SpectralWeights
