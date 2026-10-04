import HiddenCircuits.Circuit.Runtime.SpectralBasis

/-! Exact actual spectral-basis output identities and polynomial bounds in circuit degree. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralBasis
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic LagrangeIntegerArrays Polynomial

 def roots (g : ℕ) (i : SpectralIndex g) : List ℤ := otherNodes (spectralIndices g) spectralIntegerNode i
 def coefficientVector (g : ℕ) (i : SpectralIndex g) : List ℤ := SpectralCoefficients.coefficients (roots g i)

 theorem coefficientVector_get (g : ℕ) (i : SpectralIndex g) (k : ℕ) :
    (coefficientVector g i)[k]?.getD 0=spectralBasisNumerator g i k :=
  SpectralCoefficients.coefficients_get _ _

 theorem roots_length_add_one (g : ℕ) (i : SpectralIndex g) :
    (roots g i).length+1=Fintype.card (SpectralIndex g) := by
  have hn := (spectralIndices_nodup g).filter (fun j => decide (j≠i))
  have hs : ((spectralIndices g).filter (fun j => j≠i)).toFinset=Finset.univ.erase i := by
    ext j;simp
  unfold roots otherNodes
  rw [List.length_map,←List.toFinset_card_of_nodup hn,hs]
  exact Finset.card_erase_add_one (Finset.mem_univ i)

 theorem coefficientVector_length (g : ℕ) (i : SpectralIndex g) :
    (coefficientVector g i).length=Fintype.card (SpectralIndex g) := by
  rw [coefficientVector,SpectralCoefficients.coefficients_length,roots_length_add_one]

 theorem node_signed_length (g : ℕ) (i : SpectralIndex g) :
    (signedBits (spectralIntegerNode i)).length≤4*g+2 :=
  signedBits_length_of_abs_bound (spectralIntegerNode_bound i)

 theorem roots_signed_length (g : ℕ) (i : SpectralIndex g) (a : ℤ) (ha : a∈roots g i) :
    (signedBits a).length≤4*g+2 := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
  exact node_signed_length g j

noncomputable def inputSize : Polynomial ℕ := (4*X+2)+(X+1)^2*(2*(4*X+2)+2)
noncomputable def spectralTime : Polynomial ℕ := time.comp inputSize

 theorem spectral_input_length (g : ℕ) (i : SpectralIndex g) :
    inputLength (spectralIntegerNode i) (roots g i)≤ inputSize.eval g := by
  have hx := node_signed_length g i
  have hl : (roots g i).length≤(g+1)^2 := by
    have hh := roots_length_add_one g i
    have hc := spectralIndex_card_bound g
    omega
  have hs := encodedWords_length_le ((roots g i).map signedBits) (4*g+2) (by
    intro w hw;obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw;exact roots_signed_length g i a ha)
  simp only [List.length_map] at hs
  have hm := Nat.mul_le_mul_right (2*(4*g+2)+2) hl
  simp only [inputLength,inputSize,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat]
  omega

/-- On the actual omitted spectral nodes, the real program emits every exact
basis numerator and the proved nonzero basis denominator, with polynomial time. -/
theorem program_spectral_executes (oracle : BitString → ℕ) (g : ℕ) (i : SpectralIndex g) :
    ∃ t, program.Executes oracle
      (store (signedBits (spectralIntegerNode i)) (encodeBitList ((roots g i).map signedBits)) [] [] [] [])
      (store (signedBits (spectralIntegerNode i)) (encodeBitList ((roots g i).map signedBits))
        (encodeBitList ((coefficientVector g i).map signedBits)) (signedBits (spectralBasisDenominator g i)) [] []) t ∧
      t≤spectralTime.eval g := by
  obtain ⟨t,ht,hb⟩ := program_executes oracle (spectralIntegerNode i) (roots g i)
  refine ⟨t,ht,hb.trans ?_⟩
  have hm := polynomial_nat_eval_mono time (spectral_input_length g i)
  simpa only [spectralTime,eval_comp] using hm

 theorem emitted_denominator_nonzero (g : ℕ) (i : SpectralIndex g) : spectralBasisDenominator g i≠0 :=
  spectralBasisDenominator_ne_zero g i
end HiddenCircuits.Circuit.Runtime.SpectralBasis
