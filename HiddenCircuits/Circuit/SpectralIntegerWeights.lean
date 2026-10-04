import HiddenCircuits.Circuit.LagrangeIntegerArrays
import HiddenCircuits.Circuit.DoubleSpectral

/-! Executable triangular spectral enumeration and bounded integer coefficient data. -/
namespace HiddenCircuits.Circuit
open scoped BigOperators
open LagrangeIntegerArrays IntegerSpectralWeights

/-- Literal lexicographic triangular enumeration, with no chosen finite-type equivalence. -/
def spectralIndices (g : ℕ) : List (SpectralIndex g) :=
  (List.finRange (g+1)).sigma (fun a => List.finRange (g-a.val+1))

 theorem spectralIndices_nodup (g : ℕ) : (spectralIndices g).Nodup :=
  (List.nodup_finRange _).sigma (fun _ => List.nodup_finRange _)

@[simp] theorem mem_spectralIndices (g : ℕ) (x : SpectralIndex g) : x∈spectralIndices g := by
  rcases x with ⟨a,b⟩
  exact List.mem_sigma.mpr ⟨by simp,by simp⟩

 theorem spectralIndices_toFinset (g : ℕ) : (spectralIndices g).toFinset=Finset.univ := by
  ext x
  simp

 theorem spectralIndices_length (g : ℕ) : (spectralIndices g).length=Fintype.card (SpectralIndex g) := by
  rw [← List.toFinset_card_of_nodup (spectralIndices_nodup g),spectralIndices_toFinset,Finset.card_univ]

def spectralIntegerNode {g : ℕ} (x : SpectralIndex g) : ℤ := spectralNode x.1.val x.2.val

 theorem spectralIntegerNode_injective (g : ℕ) : Function.Injective (@spectralIntegerNode g) := by
  intro x y he
  apply spectralPair_injective g
  apply spectralNode_injective
  change (spectralNode x.1.val x.2.val:ℤ)=(spectralNode y.1.val y.2.val:ℤ) at he
  change spectralNode x.1.val x.2.val=spectralNode y.1.val y.2.val
  exact_mod_cast he

 theorem spectralIntegerNode_bound {g : ℕ} (x : SpectralIndex g) :
    (spectralIntegerNode x).natAbs ≤ 2^(4*g) := by
  have hh := spectralNode_bound x
  have he : (16:ℕ)^g=2^(4*g) := by change (2^4)^g=2^(4*g); rw [pow_mul]
  simpa only [spectralIntegerNode,Int.natAbs_natCast,he] using hh

def spectralBasisDenominator (g : ℕ) (i : SpectralIndex g) : ℤ :=
  basisDenominator (spectralIndices g) spectralIntegerNode i

def spectralBasisNumerator (g : ℕ) (i : SpectralIndex g) (k : ℕ) : ℤ :=
  basisNumerator (spectralIndices g) spectralIntegerNode i k

/-- The complete stored numerator array is computed by the actual quadratic product loop. -/
def spectralBasisArray (g : ℕ) (i : SpectralIndex g) : HiddenCircuits.DH.ArrayColumn.Counted (Array ℤ) :=
  arrayRun (otherNodes (spectralIndices g) spectralIntegerNode i)

 theorem spectralBasisArray_read (g : ℕ) (i : SpectralIndex g) (k : ℕ) :
    HiddenCircuits.DH.ArrayColumn.read (spectralBasisArray g i).value k=spectralBasisNumerator g i k :=
  arrayRun_read _ _

 theorem spectralBasisDenominator_ne_zero (g : ℕ) (i : SpectralIndex g) :
    spectralBasisDenominator g i≠0 := basisDenominator_ne_zero _ _ (spectralIntegerNode_injective g) i

/-- Every signed integer coefficient/denominator has a displayed polynomial bit bound. -/
theorem spectralBasis_bits (g : ℕ) (i : SpectralIndex g) (k : ℕ) :
    (spectralBasisNumerator g i k).natAbs.size+1 ≤ (4*g+1)*(g+1)^2+2 ∧
      (spectralBasisDenominator g i).natAbs.size+1 ≤ (4*g+1)*(g+1)^2+2 := by
  have hh := basis_bounds (spectralIndices g) spectralIntegerNode (4*g) spectralIntegerNode_bound i k
  rw [spectralIndices_length] at hh
  have hc := spectralIndex_card_bound g
  exact ⟨hh.1.trans (by gcongr),hh.2.trans (by gcongr)⟩

/-- The exact Section7 coefficient is an explicit sum of ratios of the computed integer arrays.
For z=0 and z=-1 all target powers are in {-1,0,1}. -/
theorem targetCoefficient_integer_weights (g : ℕ) (z : ℤ) (k : ℕ) :
    targetCoefficient g (z:ℚ) k=
      ∑ i : SpectralIndex g, ((z^(g-i.1.val-i.2.val):ℤ):ℚ)*
        ((spectralBasisNumerator g i k:ℚ)/(spectralBasisDenominator g i:ℚ)) := by
  have hh := interpolate_coefficient (spectralIndices g) (spectralIndices_nodup g)
    (mem_spectralIndices g) spectralIntegerNode
    (fun i : SpectralIndex g => (z:ℚ)^(g-i.1.val-i.2.val)) k
  simpa only [targetCoefficient,spectralCoefficient,spectralPolynomial,rationalSpectralNode,
    spectralIntegerNode,Int.cast_natCast,Int.cast_pow,spectralBasisNumerator,spectralBasisDenominator] using hh

end HiddenCircuits.Circuit
