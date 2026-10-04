import HiddenCircuits.Circuit.Runtime.SpectralNodeOmission
import HiddenCircuits.Circuit.SpectralIntegerWeights
import Mathlib.Data.List.InsertIdx

namespace HiddenCircuits.Circuit.Runtime.SpectralNodeOmission
open HiddenCircuits.Complexity HiddenCircuits.Complexity.BinaryArithmetic
open HiddenCircuits.DH.Runtime.WordArray LagrangeIntegerArrays

theorem index_omission (g j : ℕ) (hj : j<(spectralIndices g).length) :
    (((spectralIndices g).map spectralIntegerNode).map signedBits).eraseIdx j=
      (otherNodes (spectralIndices g) spectralIntegerNode (spectralIndices g)[j]).map signedBits := by
  rw [List.eraseIdx_map,List.eraseIdx_map,←(spectralIndices_nodup g).erase_getElem j hj,
    (spectralIndices_nodup g).erase_eq_filter]
  unfold otherNodes
  congr 2
  apply List.filter_congr
  intro x hx
  apply Bool.eq_iff_iff.mpr
  simp

theorem spectral_program_executes (oracle : BitString → ℕ) (g j : ℕ) (hj : j<(spectralIndices g).length) :
    ∃t, program.Executes oracle
      (store (encodeBitList (((spectralIndices g).map spectralIntegerNode).map signedBits)) (List.replicate j true) [])
      (store (encodeBitList ((otherNodes (spectralIndices g) spectralIntegerNode (spectralIndices g)[j]).map signedBits))
        (List.replicate j true) (signedBits (spectralIntegerNode (spectralIndices g)[j]))) t ∧
      t≤100*((encodeBitList (((spectralIndices g).map spectralIntegerNode).map signedBits)).length+j+1)^2 := by
  have hlen : j<(((spectralIndices g).map spectralIntegerNode).map signedBits).length := by simpa using hj
  obtain ⟨t,ht,hb⟩ := program_executes oracle (((spectralIndices g).map spectralIntegerNode).map signedBits) j hlen
  refine ⟨t,?_,hb⟩
  simpa only [index_omission g j hj,List.getElem_map] using ht
end HiddenCircuits.Circuit.Runtime.SpectralNodeOmission
