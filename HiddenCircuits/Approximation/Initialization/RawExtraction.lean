import HiddenCircuits.Approximation.Initialization.CandidateTestData
import HiddenCircuits.Approximation.Initialization.ForwardExtraction

/-! A total finite raw-tape accumulator algorithm. It examines at most `fuel`
vertex pairs, constructs every returned matching itself, and rejects exhausted
searches. Missing raw bits are interpreted by the proved zero-padding reader. -/
namespace HiddenCircuits.Approximation.Initialization.RawExtraction
open Complexity SelfReduction SamplerRuntime

variable {N : ℕ} (G : MatrixGraph N)

def stageLength (N B : ℕ) : ℕ := N*N*B

def select (U : Finset (Fin N)) (B : ℕ) (tape : BitString) : Option (Fin N) :=
  if h : U.Nonempty then (List.finRange N).find? (CandidateTest.test G U B tape (U.min' h)) else none

noncomputable def run (B : ℕ) : ℕ → Finset (Fin N) → BitString → Equiv.Perm (Fin N) → Option (Equiv.Perm (Fin N))
  | 0,U,_,π => if U=∅ then some π else none
  | fuel+1,U,source,π =>
      if h : U.Nonempty then
        let tape := TapeRead.takePadded (stageLength N B) source
        match (List.finRange N).find? (CandidateTest.test G U B tape (U.min' h)) with
        | none => none
        | some v => run B fuel ((U.erase (U.min' h)).erase v) (source.drop (stageLength N B))
            (MonotoneEndpoints.transpose π (U.min' h) v)
      else some π

@[simp] theorem run_empty (B fuel : ℕ) (source : BitString) (π : Equiv.Perm (Fin N)) :
    run G B fuel ∅ source π=some π := by
  cases fuel <;> simp [run]

theorem run_valid (B fuel : ℕ) (U : Finset (Fin N)) (source : BitString)
    (π ρ : Equiv.Perm (Fin N)) (hπ : PartialPartners.Valid G.graph U π)
    (hr : run G B fuel U source π=some ρ) : PartialPartners.Valid G.graph ∅ ρ := by
  induction fuel generalizing U source π ρ with
  | zero =>
    by_cases hU : U=∅
    · have hp : π=ρ := by simpa [run,hU] using hr
      simpa [←hp,hU] using hπ
    · simp [run,hU] at hr
  | succ fuel ih =>
    by_cases hU : U.Nonempty
    · let tape := TapeRead.takePadded (stageLength N B) source
      cases hs : (List.finRange N).find? (CandidateTest.test G U B tape (U.min' hU)) with
      | none => simp [run,hU,tape,hs] at hr
      | some v =>
        have hv : CandidateTest.test G U B tape (U.min' hU) v=true :=
          List.find?_some (p:=CandidateTest.test G U B tape (U.min' hU)) (a:=v) hs
        have hh := CandidateTest.test_sound G U B tape (U.min' hU) v hv
        have hp := PartialPartners.add_pair hπ (U.min' hU) v (U.min'_mem hU) hh.1 hh.2.1
        dsimp only [tape] at hs
        have hx : run G B fuel ((U.erase (U.min' hU)).erase v) (source.drop (stageLength N B))
            (MonotoneEndpoints.transpose π (U.min' hU) v)=some ρ := by
          simpa only [run,dif_pos hU,hs] using hr
        exact ih _ _ _ _ hp hx
    · have he : U=∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      have hp : π=ρ := by simpa [run,hU] using hr
      simpa [←hp,he] using hπ

/-- On every tape, a graph without a perfect matching is rejected. -/
theorem run_zero (B fuel : ℕ) (source : BitString) (hG : ¬Nonempty (PerfectMatching G.graph)) :
    run G B fuel Finset.univ source (Equiv.refl (Fin N))=none := by
  cases hr : run G B fuel Finset.univ source (Equiv.refl (Fin N)) with
  | none => rfl
  | some π =>
    have hp := run_valid G B fuel Finset.univ source _ π (PartialPartners.initial G.graph) hr
    exact False.elim (hG ⟨(PartialPartners.finish hp).toMatching⟩)

end HiddenCircuits.Approximation.Initialization.RawExtraction
