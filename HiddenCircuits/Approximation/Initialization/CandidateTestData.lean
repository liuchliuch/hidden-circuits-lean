import HiddenCircuits.Approximation.Initialization.ResidualPositiveData

/-! The exact Boolean candidate predicate consumed by finite search.
It checks a real graph edge and the integer determinant of its erased residual. -/
namespace HiddenCircuits.Approximation.Initialization.CandidateTest
open Complexity SelfReduction

def valid {n : ℕ} (G : MatrixGraph n) (U : Finset (Fin n)) (u v : Fin n) : Bool :=
  decide (v ∈ U) && G.edge u v

def test {n : ℕ} (G : MatrixGraph n) (U : Finset (Fin n))
    (B : ℕ) (tape : BitString) (u v : Fin n) : Bool :=
  if valid G U u v = true then ResidualPositive.positive G ((U.erase u).erase v) B tape else false

lemma valid_iff {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) (u v : Fin N) :
    valid G U u v = true ↔ v ∈ U ∧ G.graph.Adj u v := by
  simp [valid,MatrixGraph.graph]

theorem test_child {b d : ℕ} (G : MatrixGraph (b+1))
    (U : {U : Finset (Fin (b+1)) // U.card=2*(d+1)}) (k : ℕ)
    (r : CoinTape (ResidualTest.bits b k)) (v : Fin (b+1)) :
    test G U.val (b+1+k) (List.ofFn r) (matchingPivot U).val v =
      ResidualTest.statePositive G.graph k (matchingChild G.graph ⟨d+1,some U⟩ v) r := by
  by_cases h : v∈U.val ∧ G.graph.Adj (matchingPivot U).val v
  · have hv := (valid_iff G U.val (matchingPivot U).val v).mpr h
    rw [test,if_pos hv,matchingChild_active,dif_pos h]
    exact ResidualPositive.positive_residual G
      ⟨(U.val.erase (matchingPivot U).val).erase v,erased_card U v h.1 h.2.ne.symm⟩ k r
  · have hv : valid G U.val (matchingPivot U).val v = false := Bool.eq_false_iff.mpr
      (fun he => h ((valid_iff G U.val _ v).mp he))
    rw [test,if_neg (by simp [hv]),matchingChild_active,dif_neg h]
    rfl

theorem test_sound {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) (B : ℕ) (tape : BitString)
    (u v : Fin N) (h : test G U B tape u v = true) :
    v∈U ∧ G.graph.Adj u v ∧
      Nonempty (PerfectMatching (G.graph.induce (((U.erase u).erase v) : Set (Fin N)))) := by
  unfold test at h
  split at h
  next hv =>
    have hh := (valid_iff G U u v).mp hv
    exact ⟨hh.1,hh.2,ResidualPositive.positive_sound G _ B tape h⟩
  next hv => contradiction

end HiddenCircuits.Approximation.Initialization.CandidateTest
