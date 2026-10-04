import HiddenCircuits.Approximation.Initialization.TutteInteger

/-! The total integer determinant predicate on a retained vertex set.
The finite machine implementation is added separately in ResidualPositive. -/
namespace HiddenCircuits.Approximation.Initialization.ResidualPositive
open Complexity SelfReduction

def positive {n : ℕ} (G : MatrixGraph n) (U : Finset (Fin n))
    (B : ℕ) (tape : BitString) : Bool :=
  TutteInteger.positive (ResidualTest.graph G.graph U) B tape

theorem positive_sound {n : ℕ} (G : MatrixGraph n) (U : Finset (Fin n))
    (B : ℕ) (tape : BitString) (h : positive G U B tape = true) :
    Nonempty (PerfectMatching (G.graph.induce (U : Set (Fin n)))) :=
  (TutteInteger.positive_sound (ResidualTest.graph G.graph U) B tape h).map
    (perfectMatchingIsoEquiv (ResidualTest.graphIso G.graph U))

theorem positive_residual {b d : ℕ} (G : MatrixGraph (b+1))
    (U : {U : Finset (Fin (b+1)) // U.card = 2*d}) (k : ℕ)
    (r : CoinTape (ResidualTest.bits b k)) :
    positive G U.val (b+1+k) (List.ofFn r) =
      ResidualTest.statePositive G.graph k ⟨d,some U⟩ r := by
  unfold positive
  rw [TutteInteger.positive_prefix _ (ResidualTest.budget U.val k) r,
    TutteInteger.positive_ofFn]
  rfl

end HiddenCircuits.Approximation.Initialization.ResidualPositive
