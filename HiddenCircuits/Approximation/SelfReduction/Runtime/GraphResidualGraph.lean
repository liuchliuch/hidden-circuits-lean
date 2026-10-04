import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidualPrepare

/-! Fresh compatibility boundary: ordered induced matrices with arbitrary finite
index maps. This is the same graph emitted by the reconstructed initializer. -/
namespace HiddenCircuits.Approximation.Initialization.InducedGraphEmitter
open Complexity

def graph {N n : ℕ} (G : MatrixGraph N) (e : Fin n → Fin N) : MatrixGraph n where
  edge i j := G.edge (e i) (e j)
  symm i j := G.symm _ _
  loopless i := G.loopless _
end HiddenCircuits.Approximation.Initialization.InducedGraphEmitter
namespace HiddenCircuits.Approximation.Initialization.ResidualGraphProgram

def vertexMap {N : ℕ} (U : Finset (Fin N)) : Fin U.card → Fin N := U.orderEmbOfFin rfl
end HiddenCircuits.Approximation.Initialization.ResidualGraphProgram
