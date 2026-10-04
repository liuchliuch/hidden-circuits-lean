import HiddenCircuits.DH.Runtime.RawNumericModel
import HiddenCircuits.Complexity.GraphEncoding

/-! The total binary extension parses its ordinary graph
input and computes its own physical-scan pruning plan. Invalid encodings return
zero; no correctness claim is imposed on valid inputs outside the DH promise. -/
namespace HiddenCircuits.DH.Runtime.BinaryModel
open Complexity

def matrixCount {n : ℕ} (G : MatrixGraph n) : ℕ :=
  NumericStateModel.result (NumericStateModel.rawRun (PairCheck.MatrixData.ofGraph G) n (NumericStateModel.initial n))
def count (input : BitString) : ℕ :=
  match GraphInput.decode input with
  | none=>0
  | some G=>matrixCount G.2

def function (input : BitString) : BitString := Computability.encodeNat (count input)

theorem malformed {input : BitString} (h : GraphInput.decode input=none) : function input=[] := by
  simp only [function,count,h]
  rfl
theorem distanceHereditary (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) :
    function (GraphInput.encode G)=Computability.encodeNat (perfectMatchingCount G.2.graph) := by
  simp only [function,count,GraphInput.decode_encode]
  rw [matrixCount,NumericStateModel.raw_count_correct G.2 hG]
theorem quasiChains (G : GraphInput) (hG : QuasiChains G.2.graph) :
    function (GraphInput.encode G)=Computability.encodeNat (perfectMatchingCount G.2.graph) :=
  distanceHereditary G (quasiChains_distanceHereditary hG)
end HiddenCircuits.DH.Runtime.BinaryModel
