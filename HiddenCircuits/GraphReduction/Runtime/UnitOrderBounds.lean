import HiddenCircuits.GraphReduction.Runtime.UnitOrderSemantics

/-! Uniform storage bounds for the accumulated original-label output, on all
matrix data, including rejected inputs. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitOrderSemantics
open Complexity DH.Runtime.PairCheck

lemma savedOrder_length {n : ℕ} (G : MatrixData n) (A : Vector Bool n)
    (b : UnitRecognitionRoots.Best n) : (savedOrder G A b).length ≤ n+1 := by
  cases b with
  | none => simp [savedOrder]
  | some root =>
    simpa only [savedOrder,Option.map_some,Option.getD_some,List.length_reverse] using
      UnitRecognitionComponent.component_order_length G A root

/-- No accepted-graph hypothesis is needed for the physical output-space bound. -/
theorem run_order_length {n : ℕ} (G : MatrixData n) (fuel : ℕ)
    (A : Vector Bool n) (acc : List (Fin n)) :
    (run G fuel A acc).2.length ≤ acc.length + fuel*(n+1) := by
  induction fuel generalizing A acc with
  | zero => simp [run]
  | succ fuel ih =>
    have hi := ih (UnitRecognitionRoots.residual G A (UnitRecognitionRoots.find G A))
      (savedOrder G A (UnitRecognitionRoots.find G A) ++ acc)
    have hs := savedOrder_length G A (UnitRecognitionRoots.find G A)
    simp only [run,List.length_append] at hi ⊢
    nlinarith

/-- Encoding uses unary original labels and the project's self-delimiting list format. -/
lemma encode_order_length {n : ℕ} (ls : List (Fin n)) :
    (encodeBitList (ls.map (fun v => List.replicate v.val true))).length ≤
      2*(n+1)*ls.length := by
  simpa only [UnitRecognitionComponent.orderBits,List.reverse_reverse,List.length_reverse] using
    UnitRecognitionComponent.orderBits_length_le ls.reverse

theorem order_length_le {n : ℕ} (G : MatrixData n) :
    (order G).length ≤ n*(n+1) := by
  simpa only [order,List.length_nil,Nat.zero_add] using
    run_order_length G n (Vector.replicate n true) []

/-- The entire returned encoded array has a cubic bound even on rejection. -/
theorem encoded_order_length_le {n : ℕ} (G : MatrixData n) :
    (encodeBitList ((order G).map (fun v => List.replicate v.val true))).length ≤
      2*n*(n+1)^2 := by
  have he := encode_order_length (order G)
  have hs := order_length_le G
  nlinarith

end HiddenCircuits.GraphReduction.Runtime.UnitOrderSemantics
