import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponentInitialize

/-! Literal storage bounds for component scans, independent of graph-class
membership. These bounds are derived from the physical fixed-n loop itself. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
open Complexity DH.Runtime.PairCheck

lemma step_order_length {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (s : Data n) :
    (step G A s).order.length≤s.order.length+1 := by
  unfold step
  split
  · omega
  · split
    · omega
    · simp [advance]

lemma run_order_length {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (fuel : ℕ) (s : Data n) :
    (run G A fuel s).order.length≤s.order.length+fuel := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    have h := ih (step G A s)
    have hs := step_order_length G A s
    simp only [run]
    omega

lemma component_order_length {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (root : Fin n) :
    (component G A root).order.length≤n+1 := by
  have h := run_order_length G A n (initial A root)
  simpa [component,initial,emptyData,advance,Nat.add_comm] using h

lemma orderBits_length_le {n : ℕ} (ls : List (Fin n)) : (orderBits ls).length≤2*(n+1)*ls.length := by
  have h : ∀ws : List (Fin n), (encodeBitList (ws.map (fun v=>List.replicate v.val true))).length≤2*(n+1)*ws.length := by
    intro ws
    induction ws with
    | nil => simp [encodeBitList]
    | cons v vs ih =>
      have hv := v.isLt
      simp only [List.map_cons,encodeBitList,List.length_cons,pairBits_length,List.length_replicate]
      nlinarith
  simpa only [orderBits,List.length_reverse] using h ls.reverse

lemma component_orderBits_length {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (root : Fin n) :
    (orderBits (component G A root).order).length≤2*(n+1)^2 := by
  have h := orderBits_length_le (component G A root).order
  have hm := Nat.mul_le_mul_left (2*(n+1)) (component_order_length G A root)
  nlinarith

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
