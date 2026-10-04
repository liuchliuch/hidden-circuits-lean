import HiddenCircuits.GraphReduction.Runtime.DescriptorEvenParts

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorEven
open Complexity OracleBlock BinaryArithmetic DescriptorFront
set_option maxHeartbeats 800000

def records (width : ℕ) : ℕ → BitString → BitString → List VertexRecord
  | 0,S,T => DescriptorMaskRow.records (vertex 0) (DescriptorMaskDifference.difference S T)
  | n+1,S,T => DescriptorMaskRow.records (vertex 0) S ++ DescriptorRectangle.records (vertex 1) width n ++
      DescriptorMaskRow.records (vertex (n+1)) (DescriptorMaskDifference.difference (List.replicate width true) T)

def bound (width height : ℕ) : ℕ := (height+2)*(width*(20*height+20*width+140)+20)+height+20
noncomputable def positive : OracleBlock 19 := seq sourceRow
  (seq (push 1 true) (seq (rectangleLoop false) (seq (differenceRow true) (clear 1))))

theorem positive_executes (g : BitString → ℕ) (width n samples : ℕ) (S T pairs out : BitString) (count : ℕ)
    (hS : S.length=width) (hT : T.length=width) :
    ∃c,positive.Executes g (workState (vertex 0) width (n+1) samples n [] S T pairs out count)
      (workState (vertex 0) width (n+1) samples 0 [] S T pairs
        ((encodeBitList ((records width (n+1) S T).map encodeVertex)).reverse++out)
        (count+(records width (n+1) S T).length)) c ∧ c≤bound width (n+1) := by
  let A := DescriptorMaskRow.records (vertex 0) S
  let B := DescriptorRectangle.records (vertex 1) width n
  let C := DescriptorMaskRow.records (vertex (n+1)) (DescriptorMaskDifference.difference (List.replicate width true) T)
  let outA := (encodeBitList (A.map encodeVertex)).reverse++out
  let outB := (encodeBitList (B.map encodeVertex)).reverse++outA
  let outC := (encodeBitList (C.map encodeVertex)).reverse++outB
  obtain ⟨a,ha,hab⟩ := sourceRow_executes g (vertex 0) rfl width (n+1) samples n S T pairs out count
  have hi := increment_layer g (vertex 0) width (n+1) samples n S T pairs outA (count+A.length)
  obtain ⟨b,hb,hbb⟩ := rectangleLoop_executes g false (vertex 1) rfl width (n+1) samples n S T pairs outA (count+A.length)
  obtain ⟨c,hc,hcb⟩ := differenceRow_executes g true (vertex (n+1)) rfl width (n+1) samples 0 S T pairs outB (count+A.length+width*n)
    (by simpa only [ite_true,List.length_replicate] using hT.symm)
  have hz := clear_layer g (vertex (n+1)) width (n+1) samples 0 S T pairs outC (count+A.length+width*n+C.length)
  have hvertex : {vertex 1 with layer:=(vertex 1).layer+n}=vertex (n+1) := by simp [vertex,Nat.add_comm]
  rw [hvertex] at hb
  have hlen : B.length=width*n := DescriptorRectangle.records_length _ _ _
  have hall := seq_executes _ _ g ha (seq_executes _ _ g hi (seq_executes _ _ g hb (seq_executes _ _ g hc hz)))
  refine ⟨a+(1+(b+(c+((vertex (n+1)).layer+1)+2)+2)+2)+2,?_,?_⟩
  · convert hall using 1
    simp only [records,List.map_append,encodeBitList_append,List.reverse_append,List.append_assoc,List.length_append]
    dsimp only [outC,outB,outA,A,B,C] at *
    rw [DescriptorRectangle.records_length]
    congr 1 <;> simp [vertex] <;> omega
  · dsimp only [vertex,backgroundCode] at hab hbb hcb
    simp only [Bool.false_eq_true,ite_false,ite_true,List.length_replicate] at hbb hcb
    rw [hS] at hab
    change a+(1+(b+(c+(n+2)+2)+2)+2)+2≤_
    unfold bound
    nlinarith
end HiddenCircuits.GraphReduction.Runtime.DescriptorEven
