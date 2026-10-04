import HiddenCircuits.GraphReduction.Runtime.DescriptorFrontNoQuery

namespace HiddenCircuits.GraphReduction.Runtime.CliqueFront
open Complexity OracleBlock BinaryArithmetic DescriptorFront
set_option maxHeartbeats 800000

noncomputable def popHeight : OracleBlock 19 := branchPop 10 skip skip skip
noncomputable def evenProbes : OracleBlock 19 := seq (push 10 true) (seq (probes false) popHeight)
def tailRecords (mode : Bool) (s h : ℕ) : List VertexRecord := if mode then DescriptorRectangle.records (taggedVertex true true 0) s h else []
noncomputable def tail (mode : Bool) : OracleBlock 19 := if mode then probes true else skip

def probeBound (height samples : ℕ) : ℕ := height*(samples*(20*height+20*samples+125)+19)+68

lemma evenProbes_executes (g : BitString → ℕ) (width height samples : ℕ) (S T pairs out : BitString) (count : ℕ) :
    ∃c,evenProbes.Executes g (workState (DescriptorEven.vertex 0) width height samples 0 [] S T pairs out count)
      (workState (DescriptorEven.vertex 0) width height samples 0 [] S T pairs
        ((encodeBitList ((DescriptorRectangle.records (taggedVertex false true 0) samples (height+1)).map encodeVertex)).reverse++out)
        (count+samples*(height+1))) c ∧ c≤probeBound (height+1) samples+8 := by
  have hp : (push (10:Fin 20) true).Executes g (workState (DescriptorEven.vertex 0) width height samples 0 [] S T pairs out count)
      (workState (DescriptorEven.vertex 0) width (height+1) samples 0 [] S T pairs out count) 1 := by
    convert push_executes g (10:Fin 20) true (workState (DescriptorEven.vertex 0) width height samples 0 [] S T pairs out count) using 1
    funext i;fin_cases i <;> simp [workState,List.replicate_succ]
  obtain ⟨c,hc,hb⟩ := probes_executes g false width (height+1) samples S T pairs out count
  let next := (encodeBitList ((DescriptorRectangle.records (taggedVertex false true 0) samples (height+1)).map encodeVertex)).reverse++out
  have hz : popHeight.Executes g (workState (DescriptorEven.vertex 0) width (height+1) samples 0 [] S T pairs next (count+samples*(height+1)))
      (workState (DescriptorEven.vertex 0) width height samples 0 [] S T pairs next (count+samples*(height+1))) 3 := by
    apply branchPop_true 10 skip skip skip g rfl
    have he : Function.update (workState (DescriptorEven.vertex 0) width (height+1) samples 0 [] S T pairs next (count+samples*(height+1))) 10 (List.replicate height true)=
        workState (DescriptorEven.vertex 0) width height samples 0 [] S T pairs next (count+samples*(height+1)) := by
      funext i;fin_cases i <;> rfl
    rw [he]
    exact skip_executes _ _
  exact ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hc hz),by unfold probeBound;omega⟩

lemma tail_executes (g : BitString → ℕ) (mode : Bool) (width height samples : ℕ) (S T pairs out : BitString) (count : ℕ) :
    ∃c,(tail mode).Executes g (workState (DescriptorEven.vertex 0) width height samples 0 [] S T pairs out count)
      (workState (DescriptorEven.vertex 0) width height samples 0 [] S T pairs
        ((encodeBitList ((tailRecords mode samples height).map encodeVertex)).reverse++out) (count+(tailRecords mode samples height).length)) c ∧
      c≤probeBound height samples := by
  cases mode
  · exact ⟨1,by simpa [tail,tailRecords] using skip_executes g (workState (DescriptorEven.vertex 0) width height samples 0 [] S T pairs out count),by unfold probeBound;omega⟩
  · simpa only [tail,tailRecords,ite_true,DescriptorRectangle.records_length] using probes_executes g true width height samples S T pairs out count

lemma evenProbes_queryFree : evenProbes.QueryFree := seq_queryFree _ _ (push_queryFree _ _)
  (seq_queryFree _ _ (probes_queryFree _) (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree skip_queryFree))
lemma tail_queryFree (mode : Bool) : (tail mode).QueryFree := by cases mode <;> first | exact skip_queryFree | exact probes_queryFree _
end HiddenCircuits.GraphReduction.Runtime.CliqueFront
