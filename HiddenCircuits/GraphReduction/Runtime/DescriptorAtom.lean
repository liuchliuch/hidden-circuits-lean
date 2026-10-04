import HiddenCircuits.GraphReduction.Runtime.DescriptorAtomHelpers

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorAtom
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

theorem state_out (v : VertexRecord) (out next : BitString) (count : ℕ) :
    Function.update (state v out count) (4:Fin 8) next=state v next count := by
  funext i;fin_cases i <;> simp [state]

theorem push_out_executes (oracle : BitString → ℕ) (v : VertexRecord) (out : BitString) (count : ℕ) (b : Bool) :
    (push (4:Fin 8) b).Executes oracle (state v out count) (state v (b::out) count) 1 := by
  simpa only [show state v out count 4=out from rfl,state_out] using push_executes oracle (4:Fin 8) b (state v out count)
noncomputable def delimiter : OracleBlock 7 := seq (push 4 true) (push 4 false)
theorem delimiter_executes (oracle : BitString → ℕ) (v : VertexRecord) (out : BitString) (count : ℕ) :
    delimiter.Executes oracle (state v out count) (state v (false::true::out) count) 4 :=
  seq_executes _ _ oracle (push_out_executes oracle v out count true) (push_out_executes oracle v (true::out) count false)

theorem field_executes (oracle : BitString → ℕ) (v : VertexRecord) (out : BitString) (count : ℕ)
    (source : Fin 8) (h4 : source≠4) (h6 : source≠6) (h7 : source≠7) (width n : ℕ)
    (hs : state v out count source=List.replicate n true) :
    (unary source h6 h7 width).Executes oracle (state v out count)
      (state v (List.replicate (width*n) true++out) count) ((3*width+8)*n+5) := by
  simpa only [show state v out count 4=out from rfl,state_out] using
    unary_executes oracle source h4 h6 h7 width n (state v out count) hs rfl rfl

noncomputable def program : OracleBlock 7 := seq (push 4 true) (seq tags
  (seq (unary 1 (by decide) (by decide) 4) (seq delimiter
    (seq (unary 2 (by decide) (by decide) 4) (seq delimiter
      (seq (unary 3 (by decide) (by decide) 2) (seq (push 4 false) (push 5 true))))))))

theorem program_executes (oracle : BitString → ℕ) (v : VertexRecord) (out : BitString) (count : ℕ) :
    program.Executes oracle (state v out count)
      (state v ((wordChunk (encodeVertex v)).reverse++out) (count+1))
      (20*v.layer+20*v.track+14*v.cut.index+113) := by
  let a := (wordPayload (tagBits v)).reverse++true::out
  let b := List.replicate (4*v.layer) true++a
  let c := List.replicate (4*v.track) true++false::true::b
  let d := List.replicate (2*v.cut.index) true++false::true::c
  have h₁ := push_out_executes oracle v out count true
  have h₂ := tags_executes oracle v (true::out) count
  have h₃ := field_executes oracle v a count 1 (by decide) (by decide) (by decide) 4 v.layer rfl
  have h₄ := delimiter_executes oracle v b count
  have h₅ := field_executes oracle v (false::true::b) count 2 (by decide) (by decide) (by decide) 4 v.track rfl
  have h₆ := delimiter_executes oracle v c count
  have h₇ := field_executes oracle v (false::true::c) count 3 (by decide) (by decide) (by decide) 2 v.cut.index rfl
  have h₈ := push_out_executes oracle v d count false
  have h₉ : (push (5:Fin 8) true).Executes oracle (state v (false::d) count) (state v (false::d) (count+1)) 1 := by
    convert push_executes oracle (5:Fin 8) true (state v (false::d) count) using 1
    funext i;fin_cases i <;> simp [state,List.replicate_succ]
  have hh := seq_executes _ _ oracle h₁ (seq_executes _ _ oracle h₂ (seq_executes _ _ oracle h₃
    (seq_executes _ _ oracle h₄ (seq_executes _ _ oracle h₅ (seq_executes _ _ oracle h₆
      (seq_executes _ _ oracle h₇ (seq_executes _ _ oracle h₈ h₉)))))))
  convert hh using 1
  · simp [vertex_chunk,List.reverse_append,List.append_assoc,a,b,c,d]
  · ring

theorem program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ tags_queryFree
    (seq_queryFree _ _ (unary_queryFree _ _ _ _)
      (seq_queryFree _ _ (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))
        (seq_queryFree _ _ (unary_queryFree _ _ _ _)
          (seq_queryFree _ _ (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))
            (seq_queryFree _ _ (unary_queryFree _ _ _ _)
              (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))))))))
end HiddenCircuits.GraphReduction.Runtime.DescriptorAtom
