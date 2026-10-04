import HiddenCircuits.GraphReduction.Runtime.DescriptorOdd

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorOdd
open Complexity OracleBlock BinaryArithmetic DescriptorFront WordGraph
set_option maxHeartbeats 800000
noncomputable def loop : OracleBlock 19 := whilePop 16 body body
noncomputable def program : OracleBlock 19 := seq loop (clear 1)

@[simp] lemma records_length {p : ℕ} (width layer : ℕ) (ps : List (CutPair p)) : (records width layer ps).length=width*ps.length := by
  induction ps generalizing layer with
  | nil => simp [records]
  | cons P ps ih => simp [records,ih];ring

lemma stream_update (v : VertexRecord) (width height samples : ℕ) (S T pairs rest out : BitString) (count : ℕ) :
    Function.update (workState v width height samples 0 [] S T pairs out count) 16 rest=
      workState v width height samples 0 [] S T rest out count := by
  funext i;fin_cases i <;> rfl

theorem loop_execution {p : ℕ} (g : BitString → ℕ) (layer : ℕ) (ps : List (CutPair p))
    (height samples : ℕ) (S T out : BitString) (count : ℕ) :
    ∃c,WhileExecution (16:Fin 20) body body g
      (workState (DescriptorEven.vertex layer) (2*p) height samples 0 [] S T (pairStream ps) out count)
      (workState (DescriptorEven.vertex (layer+ps.length)) (2*p) height samples 0 [] S T []
        ((encodeBitList ((records (2*p) layer ps).map encodeVertex)).reverse++out) (count+2*p*ps.length)) c ∧
      c≤ps.length*((2*p)*(20*(layer+ps.length)+34*(2*p)+125)+8*(2*p)+127)+1 := by
  induction ps generalizing layer out count with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa [records] using WhileExecution.empty (stack:=(16:Fin 20)) (B:=body) (C:=body) (g:=g)
      (workState (DescriptorEven.vertex layer) (2*p) height samples 0 [] S T [] out count) rfl
  | cons P ps ih =>
    obtain ⟨a,ha,hab⟩ := body_executes g P layer height samples S T (pairStream ps) out count
    obtain ⟨b,hb,hbb⟩ := ih (layer+1)
      ((encodeBitList ((DescriptorRow.records (vertex layer P) (2*p)).map encodeVertex)).reverse++out) (count+2*p)
    have hs := WhileExecution.one (stack:=(16:Fin 20)) (B:=body) (C:=body) (g:=g)
      (s:=workState (DescriptorEven.vertex layer) (2*p) height samples 0 [] S T (pairStream (P::ps)) out count) rfl
      (by rw [stream_update];exact ha) hb
    refine ⟨1+a+1+b,?_,?_⟩
    · have hl : layer+(ps.length+1)=layer+1+ps.length := by omega
      have hn : count+2*p*(ps.length+1)=count+2*p+2*p*ps.length := by ring
      simpa only [records,List.map_append,encodeBitList_append,List.reverse_append,List.append_assoc,List.length_cons,hl,hn] using hs
    · have hm : (2*p)*(20*layer+34*(2*p)+125)≤(2*p)*(20*(layer+(ps.length+1))+34*(2*p)+125) := by gcongr;omega
      have hl : layer+1+ps.length=layer+(ps.length+1) := by omega
      rw [hl] at hbb
      simp only [List.length_cons]
      nlinarith

theorem program_executes {p : ℕ} (g : BitString → ℕ) (ps : List (CutPair p))
    (height samples : ℕ) (S T out : BitString) (count : ℕ) :
    ∃c,program.Executes g (workState (DescriptorEven.vertex 0) (2*p) height samples 0 [] S T (pairStream ps) out count)
      (workState (DescriptorEven.vertex 0) (2*p) height samples 0 [] S T []
        ((encodeBitList ((records (2*p) 0 ps).map encodeVertex)).reverse++out) (count+2*p*ps.length)) c ∧
      c≤ps.length*((2*p)*(20*ps.length+34*(2*p)+125)+8*(2*p)+128)+4 := by
  obtain ⟨c,hc,hb⟩ := loop_execution g 0 ps height samples S T out count
  simp only [Nat.zero_add] at hc hb
  have hz := DescriptorEven.clear_layer g (DescriptorEven.vertex ps.length) (2*p) height samples 0 S T []
    ((encodeBitList ((records (2*p) 0 ps).map encodeVertex)).reverse++out) (count+2*p*ps.length)
  refine ⟨_,seq_executes _ _ g (whilePop_executes _ _ _ g hc) hz,?_⟩
  change c+(ps.length+1)+2≤_
  nlinarith
end HiddenCircuits.GraphReduction.Runtime.DescriptorOdd
