import HiddenCircuits.Circuit.Runtime.DyadicScalar
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsLoop
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorRuntime
import HiddenCircuits.Complexity.OracleMove
import HiddenCircuits.Circuit.GeometricIntegerWeights

/-! Physically emit the powers-of-two node list by one
literal shift per node, in canonical order, with quadratic charged runtime. -/
namespace HiddenCircuits.Circuit.Runtime.GeometricNodes
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial

def node (k : ℕ) : BitString := signedBits ((2:ℤ)^k)
def nodesFrom (k m : ℕ) : List ℤ := (List.range' k m).map (fun j=>(2:ℤ)^j)
def nodes (d : ℕ) : List ℤ := nodesFrom 0 (d+1)
lemma node_length (k : ℕ) : (node k).length=k+2 := by simp [node,DyadicScalar.signed_powerBits,DyadicScalar.powerBits]
lemma node_succ (k : ℕ) : node (k+1)=false::node k := by simp [node,DyadicScalar.signed_powerBits,DyadicScalar.powerBits,List.replicate_succ]
lemma nodes_geometric (d : ℕ) : nodes d=(List.finRange (d+1)).map geometricIntegerNode := by
  rw [nodes,nodesFrom,←List.range_eq_range',←List.map_coe_finRange_eq_range]
  simp only [List.map_map]
  rfl
lemma stream_bound (d : ℕ) : (encodeBitList ((nodes d).map signedBits)).length≤(d+1)*(2*(d+2)+2) := by
  apply (encodedWords_length_le _ (d+2) ?_).trans_eq
  · simp [nodes,nodesFrom]
  · intro w hw
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hw
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hz
    have hj' : j<d+1 := List.mem_range.mp (by simpa only [←List.range_eq_range'] using hj)
    exact (node_length j).le.trans (by omega)

def state (d k clock : ℕ) (word out : BitString) : Store 5 := fun i =>
  if i.val=0 then List.replicate d true else if i.val=1 then node k else if i.val=2 then List.replicate clock true
  else if i.val=3 then word else if i.val=4 then out else []
def inputStore (d : ℕ) : Store 5 := Function.update (fun _=>[]) 0 (List.replicate d true)
def outputStore (d : ℕ) (out : BitString) : Store 5 := fun i =>
  if i.val=0 then List.replicate d true else if i.val=4 then out else []
def emitEmbedding : Fin 2 ↪ Fin 6 where
  toFun i := if i.val=0 then 3 else 4
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def emit : OracleBlock 5 := rename wordEmit emitEmbedding
noncomputable def body : OracleBlock 5 := seq (copyOn 1 3 5 (by decide) (by decide) (by decide)) (seq emit (push 1 false))
noncomputable def loop : OracleBlock 5 := whilePop 2 body body
noncomputable def setup : OracleBlock 5 := seq (copyOn 0 2 5 (by decide) (by decide) (by decide))
  (seq (push 2 true) (prepend 1 [false,true]))
noncomputable def finish : OracleBlock 5 := seq (clear 1) (seq (reverseOn 4 3 (by decide)) (moveOn 3 4 5 (by decide) (by decide) (by decide)))
noncomputable def program : OracleBlock 5 := seq setup (seq loop finish)
noncomputable def time : Polynomial ℕ := 50*(X+2)^2

lemma body_executes (g : BitString → ℕ) (d k clock : ℕ) (out : BitString) :
    body.Executes g (state d k clock [] out)
      (state d (k+1) clock [] ((wordChunk (node k)).reverse++out)) (11*(k+2)+14) := by
  have hc : (copyOn (1:Fin 6) 3 5 (by decide) (by decide) (by decide)).Executes g
      (state d k clock [] out) (state d k clock (node k) out) (5*(k+2)+2) := by
    convert copyOn_executes g (1:Fin 6) 3 5 (by decide) (by decide) (by decide) (state d k clock [] out) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state,node_length]
  have he : emit.Executes g (state d k clock (node k) out)
      (state d k clock [] ((wordChunk (node k)).reverse++out)) (6*(k+2)+7) := by
    have h:=wordEmit_executes g (node k) out
    rw [node_length] at h
    apply rename_executes_to _ emitEmbedding g h
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim
  have hp : (push (1:Fin 6) false).Executes g
      (state d k clock [] ((wordChunk (node k)).reverse++out))
      (state d (k+1) clock [] ((wordChunk (node k)).reverse++out)) 1 := by
    convert push_executes g (1:Fin 6) false (state d k clock [] ((wordChunk (node k)).reverse++out)) using 1
    funext i;fin_cases i <;> simp [state,node_succ]
  convert seq_executes _ _ g hc (seq_executes _ _ g he hp) using 1 <;> omega

lemma loop_execution (g : BitString → ℕ) (d k m : ℕ) (out : BitString) :
    ∃c,WhileExecution (2:Fin 6) body body g (state d k m [] out)
      (state d (k+m) 0 [] ((encodeBitList ((nodesFrom k m).map signedBits)).reverse++out)) c ∧
      c≤m*(11*(k+m+1)+16)+1 := by
  induction m generalizing k out with
  | zero => exact ⟨1,by simpa [nodesFrom] using
      (WhileExecution.empty (stack:=(2:Fin 6)) (B:=body) (C:=body) (g:=g) (state d k 0 [] out) rfl),by simp⟩
  | succ m ih =>
    have hb:=body_executes g d k m out
    have hu : Function.update (state d k (m+1) [] out) (2:Fin 6) (List.replicate m true)=state d k m [] out := by
      funext i;fin_cases i <;> rfl
    rw [←hu] at hb
    obtain ⟨c,hc,hcb⟩:=ih (k+1) ((wordChunk (node k)).reverse++out)
    have h:=WhileExecution.one (stack:=(2:Fin 6)) (B:=body) (C:=body) (g:=g) rfl hb hc
    refine ⟨1+(11*(k+2)+14)+1+c,?_,?_⟩
    · convert h using 1
      simp only [nodesFrom,List.range'_succ,List.map_cons,encodeBitList_eq_chunks,List.flatMap_cons,List.reverse_append,node,List.append_assoc]
      congr 1 <;> omega
    · nlinarith

lemma setup_executes (g : BitString → ℕ) (d : ℕ) : setup.Executes g (inputStore d) (state d 0 (d+1) [] []) (5*d+14) := by
  let s1 := Function.update (inputStore d) (2:Fin 6) (List.replicate d true)
  let s2 := Function.update (inputStore d) (2:Fin 6) (List.replicate (d+1) true)
  have hc : (copyOn (0:Fin 6) 2 5 (by decide) (by decide) (by decide)).Executes g (inputStore d) s1 (5*d+2) := by
    simpa [inputStore,s1] using copyOn_executes g (0:Fin 6) 2 5 (by decide) (by decide) (by decide) (inputStore d) rfl
  have hp : (push (2:Fin 6) true).Executes g s1 s2 1 := by
    simpa [s1,s2,List.replicate_succ] using push_executes g (2:Fin 6) true s1
  have hi : (prepend (1:Fin 6) [false,true]).Executes g s2 (state d 0 (d+1) [] []) 7 := by
    convert prepend_executes g (1:Fin 6) [false,true] s2 using 1
    funext i;fin_cases i <;> simp [s2,inputStore,state,node,signedBits,negative,Computability.encodeNat] <;> rfl
  convert seq_executes _ _ g hc (seq_executes _ _ g hp hi) using 1 <;> omega

lemma finish_executes (g : BitString → ℕ) (d k : ℕ) (out : BitString) :
    finish.Executes g (state d k 0 [] out.reverse) (outputStore d out) (k+8*out.length+13) := by
  let s1 := Function.update (state d k 0 [] out.reverse) (1:Fin 6) []
  let s2 := Function.update (outputStore d []) (3:Fin 6) out
  have hc : (clear (1:Fin 6)).Executes g (state d k 0 [] out.reverse) s1 (k+3) := by
    simpa [state,node_length,s1,Nat.add_assoc] using clear_executes g (1:Fin 6) (state d k 0 [] out.reverse)
  have hr : (reverseOn (4:Fin 6) 3 (by decide)).Executes g s1 s2 (2*out.length+1) := by
    convert reverseOn_executes g (4:Fin 6) 3 (by decide) s1 using 1
    · funext i;fin_cases i <;> simp [s1,s2,state,outputStore]
    · simp [s1,state]
  have hm : (moveOn (3:Fin 6) 4 5 (by decide) (by decide) (by decide)).Executes g s2 (outputStore d out) (6*out.length+5) := by
    convert moveOn_executes g (3:Fin 6) 4 5 (by decide) (by decide) (by decide) s2 (by simp [s2,outputStore]) using 1
    funext i;fin_cases i <;> simp [s2,outputStore]
  convert seq_executes _ _ g hc (seq_executes _ _ g hr hm) using 1 <;> omega

theorem program_executes (g : BitString → ℕ) (d : ℕ) :
    ∃c,program.Executes g (inputStore d) (outputStore d (encodeBitList ((nodes d).map signedBits))) c ∧ c≤time.eval d := by
  have hs:=setup_executes g d
  obtain ⟨c,hc,hcb⟩:=loop_execution g d 0 (d+1) []
  simp only [Nat.zero_add,List.append_nil] at hc
  have hf:=finish_executes g d (d+1) (encodeBitList ((nodes d).map signedBits))
  refine ⟨_,seq_executes _ _ g hs (seq_executes _ _ g (whilePop_executes _ _ _ g hc) hf),?_⟩
  have hl:=stream_bound d
  simp only [time,eval_mul,eval_pow,eval_add,eval_X,eval_ofNat]
  nlinarith

lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (push_queryFree _ _) (prepend_queryFree _ _)))
  (seq_queryFree _ _ (whilePop_queryFree _ _ _
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (rename_queryFree _ _ wordEmit_queryFree) (push_queryFree _ _)))
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (rename_queryFree _ _ wordEmit_queryFree) (push_queryFree _ _))))
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (moveOn_queryFree _ _ _ _ _ _))))
end HiddenCircuits.Circuit.Runtime.GeometricNodes
