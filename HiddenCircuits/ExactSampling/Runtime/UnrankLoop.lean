import HiddenCircuits.ExactSampling.Runtime.UnrankStage

/-! The rank-decreasing graph-deletion driver is a fixed finite while program.
Its runtime theorem is derived from its actual stage executions, not supplied
as a certificate. Empty residual matrices stop the loop before any choice. -/
namespace HiddenCircuits.ExactSampling.Runtime.Unrank
open Complexity OracleBlock BinaryArithmetic DH DHWeights DHPaths
open Approximation Approximation.SelfReduction.Runtime Polynomial
set_option maxHeartbeats 1800000

 noncomputable def positive : OracleBlock 65 := seq (push 0 true) (seq stage (push 3 true))
 noncomputable def body : OracleBlock 65 := branchPop 0 skip (push 0 false) positive
 noncomputable def loop : OracleBlock 65 := whilePop 3 body body
 noncomputable def core : OracleBlock 65 := seq (push 3 true) loop
 noncomputable def finish : OracleBlock 65 := seq (clear 0) (seq (reverseOn 2 0 (by decide)) (push 0 true))
 noncomputable def program : OracleBlock 65 := seq core finish

 theorem empty_graph_word (G : MatrixGraph 0) : GraphInput.encode ⟨0,G⟩=[false] := by
  have hb : G.bits=[] := List.eq_nil_of_length_eq_zero (by simp)
  simp [GraphInput.encode,hb,pairBits]

 theorem positive_graph_word {N : ℕ} (G : MatrixGraph (N+1)) :
    GraphInput.encode ⟨N+1,G⟩=true::(GraphInput.encode ⟨N+1,G⟩).tail := by
  simp [GraphInput.encode,List.replicate_succ,pairBits]

 theorem body_positive (g : BitString→ℕ) {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (x : Fin (count ⟨N+1,G⟩)) (acc : BitString) :
    ∃t,body.Executes g (store (GraphInput.encode ⟨N+1,G⟩) (Computability.encodeNat x.val) acc [])
      (store (GraphResidual.output G (splitIndex G hG x).1)
        (Computability.encodeNat (splitIndex G hG x).2.val)
        ((wordChunk (List.replicate (splitIndex G hG x).1.val true)).reverse++acc) [true]) t ∧
      t≤stageTime.eval (GraphInput.encode ⟨N+1,G⟩).length+8 := by
  obtain ⟨t,ht,hb⟩ := stage_executes g G hG x acc []
  let raw := GraphInput.encode ⟨N+1,G⟩
  let rank := Computability.encodeNat x.val
  let child := GraphResidual.output G (splitIndex G hG x).1
  let rank' := Computability.encodeNat (splitIndex G hG x).2.val
  let acc' := (wordChunk (List.replicate (splitIndex G hG x).1.val true)).reverse++acc
  have h1 : (push (0:Fin 66) true).Executes g
      (Function.update (store raw rank acc []) 0 raw.tail) (store raw rank acc []) 1 := by
    convert push_executes g (0:Fin 66) true (Function.update (store raw rank acc []) 0 raw.tail) using 1
    funext i;fin_cases i <;> simp [store,state]
    exact positive_graph_word G
  have h2 : (push (3:Fin 66) true).Executes g
      (store child rank' acc' []) (store child rank' acc' [true]) 1 := by
    convert push_executes g (3:Fin 66) true _ using 1
    funext i;fin_cases i <;> simp [store,state]
  have hp := seq_executes _ _ g h1 (seq_executes _ _ g ht h2)
  have hh := branchPop_true (0:Fin 66) skip (push 0 false) positive g
    (s:=store raw rank acc []) (rest:=raw.tail) (positive_graph_word G) hp
  refine ⟨_,hh,?_⟩
  omega

 theorem body_empty (g : BitString→ℕ) (acc : BitString) :
    body.Executes g (store [false] [] acc []) (store [false] [] acc []) 3 := by
  apply branchPop_false (0:Fin 66) skip (push 0 false) positive g (rest:=[]) rfl
  convert push_executes g (0:Fin 66) false (store [] [] acc []) using 1
  · funext i;fin_cases i <;> simp [store,state]
  · funext i;fin_cases i <;> simp [store,state]

 theorem encode_choices_cons (j : ℕ) (xs : List ℕ) :
    DHPaths.encode (j::xs)=wordChunk (List.replicate j true)++DHPaths.encode xs := by
  simp [DHPaths.encode,encodeBitList_eq_chunks]

 theorem loop_execution (g : BitString→ℕ) : ∀ (n : ℕ) (G : MatrixGraph n)
    (hG : DistanceHereditaryGraph G.graph) (x : Fin (count ⟨n,G⟩)) (acc : BitString),
    ∃t,WhileExecution (3:Fin 66) body body g
      (store (GraphInput.encode ⟨n,G⟩) (Computability.encodeNat x.val) acc [true])
      (store [false] [] ((DHPaths.encode (choices n G hG x)).reverse++acc) []) t ∧
      t≤(n+1)*(stageTime.eval (GraphInput.encode ⟨n,G⟩).length+10) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      intro G hG x acc
      have hx : x.val=0 := by have hc := DHIndex.empty_count G hG; have hh := x.isLt;omega
      have hp : Function.update (store [false] [] acc [true]) (3:Fin 66) []=store [false] [] acc [] := by
        funext i;fin_cases i <;> simp [store,state]
      have ht : WhileExecution (3:Fin 66) body body g (store [false] [] acc []) (store [false] [] acc []) 1 :=
        WhileExecution.empty _ rfl
      have hh := WhileExecution.one (stack:=(3:Fin 66)) (B:=body) (C:=body)
        (g:=g) (s:=store [false] [] acc [true]) rfl (by rw [hp];exact body_empty g acc) ht
      refine ⟨6,?_,by simp⟩
      simpa [empty_graph_word G,hx,Computability.encodeNat,Computability.encodeNum,choices,DHPaths.encode,encodeBitList] using hh
    | succ N =>
      intro G hG x acc
      let j := (splitIndex G hG x).1
      let child := GraphResidual.graph G j
      let x' := residualRank G hG x
      have hsmall := DHIndex.residual_smaller G j (selected_edge G hG x)
      obtain ⟨c,hc,hcb⟩ := body_positive g G hG x acc
      let acc' := (wordChunk (List.replicate j.val true)).reverse++acc
      obtain ⟨t,ht,htb⟩ := ih _ hsmall child (residual_hereditary G hG j) x' acc'
      have hp : Function.update (store (GraphInput.encode ⟨N+1,G⟩) (Computability.encodeNat x.val) acc [true])
          (3:Fin 66) []=store (GraphInput.encode ⟨N+1,G⟩) (Computability.encodeNat x.val) acc [] := by
        funext i;fin_cases i <;> simp [store,state]
      have ht' : WhileExecution (3:Fin 66) body body g
          (store (GraphResidual.output G j) (Computability.encodeNat (splitIndex G hG x).2.val) acc' [true])
          (store [false] [] ((DHPaths.encode (choices _ child (residual_hereditary G hG j) x')).reverse++acc') []) t := ht
      have hh := WhileExecution.one (stack:=(3:Fin 66)) (B:=body) (C:=body)
        (g:=g) (s:=store (GraphInput.encode ⟨N+1,G⟩) (Computability.encodeNat x.val) acc [true]) rfl
        (by rw [hp];exact hc) ht'
      refine ⟨1+c+1+t,?_,?_⟩
      · simpa only [choices,encode_choices_cons,List.reverse_append,List.append_assoc] using hh
      · have hlen := residual_input_length G j
        have hmono := polynomial_nat_eval_mono stageTime hlen
        change stageTime.eval (GraphInput.encode ⟨_,child⟩).length≤_ at hmono
        have hb : t≤(N+1)*(stageTime.eval (GraphInput.encode ⟨N+1,G⟩).length+10) := by
          apply htb.trans
          gcongr <;> omega
        nlinarith

 theorem core_executes (g : BitString→ℕ) {n : ℕ} (G : MatrixGraph n)
    (hG : DistanceHereditaryGraph G.graph) (x : Fin (count ⟨n,G⟩)) (acc : BitString) :
    ∃t,core.Executes g (store (GraphInput.encode ⟨n,G⟩) (Computability.encodeNat x.val) acc [])
      (store [false] [] ((DHPaths.encode (choices n G hG x)).reverse++acc) []) t ∧
      t≤(n+1)*(stageTime.eval (GraphInput.encode ⟨n,G⟩).length+10)+3 := by
  have hp : (push (3:Fin 66) true).Executes g
      (store (GraphInput.encode ⟨n,G⟩) (Computability.encodeNat x.val) acc [])
      (store (GraphInput.encode ⟨n,G⟩) (Computability.encodeNat x.val) acc [true]) 1 := by
    convert push_executes g (3:Fin 66) true _ using 1
    funext i;fin_cases i <;> simp [store,state]
  obtain ⟨t,ht,hb⟩ := loop_execution g n G hG x acc
  exact ⟨_,seq_executes _ _ g hp (whilePop_executes _ _ _ g ht),by omega⟩

 theorem finish_executes (g : BitString→ℕ) (out : BitString) :
    finish.Executes g (store [false] [] out.reverse []) (store (true::out) [] [] []) (2*out.length+8) := by
  have h1 : (clear (0:Fin 66)).Executes g (store [false] [] out.reverse []) (store [] [] out.reverse []) 2 := by
    convert clear_executes g (0:Fin 66) _ using 1
    funext i;fin_cases i <;> simp [store,state]
  have h2 : (reverseOn (2:Fin 66) 0 (by decide)).Executes g
      (store [] [] out.reverse []) (store out [] [] []) (2*out.length+1) := by
    convert reverseOn_executes g (2:Fin 66) 0 (by decide) (store [] [] out.reverse []) using 1
    · funext i;fin_cases i <;> simp [store,state]
    · simp [store,state]
  have h3 : (push (0:Fin 66) true).Executes g (store out [] [] []) (store (true::out) [] [] []) 1 := by
    convert push_executes g (0:Fin 66) true _ using 1
    funext i;fin_cases i <;> simp [store,state]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1 <;> omega

 noncomputable def time : Polynomial ℕ := (X+1)*(stageTime+10)+10*(X+1)^2+20

 theorem program_executes (g : BitString→ℕ) {n : ℕ} (G : MatrixGraph n)
    (hG : DistanceHereditaryGraph G.graph) (x : Fin (count ⟨n,G⟩)) :
    ∃t,program.Executes g (store (GraphInput.encode ⟨n,G⟩) (Computability.encodeNat x.val) [] [])
      (store (true::DHPaths.encode (choices n G hG x)) [] [] []) t ∧
      t≤time.eval (GraphInput.encode ⟨n,G⟩).length := by
  obtain ⟨a,ha,hab⟩ := core_executes g G hG x []
  simp only [List.append_nil] at ha
  refine ⟨_,seq_executes _ _ g ha (finish_executes g _),?_⟩
  have hl := encoded_choices_length G hG x
  have hn := GraphInput.vertices_le_length ⟨n,G⟩
  have hm := Nat.mul_le_mul_right (stageTime.eval (GraphInput.encode ⟨n,G⟩).length+10) (Nat.add_le_add_right hn 1)
  simp only [time,eval_add,eval_mul,eval_X,eval_one,eval_ofNat,eval_pow]
  nlinarith [Nat.mul_le_mul hn hn]

 theorem program_queryFree : program.QueryFree := by
  have hp : positive.QueryFree := seq_queryFree _ _ (push_queryFree _ _)
    (seq_queryFree _ _ stage_queryFree (push_queryFree _ _))
  have hb : body.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree (push_queryFree _ _) hp
  have hc : core.QueryFree := seq_queryFree _ _ (push_queryFree _ _) (whilePop_queryFree _ _ _ hb hb)
  have hf : finish.QueryFree := seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (push_queryFree _ _))
  exact seq_queryFree _ _ hc hf

end HiddenCircuits.ExactSampling.Runtime.Unrank
