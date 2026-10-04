import HiddenCircuits.DH.BinaryRuntime
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidualPolynomial
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit

/-! Literal finite residual-count emission. Graph bytes are preserved. The
counter is the independently checked total DH binary program, with no graph
promise or matching certificate in any operational premise. -/
namespace HiddenCircuits.ExactSampling.Runtime.WeightCompiler
open Complexity OracleBlock BinaryArithmetic
open Approximation.SelfReduction.Runtime
set_option maxHeartbeats 1800000

abbrev unary (n : ℕ) : BitString := List.replicate n true

/-- 0 graph; 1 final array; 2 candidate; 3 unary clock; 4 adjacency stream;
5 count/residual; 6 reverse array; 7--59 reusable physical scratch. -/
def state (raw out index clock data word acc : BitString) : Store 59 := fun r =>
  if r.val=0 then raw else if r.val=1 then out else if r.val=2 then index
  else if r.val=3 then clock else if r.val=4 then data else if r.val=5 then word
  else if r.val=6 then acc else []

def store (raw out : BitString) : Store 59 := state raw out [] [] [] [] []

def residualPorts : Fin 19 ↪ Fin 60 where
  toFun i := if i.val=0 then 5 else if i.val=1 then 2 else ⟨i.val+5,by omega⟩
  inj' := by decide +kernel

def counterPorts : Fin 54 ↪ Fin 60 where
  toFun i := if i.val=0 then 5 else ⟨i.val+6,by omega⟩
  inj' := by decide +kernel

def emitPorts : Fin 2 ↪ Fin 60 := ⟨fun i => if i.val=0 then 5 else 6,by decide +kernel⟩
noncomputable def emit : OracleBlock 59 := rename wordEmit emitPorts
noncomputable def counter : OracleBlock 59 := rename DH.BinaryRuntime.program counterPorts
noncomputable def residual : OracleBlock 59 := GraphResidual.programOn residualPorts
noncomputable def copyGraph : OracleBlock 59 := copyOn 0 5 7 (by decide) (by decide) (by decide)
noncomputable def countEdge : OracleBlock 59 := seq copyGraph (seq residual counter)
noncomputable def choose : OracleBlock 59 := branchPop 4 skip skip countEdge
noncomputable def body : OracleBlock 59 := seq choose (seq emit (push 2 true))
noncomputable def loop : OracleBlock 59 := whilePop 3 body body

/-- These words are canonical for every input, independently of DH semantics. -/
def weightWord {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1)) : BitString :=
  if G.edge 0 j then DH.BinaryRuntime.function (GraphResidual.output G j) else []

lemma weightWord_canonical {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1)) :
    Computability.encodeNat (Computability.decodeNat (weightWord G j))=weightWord G j := by
  cases he : G.edge 0 j
  · simp only [weightWord,he,Bool.false_eq_true,ite_false];rfl
  · simp only [weightWord,he,ite_true,DH.BinaryRuntime.function,DH.Runtime.BinaryModel.function,Computability.decode_encodeNat]

lemma emit_executes (g : BitString→ℕ) (raw out index clock data word acc : BitString) :
    emit.Executes g (state raw out index clock data word acc)
      (state raw out index clock data [] ((wordChunk word).reverse++acc)) (6*word.length+7) := by
  apply rename_executes_to wordEmit emitPorts g (wordEmit_executes g word acc)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h5 : i.val≠5 := by intro h;apply hi 0;apply Fin.ext;exact h.symm
    have h6 : i.val≠6 := by intro h;apply hi 1;apply Fin.ext;exact h.symm
    simp [state,h5,h6]

lemma copyGraph_executes (g : BitString→ℕ) (raw out index clock data acc : BitString) :
    copyGraph.Executes g (state raw out index clock data [] acc)
      (state raw out index clock data raw acc) (5*raw.length+2) := by
  convert copyOn_executes g (0:Fin 60) 5 7 (by decide) (by decide) (by decide)
    (state raw out index clock data [] acc) rfl using 1
  funext i;fin_cases i <;> simp [state]

lemma residual_executes (g : BitString→ℕ) {N : ℕ} (G : MatrixGraph (N+1))
    (j : Fin (N+1)) (out clock data acc : BitString) :
    ∃t,residual.Executes g
      (state (GraphInput.encode ⟨N+1,G⟩) out (unary j.val) clock data (GraphInput.encode ⟨N+1,G⟩) acc)
      (state (GraphInput.encode ⟨N+1,G⟩) out (unary j.val) clock data (GraphResidual.output G j) acc) t ∧
      t≤GraphResidual.timeBound (N+1) := by
  obtain ⟨t,ht,hb⟩ := GraphResidual.programOn_executes residualPorts g
    (state (GraphInput.encode ⟨N+1,G⟩) out (unary j.val) clock data (GraphInput.encode ⟨N+1,G⟩) acc) G j
    (by funext i;fin_cases i <;> simp [state,residualPorts,GraphResidual.inputStore,GraphResidual.state])
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext i;fin_cases i <;> simp [state,residualPorts]

lemma counter_executes (g : BitString→ℕ) (raw out index clock data word acc : BitString) :
    ∃t,counter.Executes g (state raw out index clock data word acc)
      (state raw out index clock data (DH.BinaryRuntime.function word) acc) t ∧
      t≤DH.BinaryRuntime.time.eval word.length := by
  obtain ⟨t,ht,hb⟩ := DH.BinaryRuntime.executes g word
  refine ⟨t,?_,hb⟩
  apply rename_executes_to DH.BinaryRuntime.program counterPorts g ht
  · funext i;fin_cases i <;> simp [state,counterPorts]
  · funext i;fin_cases i <;> simp [state,counterPorts]
  · intro i hi
    have h5 : i.val≠5 := by intro h;apply hi 0;apply Fin.ext;exact h.symm
    simp [state,h5]

lemma residual_length {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1)) :
    (GraphResidual.output G j).length≤(GraphInput.encode ⟨N+1,G⟩).length := by
  have hc : (GraphResidual.retained j).card≤N+1 := by simpa using (GraphResidual.retained j).card_le_univ
  simp only [GraphResidual.output,GraphInput.encode,pairBits_length,List.length_replicate,MatrixGraph.bits_length]
  gcongr

lemma function_length (raw : BitString) :
    (DH.BinaryRuntime.function raw).length≤raw.length+DH.BinaryRuntime.time.eval raw.length := by
  obtain ⟨t,ht,hb⟩ := DH.BinaryRuntime.executes (fun _=>0) raw
  have hi : ∀q : Fin 54,(Function.update (fun _=>[]) 0 raw q).length≤raw.length := by
    intro q
    by_cases h:q=0
    · subst q;exact Nat.le_refl _
    · rw [Function.update_of_ne h];exact Nat.zero_le _
  have hh := ht.stack_bound hi (0:Fin 54)
  change (DH.BinaryRuntime.function raw).length≤raw.length+t at hh
  omega

noncomputable def countBound (L : ℕ) : ℕ := 5*L+GraphResidual.timeBound L+DH.BinaryRuntime.time.eval L+6

lemma countEdge_executes (g : BitString→ℕ) {N : ℕ} (G : MatrixGraph (N+1))
    (j : Fin (N+1)) (out clock data acc : BitString) :
    ∃t,countEdge.Executes g
      (state (GraphInput.encode ⟨N+1,G⟩) out (unary j.val) clock data [] acc)
      (state (GraphInput.encode ⟨N+1,G⟩) out (unary j.val) clock data
        (DH.BinaryRuntime.function (GraphResidual.output G j)) acc) t ∧
      t≤countBound (GraphInput.encode ⟨N+1,G⟩).length := by
  obtain ⟨a,ha,hab⟩ := residual_executes g G j out clock data acc
  obtain ⟨b,hb,hbb⟩ := counter_executes g (GraphInput.encode ⟨N+1,G⟩) out (unary j.val) clock data (GraphResidual.output G j) acc
  refine ⟨_,seq_executes _ _ g (copyGraph_executes g _ out _ clock data acc) (seq_executes _ _ g ha hb),?_⟩
  have hn := GraphResidual.timeBound_mono (GraphInput.vertices_le_length ⟨N+1,G⟩)
  have hm := polynomial_nat_eval_mono DH.BinaryRuntime.time (residual_length G j)
  dsimp only at hn hm
  unfold countBound
  omega

lemma emit_queryFree : emit.QueryFree := rename_queryFree _ _ wordEmit_queryFree
lemma counter_queryFree : counter.QueryFree := rename_queryFree _ _ DH.BinaryRuntime.queryFree
lemma residual_queryFree : residual.QueryFree := GraphResidual.programOn_queryFree _
lemma copyGraph_queryFree : copyGraph.QueryFree := copyOn_queryFree _ _ _ _ _ _
lemma countEdge_queryFree : countEdge.QueryFree := seq_queryFree _ _ copyGraph_queryFree
  (seq_queryFree _ _ residual_queryFree counter_queryFree)
lemma choose_queryFree : choose.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree countEdge_queryFree
lemma body_queryFree : body.QueryFree := seq_queryFree _ _ choose_queryFree (seq_queryFree _ _ emit_queryFree (push_queryFree _ _))
lemma loop_queryFree : loop.QueryFree := whilePop_queryFree _ _ _ body_queryFree body_queryFree
end HiddenCircuits.ExactSampling.Runtime.WeightCompiler
