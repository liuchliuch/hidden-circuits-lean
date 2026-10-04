import HiddenCircuits.ExactSampling.Runtime.WeightInterface
import HiddenCircuits.ExactSampling.Runtime.WeightedSelectCorrectness
import HiddenCircuits.ExactSampling.Runtime.CountBounds

/-! One fixed 66-stack exact self-reduction stage. The graph remains labeled by
its inherited ordering; the selected local vertex is emitted into a reverse
self-delimiting matching path. No count oracle or arithmetic primitive occurs. -/
namespace HiddenCircuits.ExactSampling.Runtime.Unrank
open Complexity OracleBlock BinaryArithmetic DH DHWeights DHPaths
open Approximation Approximation.SelfReduction.Runtime
open Polynomial
set_option maxHeartbeats 1800000

 def state (graph rank acc clock chosen flag weights : BitString) : Store 65 := fun i =>
  if i.val=0 then graph else if i.val=1 then rank else if i.val=2 then acc
  else if i.val=3 then clock else if i.val=4 then chosen else if i.val=5 then flag
  else if i.val=6 then weights else []

 def store (graph rank acc clock : BitString) : Store 65 := state graph rank acc clock [] [] []

 def weightPorts : Fin 60 ↪ Fin 66 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 6 else ⟨i.val+5,by omega⟩
  inj' := by decide +kernel
 def selectPorts : Fin 11 ↪ Fin 66 := ⟨fun i => ![6,1,4,7,8,9,10,11,12,13,5] i,by decide +kernel⟩
 def residualPorts : Fin 19 ↪ Fin 66 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 4 else ⟨i.val+5,by omega⟩
  inj' := by decide +kernel
 def emitPorts : Fin 2 ↪ Fin 66 := ⟨fun i => if i.val=0 then 4 else 2,by decide +kernel⟩

 noncomputable def weights : OracleBlock 65 := WeightCompiler.programOn weightPorts
 noncomputable def select : OracleBlock 65 := WeightedSelect.programOn selectPorts
 noncomputable def residual : OracleBlock 65 := GraphResidual.programOn residualPorts
 noncomputable def emit : OracleBlock 65 := rename wordEmit emitPorts
 noncomputable def stage : OracleBlock 65 := seq weights (seq select (seq (clear 5) (seq residual emit)))

 def weightArray {N : ℕ} (G : MatrixGraph (N+1)) : BitString :=
  encodeBitList ((List.ofFn (weight G)).map Computability.encodeNat)

 theorem weights_executes (g : BitString→ℕ) {N : ℕ} (G : MatrixGraph (N+1))
    (rank acc clock : BitString) :
    ∃t,weights.Executes g (store (GraphInput.encode ⟨N+1,G⟩) rank acc clock)
      (state (GraphInput.encode ⟨N+1,G⟩) rank acc clock [] [] (weightArray G)) t ∧
      t≤WeightCompiler.timePolynomial.eval (GraphInput.encode ⟨N+1,G⟩).length := by
  obtain ⟨t,ht,hb⟩ := WeightCompiler.programOn_executes weightPorts g
    (store (GraphInput.encode ⟨N+1,G⟩) rank acc clock) ⟨N+1,G⟩
    (by funext i;fin_cases i <;> rfl)
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext i;fin_cases i <;> simp [store,state,weightPorts,WeightCompiler.output_positive,weightArray,List.map_ofFn,Function.comp_def]

 theorem select_executes (g : BitString→ℕ) {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (x : Fin (count ⟨N+1,G⟩)) (acc clock : BitString) :
    ∃t,select.Executes g
      (state (GraphInput.encode ⟨N+1,G⟩) (Computability.encodeNat x.val) acc clock [] [] (weightArray G))
      (state (GraphInput.encode ⟨N+1,G⟩) (Computability.encodeNat (splitIndex G hG x).2.val)
        acc clock (List.replicate (splitIndex G hG x).1.val true) [true] []) t ∧
      t≤(N+2)*(60*((weightArray G).length+Nat.size x.val+1)+60) := by
  obtain ⟨t,ht,hb⟩ := WeightedSelect.program_exact_choice g G hG x
  refine ⟨t,?_,hb⟩
  apply rename_executes_to WeightedSelect.program selectPorts g ht
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h1 : i.val≠1 := by intro h;exact hi 1 (Fin.ext h.symm)
    have h4 : i.val≠4 := by intro h;exact hi 2 (Fin.ext h.symm)
    have h5 : i.val≠5 := by intro h;exact hi 10 (Fin.ext h.symm)
    have h6 : i.val≠6 := by intro h;exact hi 0 (Fin.ext h.symm)
    simp [state,h1,h4,h5,h6]

 theorem residual_executes (g : BitString→ℕ) {N : ℕ} (G : MatrixGraph (N+1))
    (j : Fin (N+1)) (rank acc clock : BitString) :
    ∃t,residual.Executes g
      (state (GraphInput.encode ⟨N+1,G⟩) rank acc clock (List.replicate j.val true) [] [])
      (state (GraphResidual.output G j) rank acc clock (List.replicate j.val true) [] []) t ∧
      t≤GraphResidual.timeBound (N+1) := by
  obtain ⟨t,ht,hb⟩ := GraphResidual.programOn_executes residualPorts g
    (state (GraphInput.encode ⟨N+1,G⟩) rank acc clock (List.replicate j.val true) [] []) G j
    (by funext i;fin_cases i <;> rfl)
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext i;fin_cases i <;> simp [state,residualPorts]

 theorem emit_executes (g : BitString→ℕ) (graph rank acc clock word : BitString) :
    emit.Executes g (state graph rank acc clock word [] [])
      (store graph rank ((wordChunk word).reverse++acc) clock) (6*word.length+7) := by
  apply rename_executes_to wordEmit emitPorts g (wordEmit_executes g word acc)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h2 : i.val≠2 := by intro h;exact hi 1 (Fin.ext h.symm)
    have h4 : i.val≠4 := by intro h;exact hi 0 (Fin.ext h.symm)
    simp [store,state,h2,h4]

 noncomputable def stageTime : Polynomial ℕ := WeightCompiler.timePolynomial+
  (X+1)*(60*(2*X+WeightCompiler.timePolynomial+DH.BinaryRuntime.time+1)+60)+
  GraphResidual.timePolynomial+10*X+30

 theorem stage_executes (g : BitString→ℕ) {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (x : Fin (count ⟨N+1,G⟩)) (acc clock : BitString) :
    ∃t,stage.Executes g (store (GraphInput.encode ⟨N+1,G⟩) (Computability.encodeNat x.val) acc clock)
      (store (GraphResidual.output G (splitIndex G hG x).1)
        (Computability.encodeNat (splitIndex G hG x).2.val)
        ((wordChunk (List.replicate (splitIndex G hG x).1.val true)).reverse++acc) clock) t ∧
      t≤stageTime.eval (GraphInput.encode ⟨N+1,G⟩).length := by
  let j := (splitIndex G hG x).1
  let r := Computability.encodeNat (splitIndex G hG x).2.val
  let graph := GraphInput.encode ⟨N+1,G⟩
  obtain ⟨a,ha,hab⟩ := weights_executes g G (Computability.encodeNat x.val) acc clock
  obtain ⟨b,hb,hbb⟩ := select_executes g G hG x acc clock
  have hc : (clear (5:Fin 66)).Executes g
      (state graph r acc clock (List.replicate j.val true) [true] [])
      (state graph r acc clock (List.replicate j.val true) [] []) 2 := by
    convert clear_executes g (5:Fin 66) _ using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨d,hd,hdb⟩ := residual_executes g G j r acc clock
  have he := emit_executes g (GraphResidual.output G j) r acc clock (List.replicate j.val true)
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc (seq_executes _ _ g hd he))),?_⟩
  have hn := GraphInput.vertices_le_length ⟨N+1,G⟩
  change N+1≤graph.length at hn
  have hj := j.isLt
  have hr := rank_size_bound ⟨N+1,G⟩ hG x
  have hw := WeightCompiler.output_length ⟨N+1,G⟩
  rw [WeightCompiler.output_positive] at hw
  change (encodeBitList (List.ofFn (fun j => Computability.encodeNat (weight G j)))).length≤_ at hw
  have hw' : (weightArray G).length≤graph.length+WeightCompiler.timePolynomial.eval graph.length := by
    simpa [weightArray,List.map_ofFn,Function.comp_def,graph] using hw
  have hd' : d≤GraphResidual.timePolynomial.eval graph.length :=
    hdb.trans (by rw [GraphResidual.timePolynomial_eval]; exact GraphResidual.timeBound_mono hn)
  have hs : b≤(graph.length+1)*(60*(2*graph.length+WeightCompiler.timePolynomial.eval graph.length+
      DH.BinaryRuntime.time.eval graph.length+1)+60) := by
    apply hbb.trans
    apply Nat.mul_le_mul
    · exact Nat.add_le_add_right hn 1
    · dsimp only [graph] at *;omega
  simp only [List.length_replicate] at *
  simp only [stageTime,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
  dsimp only [graph,r,j] at *
  omega

 theorem stage_queryFree : stage.QueryFree := seq_queryFree _ _ (WeightCompiler.programOn_queryFree _)
  (seq_queryFree _ _ (WeightedSelect.programOn_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (GraphResidual.programOn_queryFree _) (rename_queryFree _ _ wordEmit_queryFree))))

end HiddenCircuits.ExactSampling.Runtime.Unrank
