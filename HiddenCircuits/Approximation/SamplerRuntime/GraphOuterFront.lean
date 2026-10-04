import HiddenCircuits.Approximation.SamplerRuntime.GraphParserProgram
import HiddenCircuits.Approximation.SamplerRuntime.OuterPrepare
import HiddenCircuits.Approximation.SamplerRuntime.GraphFunctional

/-! Total raw-pair preparation and graph parsing on the actual
78-stack general sampler, including malformed input and precision rejection. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.GraphOuter
open Complexity Complexity.OracleBlock Polynomial GraphVerifier GraphVerifier.Runtime
open Outer (graph tape inputSize preValid unary)
set_option maxHeartbeats 2000000

def store (a b c d e f g h i j : BitString) : Store 77 := fun r =>
  if r.val=0 then a else if r.val=1 then b else if r.val=2 then c else if r.val=3 then d
  else if r.val=4 then e else if r.val=5 then f else if r.val=6 then g else if r.val=7 then h
  else if r.val=8 then i else if r.val=9 then j else []

def prepared (raw : BitString) : Store 77 :=
  store (tape raw) [] [] [] (graph raw) [] (unary (inputSize raw)) [] [preValid raw] []
def beforeParser (raw : BitString) : Store 77 :=
  store (tape raw) [] [] [] (graph raw) [] (unary (inputSize raw)) [] [] []
def postParser (raw : BitString) : Store 77 :=
  store (tape raw) (GraphParser.output (graph raw) 2) [] (GraphParser.output (graph raw) 3)
    (graph raw) [] (unary (inputSize raw)) (GraphParser.output (graph raw) 1) [] []
def afterValid (raw : BitString) : Store 77 := Function.update (postParser raw) 7 []

def preparePorts : Fin 45 ↪ Fin 78 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun q : Fin 78 => q.val) h)
def parserPorts : Fin 39 ↪ Fin 78 where
  toFun i := if i.val=0 then 4 else if i.val=1 then 7 else if i.val=2 then 1
    else if i.val=3 then 3 else ⟨i.val+6,by omega⟩
  inj' := by decide +kernel
noncomputable def prepare : OracleBlock 77 := rename Outer.prepare preparePorts
noncomputable def parseGraph : OracleBlock 77 := rename GraphParser.program parserPorts

lemma prepare_executes (g : BitString → ℕ) (raw : BitString) :
    ∃t,prepare.Executes g (Function.update (fun _ : Fin 78 => ([]:BitString)) 0 raw)
      (prepared raw) t ∧ t≤50*(raw.length+1)^2 := by
  obtain ⟨t,ht,hb⟩ := Outer.prepare_executes g raw
  refine ⟨t,rename_executes_to _ preparePorts g ht ?_ ?_ ?_,hb⟩
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have hge : 45 ≤ i.val := by
      by_contra h
      exact hi ⟨i.val,by omega⟩ (Fin.ext rfl)
    have h0 : i≠(0:Fin 78) := by intro h;subst i;norm_num at hge
    simp [prepared,store,Function.update_of_ne h0,show i.val≠0 by omega,
      show i.val≠1 by omega,show i.val≠2 by omega,show i.val≠3 by omega,
      show i.val≠4 by omega,show i.val≠5 by omega,show i.val≠6 by omega,
      show i.val≠7 by omega,show i.val≠8 by omega,show i.val≠9 by omega]

lemma parser_executes (g : BitString → ℕ) (raw : BitString) :
    ∃t,parseGraph.Executes g (beforeParser raw) (postParser raw) t ∧
      t≤GraphParser.time.eval (graph raw).length := by
  obtain ⟨t,ht,hb⟩ := GraphParser.program_executes g (graph raw)
  refine ⟨t,rename_executes_to _ parserPorts g ht ?_ ?_ ?_,hb⟩
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl)

lemma pop_prepared (raw : BitString) : Function.update (prepared raw) 8 []=beforeParser raw := by
  funext i;fin_cases i <;> rfl

noncomputable def chosenValue (raw : BitString) : BitString :=
  match GraphInput.decode (graph raw) with
  | none => []
  | some G => GraphFunctional.core G.2 (inputSize raw+1) (tape raw)

lemma evaluate_eq (raw : BitString) :
    GraphFunctional.evaluate raw=if preValid raw then chosenValue raw else [] := by
  unfold GraphFunctional.evaluate
  rw [parse_spec raw]
  cases h1 : (parse raw).ok
  · simp [h1,Outer.preValid]
  · simp only [ite_true]
    rw [parse_spec (parse raw).left]
    cases h2 : (parse (parse raw).left).ok
    · simp [h1,h2,Outer.preValid]
    · simp [h1,h2,Outer.preValid,chosenValue,Outer.graph,Outer.inputSize,Outer.tape] <;> rfl

lemma prepare_queryFree : prepare.QueryFree := rename_queryFree _ _ Outer.prepare_queryFree
lemma parseGraph_queryFree : parseGraph.QueryFree := rename_queryFree _ _ GraphParser.program_queryFree
end HiddenCircuits.Approximation.SamplerRuntime.GraphOuter
