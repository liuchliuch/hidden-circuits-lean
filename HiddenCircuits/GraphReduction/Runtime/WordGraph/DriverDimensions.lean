import HiddenCircuits.GraphReduction.Runtime.WordGraph.WordParserCorrectness
import HiddenCircuits.GraphReduction.Runtime.WordGraph.RecoveryAlgebra

/-! Fresh reconstruction: read the literal word and its dimensions into the
24-port driver header; preserve both boundary masks for the empty-word case. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverDimensions
open Complexity OracleBlock
set_option maxHeartbeats 700000

def state (w : WordInstance) (width degree clock : ℕ) : Store 23 := fun i =>
  if i.val=0 then wordBits w else if i.val=1 then List.replicate w.particles true
  else if i.val=2 then List.replicate w.word.length true else if i.val=3 then List.replicate width true
  else if i.val=4 then List.replicate degree true else if i.val=5 then List.replicate clock true
  else if i.val=16 then stateBits w.source else if i.val=17 then stateBits w.target
  else if i.val=18 then encodeBitList (w.word.map letterBits) else []
def parserEmbedding : Fin 18 ↪ Fin 24 where
  toFun i := ![0,1,16,17,18,2,6,7,8,9,10,11,12,13,14,15,19,20] i
  inj' := by decide +kernel
noncomputable def program : OracleBlock 23 := rename WordParser.program parserEmbedding

theorem program_executes (g : BitString → ℕ) (w : WordInstance) :
    ∃c,program.Executes g (Function.update (fun _ => []) 0 (wordBits w)) (state w 0 0 0) c ∧
      c≤40*(wordBits w).length+100 := by
  obtain ⟨c,hc,hcb⟩ := WordParser.program_executes g w 0
  refine ⟨c,?_,hcb⟩
  apply rename_executes_to WordParser.program parserEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have hn0 : i≠(0:Fin 24) := fun h => hi 0 h.symm
    have hn1 : i.val≠1 := fun h => hi 1 (Fin.ext h.symm)
    have hn2 : i.val≠2 := fun h => hi 5 (Fin.ext h.symm)
    have hn16 : i.val≠16 := fun h => hi 2 (Fin.ext h.symm)
    have hn17 : i.val≠17 := fun h => hi 3 (Fin.ext h.symm)
    have hn18 : i.val≠18 := fun h => hi 4 (Fin.ext h.symm)
    have hn0v : i.val≠0 := fun h => hn0 (Fin.ext h)
    simp [state,Function.update_of_ne hn0,hn0v,hn1,hn2,hn16,hn17,hn18]
lemma program_queryFree : program.QueryFree := rename_queryFree _ _ WordParser.program_queryFree
end HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverDimensions

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
open Complexity OracleBlock

def parseEmbedding : Fin 24 ↪ Fin 98 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun q : Fin 98 => q.val) h)
def bareState (w : WordInstance) (width degree clock : ℕ) : Store 97 := fun i =>
  if h:i.val<24 then DriverDimensions.state w width degree clock ⟨i.val,h⟩ else []
noncomputable def parse : OracleBlock 97 := rename DriverDimensions.program parseEmbedding

theorem parse_executes (g : BitString → ℕ) (w : WordInstance) :
    ∃c,parse.Executes g (Function.update (fun _ => []) 0 (wordBits w)) (bareState w 0 0 0) c ∧
      c≤40*(wordBits w).length+100 := by
  obtain ⟨c,hc,hcb⟩ := DriverDimensions.program_executes g w
  refine ⟨c,?_,hcb⟩
  apply rename_executes_to DriverDimensions.program parseEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;exact dif_pos i.isLt
  · intro i hi
    have hv : ¬i.val<24 := by intro h;exact hi ⟨i.val,h⟩ (Fin.ext rfl)
    have h0 : i≠0 := by intro h;subst i;norm_num at hv
    simp only [bareState,hv,↓reduceDIte,Function.update_of_ne h0]
lemma parse_queryFree : parse.QueryFree := rename_queryFree _ _ DriverDimensions.program_queryFree
end HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
