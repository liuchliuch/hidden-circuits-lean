import HiddenCircuits.DH.Runtime.NumericRoundsCore
import HiddenCircuits.DH.Runtime.NumericInitialize
import HiddenCircuits.DH.Runtime.FinalProductNumeric
import HiddenCircuits.DH.Runtime.BinaryModel
import HiddenCircuits.Approximation.SamplerRuntime.GraphParserProgram

/-! Actual all-input graph parsing, dynamic numeric
initialization and final integer product, with their fixed stack embeddings. -/
namespace HiddenCircuits.DH.Runtime.BinaryPipeline
open Complexity OracleBlock Polynomial
open PairCheck
open HiddenCircuits.Approximation.SamplerRuntime
set_option maxHeartbeats 1800000

def input (raw : BitString) : Store 53 := Function.update (fun _=>[]) 0 raw
def parsed (raw : BitString) : Store 53 := fun q=>
  if q.val=0 then raw else if q.val=1 then [(GraphInput.decode raw).isSome]
  else if q.val=5 then (GraphVerifier.parse raw).left
  else if q.val=50 then (GraphVerifier.parse raw).right else []
def parserMap : Fin 39 ↪ Fin 54 where
  toFun q:=⟨if q.val=0 then 0 else if q.val=1 then 1 else if q.val=2 then 50 else if q.val=3 then 5 else q.val+2,
    by split_ifs <;> omega⟩
  inj':=by
    intro q z h;apply Fin.ext;have hh:=congrArg Fin.val h
    dsimp only at hh
    split_ifs at hh <;> omega
noncomputable def parser : OracleBlock 53 := rename GraphParser.program parserMap

lemma parser_executes (g : BitString→ℕ) (raw : BitString) :
    ∃t,parser.Executes g (input raw) (parsed raw) t ∧ t≤GraphParser.time.eval raw.length := by
  obtain ⟨t,ht,hb⟩:=GraphParser.program_executes g raw
  refine ⟨t,?_,hb⟩
  apply rename_executes_to _ parserMap g ht
  · funext q;fin_cases q <;> rfl
  · funext q;fin_cases q <;> rfl
  · intro q hq
    have h0:q.val≠0:=by intro h;exact hq 0 (Fin.ext h.symm)
    have h1:q.val≠1:=by intro h;exact hq 1 (Fin.ext h.symm)
    have h5:q.val≠5:=by intro h;exact hq 3 (Fin.ext h.symm)
    have h50:q.val≠50:=by intro h;exact hq 2 (Fin.ext h.symm)
    simp [parsed,input,h0,h1,h5,h50,Function.update_apply,show q≠0 from fun h=>h0 (congrArg Fin.val h)]

lemma decoded_fields {raw : BitString} {G : GraphInput} (h : GraphInput.decode raw=some G) :
    (GraphVerifier.parse raw).left=List.replicate G.1 true ∧
      (GraphVerifier.parse raw).right=G.2.bits := GraphParser.output_fields h
lemma decoded_size_le {raw : BitString} {G : GraphInput} (h : GraphInput.decode raw=some G) : G.1≤raw.length := by
  have hp:=(GraphVerifier.Runtime.parse_lengths raw).1
  rw [(decoded_fields h).1,List.length_replicate] at hp
  exact hp

def emptyNumeric (n : ℕ) (payload : BitString) : Store 53 := NumericRounds.state n payload [] [] [] [] [] [] []
def initializeMap : Fin 14 ↪ Fin 54 := ⟨fun q=>![5,2,3,4,6,7,8,9,10,11,12,13,14,15] q,by decide +kernel⟩
noncomputable def initializeStage : OracleBlock 53 := NumericInitialize.on initializeMap

lemma clearInput_executes (g : BitString→ℕ) {raw : BitString} {G : GraphInput}
    (h : GraphInput.decode raw=some G) :
    (clear (0:Fin 54)).Executes g (Function.update (parsed raw) 1 [])
      (emptyNumeric G.1 G.2.bits) (raw.length+1) := by
  obtain ⟨hn,hp⟩:=decoded_fields h
  convert clear_executes g (0:Fin 54) (Function.update (parsed raw) 1 []) using 1
  funext q;fin_cases q <;> simp [parsed,emptyNumeric,NumericRounds.state,hn,hp]

lemma initialize_executes (g : BitString→ℕ) {n : ℕ} (G : MatrixData n) :
    ∃t,initializeStage.Executes g (emptyNumeric n G.bits)
      (NumericRounds.store G (NumericStateModel.initial n) none []) t ∧ t≤NumericInitialize.time.eval n := by
  obtain ⟨t,ht,hb⟩:=NumericInitialize.on_executes initializeMap g (emptyNumeric n G.bits) n (by
    funext q;fin_cases q <;> rfl)
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext q;fin_cases q <;> rfl

def finalMap : Fin 14 ↪ Fin 54 := ⟨fun q=>![2,4,6,7,8,9,10,11,12,13,14,15,16,17] q,by decide +kernel⟩
noncomputable def finish : OracleBlock 53 := FinalProduct.on finalMap

def finished {n : ℕ} (G : MatrixData n) (s : NumericStateModel.State n) : Store 53 :=
  NumericRounds.state n G.bits [] [] (Computability.encodeNat (NumericStateModel.result s))
    (NumericEncoding.sizeBits s) [] [] []

lemma finish_executes (g : BitString→ℕ) {n : ℕ} (G : MatrixData n)
    (s : NumericStateModel.State n) (hs : NumericStateModel.Safe s) :
    ∃t,finish.Executes g (NumericRounds.store G s none []) (finished G s) t ∧ t≤FinalProduct.numericTime.eval n := by
  apply FinalProduct.on_executes finalMap g s hs
  · funext q;fin_cases q <;> rfl
  · funext q;fin_cases q <;> rfl
  · intro q hq
    have h2:q.val≠2:=by intro h;exact hq 0 (Fin.ext h.symm)
    have h4:q.val≠4:=by intro h;exact hq 1 (Fin.ext h.symm)
    simp [finished,NumericRounds.store,NumericRounds.state,h2,h4,PairSearch.keptBits,PairSearch.removedBits,PairCheck.resultBits]

lemma parser_queryFree : parser.QueryFree := rename_queryFree _ _ GraphParser.program_queryFree
lemma initialize_queryFree : initializeStage.QueryFree := NumericInitialize.on_queryFree _
lemma finish_queryFree : finish.QueryFree := FinalProduct.on_queryFree _
end HiddenCircuits.DH.Runtime.BinaryPipeline
