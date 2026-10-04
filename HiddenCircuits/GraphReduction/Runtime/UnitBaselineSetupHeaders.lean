import HiddenCircuits.GraphReduction.Runtime.UnitBaselineSetupNumbers

namespace HiddenCircuits.GraphReduction.Runtime.UnitBaselineSetup
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine
set_option maxRecDepth 2000
set_option maxHeartbeats 1500000

 theorem lookup_executes (g : BitString → ℕ) (records : List VertexRecord) (i : Fin records.length)
    (width height : ℕ) (out outer : BitString) :
    ∃t,lookup.Executes g (initial (queryContext records i.val 0 out [] outer) width height)
      (state (queryContext records i.val 0 out [] outer) width height (encodeVertex (records.get i))
        (fun _=>[]) (fun _=>[]) []) t ∧
      t≤lookupBound (encodeBitList (records.map encodeVertex)).length records.length := by
  let c:=queryContext records i.val 0 out [] outer
  obtain ⟨t,ht,hb⟩ := listLookupOn_executes lookupMap g (initial c width height) (records.map encodeVertex) i.val
    (by funext q;fin_cases q <;> rfl)
  have hi : (records.map encodeVertex)[i.val]?.getD []=encodeVertex (records.get i) := by
    simp [List.getElem?_map,List.getElem?_eq_getElem,i.isLt]
  rw [hi] at ht
  refine ⟨t,?_,?_⟩
  · convert ht using 1;funext q;fin_cases q <;> rfl
  · apply hb.trans
    unfold lookupBound;gcongr <;> exact i.isLt.le

 theorem parse_executes (g : BitString → ℕ) (c : QueryContext) (width height : ℕ) (x : VertexRecord) :
    parse.Executes g (state c width height (encodeVertex x) (fun _=>[]) (fun _=>[]) [])
      (parsed c width height x) (5*x.layer+5*x.track+2*x.cut.index+49) := by
  apply rename_executes_to _ parseMap g (recordParse_executes g x)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim | exact (hi 4 rfl).elim | exact (hi 5 rfl).elim | exact (hi 6 rfl).elim | exact (hi 7 rfl).elim | exact (hi 8 rfl).elim | exact (hi 9 rfl).elim

 theorem arithmetic_executes (g : BitString → ℕ) (c : QueryContext) (width height : ℕ) (x : VertexRecord) :
    ∃t,arithmetic.Executes g (ready c width height x)
      (state c width height [] (recordFields x)
        (signedBits ∘ evaluate (UnitBaseline.code (UnitBaseline.mode x)) (UnitBaseline.init width height x.layer x.track))
        [decide (x.track=x.cut.index)]) t ∧t≤UnitBaseline.timePolynomial.eval (UnitBaseline.inputBound width height x) := by
  obtain ⟨t,ht,hb⟩ := UnitBaseline.program_executes width height x g
  refine ⟨t,?_,hb⟩
  apply rename_executes_to _ arithmeticMap g ht
  · clear ht;funext i;fin_cases i <;> rfl
  · clear ht;funext i;fin_cases i <;> rfl
  · clear ht;intro i hi;fin_cases i <;> first | rfl | exact (hi 9 rfl).elim | exact (hi 10 rfl).elim | exact (hi 11 rfl).elim | exact (hi 12 rfl).elim | exact (hi 13 rfl).elim | exact (hi 14 rfl).elim | exact (hi 15 rfl).elim

 theorem clean_executes (g : BitString → ℕ) (c : QueryContext) (width height : ℕ) (x : VertexRecord)
    (R : Fin 7 → ℤ) :
    ∃t,clean.Executes g (state c width height [] (recordFields x) (signedBits ∘ R) [decide (x.track=x.cut.index)])
      (result c width height x R) t ∧t≤9*(magnitude width height x+3)+1 := by
  obtain ⟨t,ht,hb⟩ := clearList_executes_local g cleanPorts
    (state c width height [] (recordFields x) (signedBits ∘ R) [decide (x.track=x.cut.index)])
    (magnitude width height x) (by
      intro j hj;simp only [cleanPorts,List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [state,recordFields,magnitude] <;> omega)
  refine ⟨t,?_,hb⟩
  convert ht using 1;funext i;fin_cases i <;> rfl
end HiddenCircuits.GraphReduction.Runtime.UnitBaselineSetup
