import HiddenCircuits.GraphReduction.Runtime.MonotoneCallbackDefs

namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

theorem callbackParse_executes (g : BitString → ℕ) (c : QueryContext) (x y : VertexRecord) :
    callbackParse.Executes g (callbackStore c [] (encodeVertex x) (encodeVertex y) (fun _ => []) (fun _ => []) [] [])
      (callbackStore c [] [] [] (recordFields x) (recordFields y) [] [])
      ((5*x.layer+5*x.track+2*x.cut.index+49)+(5*y.layer+5*y.track+2*y.cut.index+49)+2) := by
  let s0 := callbackStore c [] (encodeVertex x) (encodeVertex y) (fun _ => []) (fun _ => []) [] []
  let s1 := callbackStore c [] [] (encodeVertex y) (recordFields x) (fun _ => []) [] []
  let s2 := callbackStore c [] [] [] (recordFields x) (recordFields y) [] []
  have h1 : callbackRowParse.Executes g s0 s1 (5*x.layer+5*x.track+2*x.cut.index+49) := by
    apply rename_executes_to recordParse callbackRowParseEmbedding g (recordParse_executes g x)
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (hi 0 rfl).elim
      · rfl
      · exact (hi 1 rfl).elim
      · exact (hi 2 rfl).elim
      · exact (hi 3 rfl).elim
      · exact (hi 4 rfl).elim
      · exact (hi 5 rfl).elim
      · exact (hi 6 rfl).elim
      · exact (hi 7 rfl).elim
      · exact (hi 8 rfl).elim
      · exact (hi 9 rfl).elim
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
  have h2 : callbackColParse.Executes g s1 s2 (5*y.layer+5*y.track+2*y.cut.index+49) := by
    apply rename_executes_to recordParse callbackColParseEmbedding g (recordParse_executes g y)
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (hi 0 rfl).elim
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (hi 1 rfl).elim
      · exact (hi 2 rfl).elim
      · exact (hi 3 rfl).elim
      · exact (hi 4 rfl).elim
      · exact (hi 5 rfl).elim
      · exact (hi 6 rfl).elim
      · exact (hi 7 rfl).elim
      · exact (hi 8 rfl).elim
      · exact (hi 9 rfl).elim
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
  exact seq_executes _ _ g h1 h2

lemma callbackParse_queryFree : callbackParse.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ recordParse_queryFree) (rename_queryFree _ _ recordParse_queryFree)

end HiddenCircuits.GraphReduction.Runtime
