import HiddenCircuits.GraphReduction.Runtime.RecordLayer
import HiddenCircuits.GraphReduction.Runtime.RecordTrack

namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

theorem recordIndexParse_executes (g : BitString → ℕ) (v : VertexRecord) : (reverseOn (0 : Fin 12) 9 (by decide)).Executes g (recordStage5 v)
    (recordParseStore [] (recordFields v) [] []) (2*v.cut.index+1) := by
  convert reverseOn_executes g (0 : Fin 12) 9 (by decide) (recordStage5 v) using 1
  · funext i; fin_cases i <;> simp [recordStage5,recordStage4,recordStage3,recordStage2,recordStage1,prefixFields,recordParseStore,recordFields]
  · simp [recordStage5,recordStage4,recordStage3,recordStage2,recordStage1,recordParseStore]

end HiddenCircuits.GraphReduction.Runtime
