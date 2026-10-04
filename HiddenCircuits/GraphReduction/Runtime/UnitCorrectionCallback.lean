import HiddenCircuits.GraphReduction.Runtime.UnitCorrectionCallbackDefs

namespace HiddenCircuits.GraphReduction.Runtime.UnitSignedCallback
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

theorem program_executes (second : Bool) (width height : ℕ) (records : List VertexRecord) (g : BitString → ℕ)
    (i j : ℕ) (out inner outer : BitString) (R : Fin 7 → ℤ) (hi:i<records.length) (hj:j<records.length) :
    ∃t,(program second).Executes g
      (SignedScan.state records.length i j [] out inner outer (params width height (encodeBitList (records.map encodeVertex))) R)
      (SignedScan.state records.length i j
        [decide (unitCorrectionValue second width (records[i]) (records[j])=1),
          decide (unitCorrectionValue second width (records[i]) (records[j])=-1)]
        out inner outer (params width height (encodeBitList (records.map encodeVertex))) R) t ∧
      t≤bound records.length (encodeBitList (records.map encodeVertex)).length width := by
  let c:=queryContext records i j out inner outer
  let x:=records.get ⟨i,hi⟩
  let y:=records.get ⟨j,hj⟩
  let s0:=callbackStore c [] [] [] (fun _=>[]) (fun _=>[]) [] []
  let s1:=callbackStore c [] (encodeVertex x) (encodeVertex y) (fun _=>[]) (fun _=>[]) [] []
  let s2:=callbackStore c [] [] [] (recordFields x) (recordFields y) [] []
  let s3:=callbackStore c (UnitCorrection.output second width x y) [] [] (recordFields x) (recordFields y) [] []
  let sf:=callbackStore c (UnitCorrection.output second width x y) [] [] (fun _=>[]) (fun _=>[]) [] []
  obtain ⟨a,ha,hba⟩:=callbackLookup_executes g records ⟨i,hi⟩ ⟨j,hj⟩ out inner outer
  have h1 : lookup.Executes g (frame s0 width height R) (frame s1 width height R) a := frame_executes _ _ _ _ _ _ _ R ha
  have h2 : parse.Executes g (frame s1 width height R) (frame s2 width height R)
      ((5*x.layer+5*x.track+2*x.cut.index+49)+(5*y.layer+5*y.track+2*y.cut.index+49)+2) :=
    frame_executes _ _ _ _ _ _ _ R (callbackParse_executes g c x y)
  obtain ⟨b,hb,hbb⟩:=UnitCorrection.on_executes predicateMap g second width x y (frame s2 width height R)
    (by funext q;fin_cases q <;> rfl)
  have h3 : (predicate second).Executes g (frame s2 width height R) (frame s3 width height R) b := by
    convert hb using 1;funext q;fin_cases q <;> rfl
  let L:=(encodeBitList (records.map encodeVertex)).length
  have hx: (encodeVertex x).length≤L:=descriptor_record_length records ⟨i,hi⟩
  have hy: (encodeVertex y).length≤L:=descriptor_record_length records ⟨j,hj⟩
  have hlx:=hx;have hly:=hy
  rw [encodeVertex_length] at hx hy
  obtain ⟨d,hd,hbd⟩:=clearList_executes_local g cleanPorts (frame s3 width height R) (2*L+1) (by
    intro q hq;simp only [cleanPorts,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [frame,s3,callbackStore,recordFields] <;> omega)
  have h4 : (clearList cleanPorts).Executes g (frame s3 width height R) (frame sf width height R) d := by
    convert hd using 1;funext q;fin_cases q <;> rfl
  have h:=seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4))
  change (program second).Executes g (frame s0 width height R) (frame sf width height R) _ at h
  rw [initial_eq,initial_eq] at h
  refine ⟨_,h,?_⟩
  simp only [cleanPorts,List.length_cons,List.length_nil] at hbd
  unfold bound UnitCorrection.size at *
  dsimp only [L] at *
  omega

lemma program_queryFree (second : Bool) : (program second).QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ callbackLookup_queryFree) (seq_queryFree _ _ (rename_queryFree _ _ callbackParse_queryFree)
    (seq_queryFree _ _ (UnitCorrection.on_queryFree _ _) (clearList_queryFree _)))
end HiddenCircuits.GraphReduction.Runtime.UnitSignedCallback
