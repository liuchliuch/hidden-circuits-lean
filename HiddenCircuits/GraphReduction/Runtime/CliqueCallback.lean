import HiddenCircuits.GraphReduction.Runtime.CliqueCallbackEdges

namespace HiddenCircuits.GraphReduction.Runtime.CliqueCallback
open Complexity OracleBlock
set_option maxHeartbeats 900000

def work : List (Fin 57) := callbackWork++[35,36]
def recordEdge (mode : Bool) (records : List VertexRecord) (i j : ℕ) : Bool :=
  cliqueRecordAdj mode (records[i]?.getD defaultRecord) (records[j]?.getD defaultRecord)
def bound (n L : ℕ) : ℕ := 2*lookupBound L n+2000*L+5000
noncomputable def program (mode : Bool) : OracleBlock 56 :=
  seq callbackLookup (seq callbackParse (seq (edges mode) (clearList work)))

lemma cleanup_executes (g : BitString → ℕ) (mode : Bool) (c : QueryContext) (x y : VertexRecord) :
    ∃t,(clearList work).Executes g
      (edgeState c x y [cliqueDirectedRecordAdj mode x y] [cliqueDirectedRecordAdj mode y x]
        [decide (x.layer=y.layer)] [decide (x.track=y.track)] [cliqueRecordAdj mode x y])
      (callbackStore c [cliqueRecordAdj mode x y] [] [] (fun _=>[]) (fun _=>[]) [] []) t ∧ t≤22*dirSize x y+67 := by
  let start := edgeState c x y [cliqueDirectedRecordAdj mode x y] [cliqueDirectedRecordAdj mode y x]
    [decide (x.layer=y.layer)] [decide (x.track=y.track)] [cliqueRecordAdj mode x y]
  have hsize : ∀i∈work,(start i).length≤dirSize x y := by
    intro i hi
    have hc := dir_coordinates_bound x y
    have hp := dirSize_pos x y
    fin_cases i <;> simp [work,callbackWork] at hi
    all_goals simp [start,edgeState,callbackStore,recordFields] <;> omega
  obtain ⟨t,ht,hb⟩ := clearList_executes_local g work start (dirSize x y) hsize
  have he : eraseStore work start=callbackStore c [cliqueRecordAdj mode x y] [] [] (fun _=>[]) (fun _=>[]) [] [] := by
    funext i;fin_cases i <;> simp [eraseStore,work,callbackWork,start,edgeState,callbackStore]
  refine ⟨t,by rwa [he] at ht,?_⟩
  simp only [work,callbackWork,List.length_append,List.length_cons,List.length_nil] at hb
  omega

theorem program_executes (g : BitString → ℕ) (mode : Bool) (records : List VertexRecord)
    (i j : Fin records.length) (out inner outer : BitString) :
    ∃t,(program mode).Executes g
      (callbackStore (queryContext records i.val j.val out inner outer) [] [] [] (fun _=>[]) (fun _=>[]) [] [])
      (callbackStore (queryContext records i.val j.val out inner outer) [recordEdge mode records i.val j.val] [] [] (fun _=>[]) (fun _=>[]) [] []) t ∧
      t≤bound records.length (encodeBitList (records.map encodeVertex)).length := by
  let context := queryContext records i.val j.val out inner outer
  let x := records.get i
  let y := records.get j
  obtain ⟨a,ha,hab⟩ := callbackLookup_executes g records i j out inner outer
  have hp := callbackParse_executes g context x y
  obtain ⟨b,hb,hbb⟩ := edges_executes g mode context x y
  obtain ⟨t,ht,htb⟩ := cleanup_executes g mode context x y
  have he : recordEdge mode records i.val j.val=cliqueRecordAdj mode x y := by simp [recordEdge,x,y,i.isLt,j.isLt]
  refine ⟨a+(((5*x.layer+5*x.track+2*x.cut.index+49)+(5*y.layer+5*y.track+2*y.cut.index+49)+2)+(b+t+2)+2)+2,?_,?_⟩
  · rw [he]
    exact seq_executes _ _ g ha (seq_executes _ _ g hp (seq_executes _ _ g hb ht))
  · have hx := descriptor_record_length records i
    have hy := descriptor_record_length records j
    have hxp := recordParse_cost_le x
    have hyp := recordParse_cost_le y
    unfold bound
    unfold dirSize at hbb htb
    change (encodeVertex x).length≤_ at hx
    change (encodeVertex y).length≤_ at hy
    omega

theorem framed (g : BitString → ℕ) (mode : Bool) (records : List VertexRecord) (i j : ℕ)
    (hi:i<records.length) (hj:j<records.length) (out inner outer : BitString) :
    ∃t,(program mode).Executes g
      (MatrixEmitter.store (k:=49) records.length i j [] out inner outer (callbackParams (encodeBitList (records.map encodeVertex))))
      (MatrixEmitter.store (k:=49) records.length i j [recordEdge mode records i j] out inner outer (callbackParams (encodeBitList (records.map encodeVertex)))) t ∧
      t≤bound records.length (encodeBitList (records.map encodeVertex)).length := by
  simpa only [callbackStore_initial,queryContext] using program_executes g mode records ⟨i,hi⟩ ⟨j,hj⟩ out inner outer
lemma program_queryFree (mode : Bool) : (program mode).QueryFree := seq_queryFree _ _ callbackLookup_queryFree
  (seq_queryFree _ _ callbackParse_queryFree (seq_queryFree _ _ (edges_queryFree _) (clearList_queryFree _)))
end HiddenCircuits.GraphReduction.Runtime.CliqueCallback
