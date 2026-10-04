import HiddenCircuits.GraphReduction.Runtime.MonotoneOrderEdges

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneOrderRuntime
open Complexity OracleBlock
set_option maxHeartbeats 1100000

def work : List (Fin 57) := callbackWork++[35,36,37,38,39,40,41]
def recordLT (lower rightPart isLeft : Bool) (records : List VertexRecord) (i j : ℕ) : Bool :=
  outputValue lower rightPart isLeft (records[i]?.getD defaultRecord) (records[j]?.getD defaultRecord)
def bound (n L : ℕ) : ℕ := 2*lookupBound L n+2500*L+7100
noncomputable def program (lower rightPart isLeft : Bool) : OracleBlock 56 := seq callbackLookup (seq callbackParse (seq (edges lower rightPart isLeft) (clearList work)))

lemma cleanup_executes (g : BitString→ℕ) (lower rightPart isLeft : Bool) (c : QueryContext) (x y : VertexRecord) :
    ∃t,(clearList work).Executes g (state lower c x y 7 [outputValue lower rightPart isLeft x y])
      (callbackStore c [outputValue lower rightPart isLeft x y] [] [] (fun _=>[]) (fun _=>[]) [] []) t ∧ t≤27*dirSize x y+82 := by
  let start:=state lower c x y 7 [outputValue lower rightPart isLeft x y]
  have hs:∀i∈work,(start i).length≤dirSize x y:=by
    intro i hi
    have hc:=dir_coordinates_bound x y
    have hp:=dirSize_pos x y
    have hx:layerValue lower x≤dirSize x y:=by have:=layerValue_le lower x;simp [dirSize,encodeVertex_length] at *;omega
    have hy:layerValue lower y≤dirSize x y:=by have:=layerValue_le lower y;simp [dirSize,encodeVertex_length] at *;omega
    fin_cases i <;> simp [work,callbackWork] at hi
    all_goals simp [start,state,flags,callbackStore,recordFields] <;> omega
  obtain ⟨t,ht,hb⟩:=clearList_executes_local g work start (dirSize x y) hs
  have he:eraseStore work start=callbackStore c [outputValue lower rightPart isLeft x y] [] [] (fun _=>[]) (fun _=>[]) [] []:=by
    funext i;fin_cases i <;> simp [eraseStore,work,callbackWork,start,state,callbackStore]
  refine ⟨t,by rwa [he] at ht,?_⟩
  simp only [work,callbackWork,List.length_append,List.length_cons,List.length_nil] at hb
  omega

theorem program_executes (g : BitString→ℕ) (lower rightPart isLeft : Bool) (records : List VertexRecord)
    (i j : Fin records.length) (out inner outer : BitString) :
    ∃t,(program lower rightPart isLeft).Executes g
      (callbackStore (queryContext records i.val j.val out inner outer) [] [] [] (fun _=>[]) (fun _=>[]) [] [])
      (callbackStore (queryContext records i.val j.val out inner outer) [recordLT lower rightPart isLeft records i.val j.val] [] [] (fun _=>[]) (fun _=>[]) [] []) t ∧
      t≤bound records.length (encodeBitList (records.map encodeVertex)).length := by
  let c:=queryContext records i.val j.val out inner outer
  let x:=records.get i
  let y:=records.get j
  obtain ⟨a,ha,hab⟩:=callbackLookup_executes g records i j out inner outer
  have hp:=callbackParse_executes g c x y
  obtain ⟨b,hb,hbb⟩:=edges_executes g lower rightPart isLeft c x y
  obtain ⟨t,ht,htb⟩:=cleanup_executes g lower rightPart isLeft c x y
  have he:recordLT lower rightPart isLeft records i.val j.val=outputValue lower rightPart isLeft x y:=by simp [recordLT,x,y,i.isLt,j.isLt]
  refine ⟨a+(((5*x.layer+5*x.track+2*x.cut.index+49)+(5*y.layer+5*y.track+2*y.cut.index+49)+2)+(b+t+2)+2)+2,?_,?_⟩
  · rw [he]
    exact seq_executes _ _ g ha (seq_executes _ _ g hp (seq_executes _ _ g hb ht))
  · have hx:=descriptor_record_length records i
    have hy:=descriptor_record_length records j
    have hxp:=recordParse_cost_le x
    have hyp:=recordParse_cost_le y
    unfold bound
    unfold dirSize at hbb htb
    change (encodeVertex x).length≤_ at hx
    change (encodeVertex y).length≤_ at hy
    omega

theorem framed (g : BitString→ℕ) (lower rightPart isLeft : Bool) (records : List VertexRecord) (i j : ℕ)
    (hi:i<records.length) (hj:j<records.length) (out inner outer : BitString) :
    ∃t,(program lower rightPart isLeft).Executes g
      (MatrixEmitter.store (k:=49) records.length i j [] out inner outer (callbackParams (encodeBitList (records.map encodeVertex))))
      (MatrixEmitter.store (k:=49) records.length i j [recordLT lower rightPart isLeft records i j] out inner outer (callbackParams (encodeBitList (records.map encodeVertex)))) t ∧
      t≤bound records.length (encodeBitList (records.map encodeVertex)).length := by
  simpa only [callbackStore_initial,queryContext] using program_executes g lower rightPart isLeft records ⟨i,hi⟩ ⟨j,hj⟩ out inner outer
lemma program_queryFree (lower rightPart isLeft : Bool) : (program lower rightPart isLeft).QueryFree := seq_queryFree _ _ callbackLookup_queryFree
  (seq_queryFree _ _ callbackParse_queryFree (seq_queryFree _ _ (edges_queryFree _ _ _) (clearList_queryFree _)))
end HiddenCircuits.GraphReduction.Runtime.MonotoneOrderRuntime
