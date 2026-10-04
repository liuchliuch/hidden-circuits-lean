import HiddenCircuits.GraphReduction.Runtime.MonotoneCallbackDefs

namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

lemma lookupBound_mono (L i n : ℕ) (hi : i≤n) : lookupBound L i≤lookupBound L n := by
  unfold lookupBound
  gcongr

theorem callbackLookup_executes (g : BitString → ℕ) (records : List VertexRecord)
    (i j : Fin records.length) (out inner outer : BitString) :
    ∃ t, callbackLookup.Executes g
      (callbackStore (queryContext records i.val j.val out inner outer) [] [] [] (fun _ => []) (fun _ => []) [] [])
      (callbackStore (queryContext records i.val j.val out inner outer) []
        (encodeVertex (records.get i)) (encodeVertex (records.get j)) (fun _ => []) (fun _ => []) [] []) t ∧
      t≤2*lookupBound (encodeBitList (records.map encodeVertex)).length records.length+2 := by
  let c := queryContext records i.val j.val out inner outer
  let s0 := callbackStore c [] [] [] (fun _ => []) (fun _ => []) [] []
  let s1 := callbackStore c [] (encodeVertex (records.get i)) [] (fun _ => []) (fun _ => []) [] []
  let s2 := callbackStore c [] (encodeVertex (records.get i)) (encodeVertex (records.get j)) (fun _ => []) (fun _ => []) [] []
  have hi : (records.map encodeVertex)[i.val]?.getD []=encodeVertex (records.get i) := by
    simp [List.getElem?_map,List.getElem?_eq_getElem,i.isLt]
  have hj : (records.map encodeVertex)[j.val]?.getD []=encodeVertex (records.get j) := by
    simp [List.getElem?_map,List.getElem?_eq_getElem,j.isLt]
  obtain ⟨a,ha,hba⟩ := listLookupOn_executes callbackRowLookupEmbedding g s0
    (records.map encodeVertex) i.val (by funext k; fin_cases k <;> rfl)
  rw [hi] at ha
  have h1 : callbackRowLookup.Executes g s0 s1 a := by
    convert ha using 1
    funext k; fin_cases k <;> rfl
  obtain ⟨b,hb,hbb⟩ := listLookupOn_executes callbackColLookupEmbedding g s1
    (records.map encodeVertex) j.val (by funext k; fin_cases k <;> rfl)
  rw [hj] at hb
  have h2 : callbackColLookup.Executes g s1 s2 b := by
    convert hb using 1
    funext k; fin_cases k <;> rfl
  refine ⟨a+b+2,seq_executes _ _ g h1 h2,?_⟩
  have hai := hba.trans (lookupBound_mono _ _ _ i.isLt.le)
  have hbj := hbb.trans (lookupBound_mono _ _ _ j.isLt.le)
  omega

lemma callbackLookup_queryFree : callbackLookup.QueryFree :=
  seq_queryFree _ _ (listLookupOn_queryFree _) (listLookupOn_queryFree _)

end HiddenCircuits.GraphReduction.Runtime
