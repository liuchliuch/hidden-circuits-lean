import HiddenCircuits.GraphReduction.Runtime.MonotoneCallbackDefs

namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

theorem callbackEdges_executes (g : BitString → ℕ) (c : QueryContext) (x y : VertexRecord) :
    ∃ t, callbackEdges.Executes g (callbackStore c [] [] [] (recordFields x) (recordFields y) [] [])
      (callbackStore c [recordAdj x y] [] [] (recordFields x) (recordFields y)
        [directedRecordAdj x y] [directedRecordAdj y x]) t ∧ t≤400*dirSize x y+1696 := by
  let s0 := callbackStore c [] [] [] (recordFields x) (recordFields y) [] []
  let s1 := callbackStore c [] [] [] (recordFields x) (recordFields y) [directedRecordAdj x y] []
  let s2 := callbackStore c [] [] [] (recordFields x) (recordFields y) [directedRecordAdj x y] [directedRecordAdj y x]
  let s3 := callbackStore c [recordAdj x y] [] [] (recordFields x) (recordFields y) [directedRecordAdj x y] [directedRecordAdj y x]
  obtain ⟨a,ha,hba⟩ := directedPredicateOn_executes callbackForwardEmbedding g x y s0
    (by funext i; fin_cases i <;> rfl)
  have h1 : callbackForward.Executes g s0 s1 a := by
    convert ha using 1
    funext i; fin_cases i <;> rfl
  obtain ⟨b,hb,hbb⟩ := directedPredicateOn_executes callbackBackwardEmbedding g y x s1
    (by funext i; fin_cases i <;> rfl)
  have h2 : callbackBackward.Executes g s1 s2 b := by
    convert hb using 1
    funext i; fin_cases i <;> rfl
  let bits : Fin 8 → Bool := ![directedRecordAdj x y,directedRecordAdj y x,x.side,y.side,x.probe,y.probe,x.cut.leftRise,y.cut.leftRise]
  have h := gate8On_executes callbackOrEmbedding g orGate bits s2 (by funext i; fin_cases i <;> rfl)
  have he : orGate (gate8Args bits)=recordAdj x y := by
    simp only [orGate,gate8Args,bits]
    exact (recordAdj_or x y).symm
  rw [he] at h
  have h3 : callbackOr.Executes g s2 s3 92 := by
    convert h using 1
    funext i; fin_cases i <;> rfl
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  have hs : dirSize y x=dirSize x y := by simp [dirSize,Nat.add_comm]
  rw [hs] at hbb
  omega

lemma callbackEdges_queryFree : callbackEdges.QueryFree :=
  seq_queryFree _ _ (directedPredicateOn_queryFree _)
    (seq_queryFree _ _ (directedPredicateOn_queryFree _) (gate8On_queryFree _ _))

theorem callbackCleanup_executes (g : BitString → ℕ) (c : QueryContext) (x y : VertexRecord) :
    ∃ t, (clearList callbackWork).Executes g
      (callbackStore c [recordAdj x y] [] [] (recordFields x) (recordFields y)
        [directedRecordAdj x y] [directedRecordAdj y x])
      (callbackStore c [recordAdj x y] [] [] (fun _ => []) (fun _ => []) [] []) t ∧ t≤20*dirSize x y+61 := by
  let s := callbackStore c [recordAdj x y] [] [] (recordFields x) (recordFields y)
    [directedRecordAdj x y] [directedRecordAdj y x]
  have hs : ∀ i∈callbackWork, (s i).length≤dirSize x y := by
    intro i hi
    have hc := dir_coordinates_bound x y
    have hp := dirSize_pos x y
    fin_cases i <;> simp [callbackWork] at hi
    all_goals simp [s,callbackStore,recordFields] <;> omega
  obtain ⟨t,ht,hb⟩ := clearList_executes_local g callbackWork s (dirSize x y) hs
  have he : eraseStore callbackWork s=callbackStore c [recordAdj x y] [] [] (fun _ => []) (fun _ => []) [] [] := by
    funext i; fin_cases i <;> simp [s,eraseStore,callbackWork,callbackStore]
  refine ⟨t,by rwa [he] at ht,?_⟩
  simp only [callbackWork,List.length_cons,List.length_nil] at hb
  omega

end HiddenCircuits.GraphReduction.Runtime
