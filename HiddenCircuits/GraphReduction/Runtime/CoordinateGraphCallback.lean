import HiddenCircuits.GraphReduction.Runtime.CoordinateGraphCallbackDefs

namespace HiddenCircuits.GraphReduction.Runtime.CoordinateGraph
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic
set_option maxRecDepth 2000
set_option maxHeartbeats 1500000

theorem callback_executes (g : BitString → ℕ) (n i j : ℕ) (out inner outer data : BitString) (d : ℤ)
    (hi:i<n) (hj:j<n) :
    ∃c,callback.Executes g (callbackState n i j out inner outer data d)
      (MatrixEmitter.store n i j [edge d data i j] out inner outer (params data d)) c ∧
      c≤callbackBound n data.length (signedBits d).length := by
  let base:=callbackState n i j out inner outer data d
  let wx:=(LooseWordList.words data)[i]?.getD []
  let wy:=(LooseWordList.words data)[j]?.getD []
  let x:=endpoint data i
  let y:=endpoint data j
  let s1:=Function.update base (11:Fin 32) wx
  let s2:=Function.update base (11:Fin 32) (signedBits x)
  let s3:=Function.update s2 (12:Fin 32) wy
  let s4:=Function.update s2 (12:Fin 32) (signedBits y)
  let s5:=Function.update s4 (10:Fin 32) (signedBits d)
  let s6:=Function.update base (13:Fin 32) [IntegerDistance.answer d x y]
  let s7:=Function.update s6 (31:Fin 32) [decide (i=j)]
  obtain ⟨a,ha,hba⟩:=listLookupOn_raw (lookupMap false) g base data i (by funext q;fin_cases q <;> rfl)
  have h1 : (lookup false).Executes g base s1 a := ha
  obtain ⟨b,hb,hbb⟩:=SignedNormalize.on_executes (normalizeMap false) g s1 wx (by funext q;fin_cases q <;> rfl)
  have h2 : (normalize false).Executes g s1 s2 b := by
    change (normalize false).Executes g s1 (Function.update (Function.update base 11 wx) 11 (signedBits x)) b at hb
    simpa only [Function.update_idem] using hb
  obtain ⟨c,hc,hbc⟩:=listLookupOn_raw (lookupMap true) g s2 data j (by funext q;fin_cases q <;> rfl)
  have h3 : (lookup true).Executes g s2 s3 c := hc
  obtain ⟨e,he,hbe⟩:=SignedNormalize.on_executes (normalizeMap true) g s3 wy (by funext q;fin_cases q <;> rfl)
  have h4 : (normalize true).Executes g s3 s4 e := by
    change (normalize true).Executes g s3 (Function.update (Function.update s2 12 wy) 12 (signedBits y)) e at he
    simpa only [Function.update_idem] using he
  have h5 : copyD.Executes g s4 s5 (5*(signedBits d).length+2) := by
    convert copyOn_executes g (9:Fin 32) 10 27 (by decide) (by decide) (by decide) s4 rfl using 1
    funext q;fin_cases q <;> simp [s5,s4,s2,base,callbackState,MatrixEmitter.store,MatrixEmitter.port,params]
  obtain ⟨f,hf,hbf⟩:=IntegerDistance.program_executes g d x y (data.length+(signedBits d).length+3)
    (by omega) ((endpoint_length data i).trans (by omega)) ((endpoint_length data j).trans (by omega)) (by omega)
  have h6 : distance.Executes g s5 s6 f := by
    apply rename_executes_to _ distanceMap g hf
    · clear hf;funext q;fin_cases q <;> rfl
    · clear hf;funext q;fin_cases q <;> rfl
    · clear hf;intro q hq
      have h10:q.val≠10 :=by intro h;exact hq 0 (Fin.ext h.symm)
      have h11:q.val≠11 :=by intro h;exact hq 1 (Fin.ext h.symm)
      have h12:q.val≠12 :=by intro h;exact hq 2 (Fin.ext h.symm)
      have h13:q.val≠13 :=by intro h;exact hq 3 (Fin.ext h.symm)
      simp [s5,s4,s3,s2,s1,s6,Function.update_apply,show q≠10 by exact fun h=>h10 (congrArg Fin.val h),
        show q≠11 by exact fun h=>h11 (congrArg Fin.val h),show q≠12 by exact fun h=>h12 (congrArg Fin.val h),
        show q≠13 by exact fun h=>h13 (congrArg Fin.val h)]
  obtain ⟨h,hh,hbh⟩:=Complexity.GraphVerifier.Runtime.readLengthOn_executes equalMap g s6
    (List.replicate i true) (List.replicate j true) (by funext q;fin_cases q <;> rfl)
  have h7 : equal.Executes g s6 s7 h := by simpa only [List.length_replicate] using hh
  have h8 : gate.Executes g s7 (MatrixEmitter.store n i j [edge d data i j] out inner outer (params data d)) 8 := by
    have ht:=Complexity.GraphVerifier.Runtime.decision_executes (3:Fin 32) [13,31] (by decide) (by decide)
      (fun bs=>(bs[0]?.getD false)&& !(bs[1]?.getD true))
      (fun q=>if q.val=13 then IntegerDistance.answer d x y else decide (i=j)) g s7 (by
        intro q hq;simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
        rcases hq with rfl|rfl <;> rfl)
    convert ht using 1
    funext q;fin_cases q <;> simp [s7,s6,base,callbackState,MatrixEmitter.store,MatrixEmitter.port,params,eraseStore,
      edge,Bool.and_comm,decide_not,x,y]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 (seq_executes _ _ g h6 (seq_executes _ _ g h7 h8)))))),?_⟩
  have hlx:=lookup_length data i
  have hly:=lookup_length data j
  have hai:rawLookupBound data.length i≤rawLookupBound data.length n := by unfold rawLookupBound;gcongr <;> omega
  have haj:rawLookupBound data.length j≤rawLookupBound data.length n := by unfold rawLookupBound;gcongr <;> omega
  simp only [List.length_replicate] at hbh
  dsimp only [wx,wy] at hbb hbe
  unfold callbackBound
  omega

lemma callback_queryFree : callback.QueryFree :=
  seq_queryFree _ _ (listLookupOn_queryFree _) (seq_queryFree _ _ (SignedNormalize.on_queryFree _)
    (seq_queryFree _ _ (listLookupOn_queryFree _) (seq_queryFree _ _ (SignedNormalize.on_queryFree _)
      (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (rename_queryFree _ _ IntegerDistance.program_queryFree)
        (seq_queryFree _ _ (Complexity.GraphVerifier.Runtime.readLengthOn_queryFree _)
          (Complexity.GraphVerifier.Runtime.decision_queryFree _ _ _)))))))
end HiddenCircuits.GraphReduction.Runtime.CoordinateGraph
