import HiddenCircuits.Complexity.EvalValidation.Core

namespace HiddenCircuits.Complexity.EvalValidation.Header
open OracleBlock GraphVerifier GraphVerifier.Runtime Core
set_option maxHeartbeats 1000000

def sourcePort (src : Fin 4) : Fin 32 := ⟨src.val,by omega⟩
def headValue (acceptFalse : Bool) : BitString→Bool
  | [] => false
  | b::_ => b || acceptFalse
noncomputable def popHead (acceptFalse : Bool) : OracleBlock 31 := branchPop 5 (push 6 false) (push 6 acceptFalse) (push 6 true)
noncomputable def headTest (src : Fin 4) (acceptFalse : Bool) : OracleBlock 31 :=
  seq (copyOn (sourcePort src) 5 7 (by fin_cases src <;> decide) (by fin_cases src <;> decide) (by decide))
    (seq (popHead acceptFalse) (clear 5))
lemma popHead_executes (g : BitString→ℕ) (acceptFalse : Bool) (input data p width flags atom : BitString) :
    (popHead acceptFalse).Executes g (state input data p width flags atom [])
      (state input data p width flags atom.tail [headValue acceptFalse atom]) 3 := by
  cases atom with
  | nil =>
    apply branchPop_empty 5 _ _ _ g rfl
    convert push_executes g (6:Fin 32) false (state input data p width flags [] []) using 1
    funext i;fin_cases i <;> rfl
  | cons b atom =>
    have he:Function.update (state input data p width flags (b::atom) []) (5:Fin 32) atom=state input data p width flags atom [] := by
      funext i;fin_cases i <;> rfl
    have hp (v : Bool) : (push (6:Fin 32) v).Executes g (state input data p width flags atom [])
        (state input data p width flags atom [v]) 1 := by
      convert push_executes g (6:Fin 32) v (state input data p width flags atom []) using 1
      funext i;fin_cases i <;> rfl
    cases b
    · exact branchPop_false 5 _ _ _ g rfl (by rw [he];simpa [headValue] using hp acceptFalse)
    · exact branchPop_true 5 _ _ _ g rfl (by rw [he];simpa [headValue] using hp true)
lemma headTest_executes (g : BitString→ℕ) (src : Fin 4) (acceptFalse : Bool) (input data p width flags xs : BitString)
    (hx:state input data p width flags [] [] (sourcePort src)=xs) :
    ∃c,(headTest src acceptFalse).Executes g (state input data p width flags [] [])
      (state input data p width flags [] [headValue acceptFalse xs]) c ∧ c≤6*xs.length+10 := by
  let st:=state input data p width flags [] []
  have hc:(copyOn (sourcePort src) (5:Fin 32) 7 (by fin_cases src <;> decide) (by fin_cases src <;> decide) (by decide)).Executes g
      st (state input data p width flags xs []) (5*xs.length+2) := by
    have h:=copyOn_executes g (sourcePort src) (5:Fin 32) 7 (by fin_cases src <;> decide) (by fin_cases src <;> decide) (by decide) st rfl
    have hx' : st (sourcePort src)=xs := hx
    rw [hx'] at h
    convert h using 1
    funext i;fin_cases i <;> simp [st,state]
  have hp:=popHead_executes g acceptFalse input data p width flags xs
  have hz:(clear (5:Fin 32)).Executes g (state input data p width flags xs.tail [headValue acceptFalse xs])
      (state input data p width flags [] [headValue acceptFalse xs]) (xs.tail.length+1) := by
    convert clear_executes g (5:Fin 32) (state input data p width flags xs.tail [headValue acceptFalse xs]) using 1
    funext i;fin_cases i <;> rfl
  exact ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hp hz),by have:=Field.tail_bound xs;omega⟩

noncomputable def headCollect (src : Fin 4) (acceptFalse : Bool) : OracleBlock 31 := seq (headTest src acceptFalse) collect
lemma headCollect_executes (g : BitString→ℕ) (src : Fin 4) (acceptFalse : Bool) (input data p width flags xs : BitString)
    (hx:state input data p width flags [] [] (sourcePort src)=xs) :
    ∃c,(headCollect src acceptFalse).Executes g (state input data p width flags [] [])
      (state input data p width (headValue acceptFalse xs::flags) [] []) c ∧ c≤6*xs.length+15 := by
  obtain ⟨c,hc,hb⟩:=headTest_executes g src acceptFalse input data p width flags xs hx
  exact ⟨_,seq_executes _ _ g hc (collect_executes g input data p width flags [] _),by omega⟩

def parsePorts : Fin 4 ↪ Fin 32 where
  toFun i:=![1,2,7,6] i
  inj' := by decide +kernel
def headerPorts : Fin 4 ↪ Fin 32 where
  toFun i:=![2,10,11,6] i
  inj' := by decide +kernel
noncomputable def readHeader : OracleBlock 31 := seq (copyOn 0 1 7 (by decide) (by decide) (by decide))
  (seq (unpairOn parsePorts) collect)
noncomputable def allHeader : OracleBlock 31 := seq (headerOn headerPorts) (seq (clear 10) collect)
noncomputable def doubleWidth : OracleBlock 31 := seq (copyOn 2 3 7 (by decide) (by decide) (by decide))
  (copyOn 2 3 7 (by decide) (by decide) (by decide))
noncomputable def program : OracleBlock 31 := seq readHeader (seq allHeader (seq (headCollect 2 false) doubleWidth))

lemma readHeader_executes (g : BitString→ℕ) (xs : BitString) :
    ∃c,readHeader.Executes g (state xs [] [] [] [] [] [])
      (state xs (parse xs).right (parse xs).left [] [(parse xs).ok] [] []) c ∧ c≤8*xs.length+13 := by
  have hc:(copyOn (0:Fin 32) 1 7 (by decide) (by decide) (by decide)).Executes g
      (state xs [] [] [] [] [] []) (state xs xs [] [] [] [] []) (5*xs.length+2) := by
    convert copyOn_executes g (0:Fin 32) 1 7 (by decide) (by decide) (by decide) (state xs [] [] [] [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  have hp:(unpairOn parsePorts).Executes g (state xs xs [] [] [] [] [])
      (state xs (parse xs).right (parse xs).left [] [] [] [(parse xs).ok]) (parseCost xs+2*(parse xs).left.length+1) := by
    apply unpairOn_executes parsePorts g _ _ xs
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 3 rfl).elim
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hp (collect_executes g xs (parse xs).right (parse xs).left [] [] [] _)),?_⟩
  have h:=unpair_cost_bound xs
  omega
lemma allHeader_executes (g : BitString→ℕ) (input data p width flags : BitString) :
    allHeader.Executes g (state input data p width flags [] [])
      (state input data p width (p.all id::flags) [] []) (6*p.length+11) := by
  let st:=state input data p width flags [] []
  let mid:=Function.update (state input data p width flags [] [p.all id]) (10:Fin 32) (List.replicate p.length true)
  have hh:(headerOn headerPorts).Executes g st mid (5*p.length+3) := by
    convert headerOn_executes headerPorts g st p (by funext i;fin_cases i <;> rfl) using 1
    funext i;fin_cases i <;> rfl
  have hz:(clear (10:Fin 32)).Executes g mid (state input data p width flags [] [p.all id]) (p.length+1) := by
    convert clear_executes g (10:Fin 32) mid using 1
    · funext i;fin_cases i <;> rfl
    · simp [mid]
  convert seq_executes _ _ g hh (seq_executes _ _ g hz (collect_executes g input data p width flags [] _)) using 1 <;> omega
lemma doubleWidth_executes (g : BitString→ℕ) (input data p flags : BitString) :
    doubleWidth.Executes g (state input data p [] flags [] []) (state input data p (p++p) flags [] []) (10*p.length+6) := by
  have h1:(copyOn (2:Fin 32) 3 7 (by decide) (by decide) (by decide)).Executes g
      (state input data p [] flags [] []) (state input data p p flags [] []) (5*p.length+2) := by
    convert copyOn_executes g (2:Fin 32) 3 7 (by decide) (by decide) (by decide) (state input data p [] flags [] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  have h2:(copyOn (2:Fin 32) 3 7 (by decide) (by decide) (by decide)).Executes g
      (state input data p p flags [] []) (state input data p (p++p) flags [] []) (5*p.length+2) := by
    convert copyOn_executes g (2:Fin 32) 3 7 (by decide) (by decide) (by decide) (state input data p p flags [] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  convert seq_executes _ _ g h1 h2 using 1 <;> omega
lemma headValue_false (xs : BitString) : headValue false xs=Field.marker xs := by cases xs <;> simp [headValue,Field.marker]
lemma headValue_true (xs : BitString) : headValue true xs= !xs.isEmpty := by cases xs <;> simp [headValue]

theorem program_executes (g : BitString→ℕ) (xs : BitString) :
    ∃c,program.Executes g (Function.update (fun _=>[]) 0 xs)
      (state xs (parse xs).right (Semantics.header xs) (Semantics.width xs) (Semantics.headerFlags xs) [] []) c ∧ c≤100*(xs.length+1) := by
  obtain ⟨a,ha,hab⟩:=readHeader_executes g xs
  have hb:=allHeader_executes g xs (parse xs).right (parse xs).left [] [(parse xs).ok]
  obtain ⟨c,hc,hcb⟩:=headCollect_executes g 2 false xs (parse xs).right (parse xs).left []
    [(parse xs).left.all id,(parse xs).ok] (parse xs).left rfl
  rw [headValue_false] at hc
  have hd:=doubleWidth_executes g xs (parse xs).right (parse xs).left
    [Field.marker (parse xs).left,(parse xs).left.all id,(parse xs).ok]
  have hstart:state xs [] [] [] [] [] []=Function.update (fun _=>[]) 0 xs := by
    funext i;fin_cases i <;> rfl
  rw [hstart] at ha
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd)),?_⟩
  have h:=(parse_lengths xs).1
  omega
end HiddenCircuits.Complexity.EvalValidation.Header
