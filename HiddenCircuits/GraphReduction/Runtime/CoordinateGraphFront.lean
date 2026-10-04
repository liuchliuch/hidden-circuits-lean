import HiddenCircuits.GraphReduction.Runtime.CoordinateGraphCallbackDefs
import HiddenCircuits.Complexity.LooseWordCount

namespace HiddenCircuits.GraphReduction.Runtime.CoordinateGraph
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic Complexity.GraphVerifier Complexity.GraphVerifier.Runtime
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

def headerMap : Fin 4 ↪ Fin 32 where
  toFun i:=![0,9,27,28] i
  inj':=by decide +kernel
def denominatorMap : Fin 4 ↪ Fin 32 where
  toFun i:=![9,27,28,29] i
  inj':=by decide +kernel
def countMap : Fin 6 ↪ Fin 32 where
  toFun i:=![8,27,28,29,30,0] i
  inj':=by decide +kernel
noncomputable def headerBody : OracleBlock 31 :=seq (unpairOn headerMap) (clear 28)
noncomputable def header : OracleBlock 31 :=branchPop 0 skip headerBody headerBody
noncomputable def front : OracleBlock 31 :=seq header (seq (SignedNormalize.on denominatorMap)
  (seq (moveOn 0 8 27 (by decide) (by decide) (by decide)) (rename LooseWordCount.program countMap)))
def headerOutput (data den : BitString) : Store 31 := fun i=>if i.val=0 then data else if i.val=9 then den else []

lemma headerBody_executes (g : BitString → ℕ) (xs : BitString) :
    ∃c,headerBody.Executes g (Function.update (fun _=>[]) 0 xs)
      (headerOutput (parse xs).right (parse xs).left) c ∧c≤3*xs.length+8 := by
  let s:=Function.update (headerOutput (parse xs).right (parse xs).left) (28:Fin 32) [(parse xs).ok]
  have hp : (unpairOn headerMap).Executes g (Function.update (fun _=>[]) 0 xs) s
      (parseCost xs+2*(parse xs).left.length+1) := by
    apply unpairOn_executes
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have h0:i.val≠0 :=by intro h;exact hi 0 (Fin.ext h.symm)
      have h9:i.val≠9 :=by intro h;exact hi 1 (Fin.ext h.symm)
      have h28:i.val≠28 :=by intro h;exact hi 3 (Fin.ext h.symm)
      simp [s,headerOutput,Function.update_apply,show i≠0 by exact fun h=>h0 (congrArg Fin.val h),
        show i≠28 by exact fun h=>h28 (congrArg Fin.val h),h0,h9]
  have hc : (clear (28:Fin 32)).Executes g s (headerOutput (parse xs).right (parse xs).left) 2 := by
    convert clear_executes g (28:Fin 32) s using 1
    funext i;fin_cases i <;> rfl
  exact ⟨_,seq_executes _ _ g hp hc,by have ht:=unpair_cost_bound xs;omega⟩

lemma header_executes (g : BitString → ℕ) (xs : BitString) :
    ∃c,header.Executes g (Function.update (fun _=>[]) 0 xs)
      (headerOutput (coordinates xs) (LooseWordList.head xs)) c ∧c≤6*xs.length+20 := by
  cases xs with
  | nil =>
    refine ⟨3,?_,by simp⟩
    apply branchPop_empty (0:Fin 32) _ _ _ g rfl
    convert skip_executes g (fun _ : Fin 32=> ([]:BitString)) using 1
    · funext i;simp
    · funext i;simp [headerOutput,coordinates,LooseWordList.tail,LooseWordList.head]
  | cons b bs =>
    obtain ⟨c,hc,hb⟩:=headerBody_executes g bs
    have hu : Function.update (Function.update (fun _ : Fin 32=>[]) 0 (b::bs)) 0 bs=
        Function.update (fun _ : Fin 32=>[]) 0 bs := by simp
    cases b
    · exact ⟨c+2,branchPop_false (0:Fin 32) _ _ _ g rfl (by rw [hu];exact hc),by simp;omega⟩
    · exact ⟨c+2,branchPop_true (0:Fin 32) _ _ _ g rfl (by rw [hu];exact hc),by simp;omega⟩

lemma head_length (xs : BitString) : (LooseWordList.head xs).length≤xs.length := by
  cases xs with
  | nil => rfl
  | cons b bs => exact (parse_lengths bs).1.trans (by simp)
lemma denominator_length (xs : BitString) : (signedBits (denominator xs)).length≤xs.length+1 :=
  (SignedNormalize.signed_length _).trans (by have h:=head_length xs;omega)

theorem front_executes (g : BitString → ℕ) (xs : BitString) :
    ∃c,front.Executes g (Function.update (fun _=>[]) 0 xs)
      (callbackState (LooseWordList.words (coordinates xs)).length 0 0 [] [] [] (coordinates xs) (denominator xs)) c ∧
      c≤100*(xs.length+1)^2 := by
  let data:=coordinates xs
  let den:=LooseWordList.head xs
  let d:=denominator xs
  let s1:=headerOutput data den
  let s2:=headerOutput data (signedBits d)
  let s3:=params data d
  obtain ⟨a,ha,hba⟩:=header_executes g xs
  obtain ⟨b,hb,hbb⟩:=SignedNormalize.on_executes denominatorMap g s1 den (by funext i;fin_cases i <;> rfl)
  have h2 : (SignedNormalize.on denominatorMap).Executes g s1 s2 b := by
    convert hb using 1
    funext i;fin_cases i <;> rfl
  have h3 : (moveOn (0:Fin 32) 8 27 (by decide) (by decide) (by decide)).Executes g s2 s3 (6*data.length+5) := by
    convert moveOn_executes g (0:Fin 32) 8 27 (by decide) (by decide) (by decide) s2 rfl using 1
    funext i;fin_cases i <;> simp [s2,s3,params,headerOutput]
  obtain ⟨c,hc,hbc⟩:=LooseWordCount.program_executes g data
  have h4 : (rename LooseWordCount.program countMap).Executes g s3
      (callbackState (LooseWordList.words data).length 0 0 [] [] [] data d) c := by
    apply rename_executes_to _ countMap g hc
    · clear hc;funext i;fin_cases i <;> rfl
    · clear hc;funext i;fin_cases i <;> rfl
    · clear hc;intro i hi
      fin_cases i <;> first | rfl | exact (hi 5 rfl).elim
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  have hl:=coordinate_length xs
  have hh:=head_length xs
  dsimp only [data,den] at hbc hbb ⊢
  have hs:((coordinates xs).length+1)^2≤(xs.length+1)^2 :=by gcongr
  nlinarith

lemma front_queryFree : front.QueryFree := seq_queryFree _ _
  (branchPop_queryFree _ _ _ _ skip_queryFree
    (seq_queryFree _ _ (unpairOn_queryFree _) (clear_queryFree _))
    (seq_queryFree _ _ (unpairOn_queryFree _) (clear_queryFree _)))
  (seq_queryFree _ _ (SignedNormalize.on_queryFree _) (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
    (rename_queryFree _ _ LooseWordCount.program_queryFree)))
end HiddenCircuits.GraphReduction.Runtime.CoordinateGraph
