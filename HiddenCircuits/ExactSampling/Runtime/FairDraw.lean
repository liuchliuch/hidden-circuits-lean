import HiddenCircuits.ExactSampling.FairFill
import HiddenCircuits.ExactSampling.Runtime.RejectionTrial

/-! An actual finite fair-coin rejection driver. Binary count and unary width
are persistent physical stacks. Every retry redraws all width bits, calls the
fixed comparison code, and clears the old proposal. Acceptance normalizes the
retained binary rank and clears both count and width. -/
namespace HiddenCircuits.ExactSampling.Runtime.FairDraw
open Complexity OracleBlock BinaryArithmetic Approximation Approximation.FiniteChains Rejection
set_option maxHeartbeats 1800000

 def state (graph bound width sample clock flag work1 work2 work3 scratch : BitString) : Store 65 := fun i =>
  if i.val=0 then graph else if i.val=1 then sample else if i.val=3 then clock
  else if i.val=4 then bound else if i.val=5 then flag else if i.val=6 then width
  else if i.val=7 then work1 else if i.val=8 then work2 else if i.val=9 then work3
  else if i.val=10 then scratch else []

 def ready (graph : BitString) (n : ℕ) (sample clock flag : BitString) : Store 65 :=
  state graph (Computability.encodeNat n) (List.replicate (width n) true) sample clock flag [] [] [] []
 def result (graph : BitString) (i : ℕ) : Store 65 :=
  state graph [] [] (Computability.encodeNat i) [] [] [] [] [] []

 def trialPorts : Fin 7↪Fin 66 := ⟨fun i => ![4,1,5,7,8,9,10] i,by decide +kernel⟩
 def normalizePorts : Fin 4↪Fin 66 := ⟨fun i => ![1,4,7,5] i,by decide +kernel⟩
 noncomputable def trial : OracleBlock 65 := rename RejectionTrial.program trialPorts
 noncomputable def reject : OracleBlock 65 := seq (clear 1) (push 3 true)
 noncomputable def accept : OracleBlock 65 := seq (clear 4)
   (seq (rename subBlock normalizePorts) (seq (clear 5) (clear 6)))
 noncomputable def draw : FairCode 65 := .seq
   (.block (copyOn 6 7 10 (by decide) (by decide) (by decide))) (FairFill.program 7 1)
 noncomputable def body : FairCode 65 := .seq draw (.seq (.block trial)
   (.branchPop 5 (.block reject) (.block reject) (.block accept)))
 noncomputable def loop : FairCode 65 := .whilePop 3 body body

 theorem draw_runs (graph : BitString) (n : ℕ) (r : CoinTape (width n)) :
    FairCode.Runs draw (ready graph n [] [] []) (ready graph n (List.ofFn r) [] [])
      (List.ofFn r).reverse (8*width n+5) := by
  have hc : (copyOn (6:Fin 66) 7 10 (by decide) (by decide) (by decide)).Executes (fun _=>0)
      (ready graph n [] [] [])
      (state graph (Computability.encodeNat n) (List.replicate (width n) true) [] [] []
        (List.replicate (width n) true) [] [] []) (5*width n+2) := by
    convert copyOn_executes (fun _=>0) (6:Fin 66) 7 10 (by decide) (by decide) (by decide)
      (ready graph n [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [ready,state]
    · simp [ready,state]
  have hf := FairFill.runs (7:Fin 66) 1 (by decide) (ready graph n [] [] []) (List.ofFn r).reverse []
  have hfi : FairFill.state (ready graph n [] [] []) 7 1 ((List.ofFn r).reverse.length) []=
      state graph (Computability.encodeNat n) (List.replicate (width n) true) [] [] []
        (List.replicate (width n) true) [] [] [] := by
    funext i;fin_cases i <;> simp [FairFill.state,ready,state]
  have hfo : FairFill.state (ready graph n [] [] []) 7 1 0 ((List.ofFn r).reverse.reverse++[])=
      ready graph n (List.ofFn r) [] [] := by
    funext i;fin_cases i <;> simp [FairFill.state,ready,state]
  rw [hfi,hfo] at hf
  have hh := FairCode.Runs.seq (FairCode.Runs.block hc) hf
  convert hh using 1 <;> simp <;> omega

 theorem trial_executes (graph : BitString) (n : ℕ) (r : CoinTape (width n)) :
    ∃t,trial.Executes (fun _=>0) (ready graph n (List.ofFn r) [] [])
      (ready graph n (List.ofFn r) [] [decide ((attempt n r).isSome)]) t ∧t≤60*(Nat.size n+1) := by
  obtain ⟨t,ht,hb⟩ := RejectionTrial.trial_executes (fun _=>0) n r
  refine ⟨t,?_,hb⟩
  apply rename_executes_to RejectionTrial.program trialPorts (fun _=>0) ht
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h5 : i.val≠5 := by intro h;exact hi 2 (Fin.ext h.symm)
    simp [ready,state,h5]

 theorem reject_executes (graph : BitString) (n : ℕ) (r : CoinTape (width n)) :
    reject.Executes (fun _=>0) (ready graph n (List.ofFn r) [] []) (ready graph n [] [true] []) (width n+4) := by
  have h1 : (clear (1:Fin 66)).Executes (fun _=>0)
      (ready graph n (List.ofFn r) [] []) (ready graph n [] [] []) (width n+1) := by
    convert clear_executes (fun _=>0) (1:Fin 66) _ using 1
    · funext i;fin_cases i <;> simp [ready,state]
    · simp [ready,state]
  have h2 : (push (3:Fin 66) true).Executes (fun _=>0)
      (ready graph n [] [] []) (ready graph n [] [true] []) 1 := by
    convert push_executes (fun _=>0) (3:Fin 66) true _ using 1
    funext i;fin_cases i <;> simp [ready,state]
  convert seq_executes _ _ (fun _=>0) h1 h2 using 1 <;> omega

 theorem accept_executes (graph : BitString) (n : ℕ) (r : CoinTape (width n)) :
    ∃t,accept.Executes (fun _=>0) (ready graph n (List.ofFn r) [] [])
      (result graph (tapeNumber (width n) r).val) t ∧t≤15*(Nat.size n+1) := by
  let mid := state graph [] (List.replicate (width n) true) (List.ofFn r) [] [] [] [] [] []
  let normalized := state graph [] (List.replicate (width n) true)
    (Computability.encodeNat (tapeNumber (width n) r).val) [] [false] [] [] [] []
  let cleanFlag := state graph [] (List.replicate (width n) true)
    (Computability.encodeNat (tapeNumber (width n) r).val) [] [] [] [] [] []
  have h1 : (clear (4:Fin 66)).Executes (fun _=>0) (ready graph n (List.ofFn r) [] []) mid (Nat.size n+1) := by
    convert clear_executes (fun _=>0) (4:Fin 66) _ using 1
    · funext i;fin_cases i <;> simp [mid,ready,state]
    · simp [ready,state,encodeNat_length]
  have hs := subBlock_executes (fun _=>0) (List.ofFn r) []
  rw [subtractBits_correct,value_ofFn,value_nil,Nat.sub_zero] at hs
  have hflag : (subRaw (List.ofFn r) [] false).2=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hh := (subRaw_borrow (List.ofFn r) []).mp h
    simpa only [value_nil,Nat.not_lt_zero] using hh
  rw [hflag] at hs
  have h2 : (rename subBlock normalizePorts).Executes (fun _=>0) mid normalized (subCost (List.ofFn r) []) := by
    apply rename_executes_to subBlock normalizePorts (fun _=>0) hs
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have h1 : i.val≠1 := by intro h;exact hi 0 (Fin.ext h.symm)
      have h5 : i.val≠5 := by intro h;exact hi 3 (Fin.ext h.symm)
      simp [mid,normalized,state,h1,h5]
  have h3 : (clear (5:Fin 66)).Executes (fun _=>0) normalized cleanFlag 2 := by
    convert clear_executes (fun _=>0) (5:Fin 66) _ using 1
    funext i;fin_cases i <;> simp [normalized,cleanFlag,state]
  have h4 : (clear (6:Fin 66)).Executes (fun _=>0) cleanFlag (result graph (tapeNumber (width n) r).val)
      (width n+1) := by
    convert clear_executes (fun _=>0) (6:Fin 66) _ using 1
    · funext i;fin_cases i <;> simp [cleanFlag,result,state]
    · simp [cleanFlag,state]
  have hb := subCost_bound (List.ofFn r) []
  simp only [List.length_ofFn,List.length_nil,Nat.max_zero] at hb
  have hw := width_le_size n
  refine ⟨_,seq_executes _ _ (fun _=>0) h1 (seq_executes _ _ (fun _=>0) h2 (seq_executes _ _ (fun _=>0) h3 h4)),?_⟩
  omega

 theorem body_reject (graph : BitString) (n : ℕ) (r : Rejected n) :
    ∃t,FairCode.Runs body (ready graph n [] [] []) (ready graph n [] [true] [])
      (List.ofFn r.val).reverse t ∧t≤100*(Nat.size n+1) := by
  obtain ⟨t,ht,hb⟩ := trial_executes graph n r.val
  rw [r.property] at ht
  simp only [Option.isSome_none] at ht
  have hp : Function.update (ready graph n (List.ofFn r.val) [] [false]) (5:Fin 66) []=
      ready graph n (List.ofFn r.val) [] [] := by
    funext i;fin_cases i <;> simp [ready,state]
  have hbranch := FairCode.Runs.branchFalse (q:=(5:Fin 66))
    (E:=.block reject) (B:=.block reject) (C:=.block accept)
    (s:=ready graph n (List.ofFn r.val) [] [false]) (rest:=[]) rfl
    (by rw [hp];exact FairCode.Runs.block (reject_executes graph n r.val))
  have hh := FairCode.Runs.seq (draw_runs graph n r.val) (FairCode.Runs.seq (FairCode.Runs.block ht) hbranch)
  refine ⟨8*width n+5+(t+(width n+4+2)+2)+2,?_,?_⟩
  · simpa only [List.append_nil,List.nil_append] using hh
  · have hw := width_le_size n;omega

 theorem body_accept {n : ℕ} (hn : 0<n) (graph : BitString) (i : Fin n) :
    ∃t,FairCode.Runs body (ready graph n [] [] []) (result graph i.val)
      (List.ofFn (acceptedTape hn i)).reverse t ∧t≤110*(Nat.size n+1) := by
  obtain ⟨t,ht,hb⟩ := trial_executes graph n (acceptedTape hn i)
  rw [attempt_accepted] at ht
  simp only [Option.isSome_some] at ht
  obtain ⟨a,ha,hab⟩ := accept_executes graph n (acceptedTape hn i)
  simp only [acceptedTape,Equiv.apply_symm_apply] at ha
  have hp : Function.update (ready graph n (List.ofFn (acceptedTape hn i)) [] [true]) (5:Fin 66) []=
      ready graph n (List.ofFn (acceptedTape hn i)) [] [] := by
    funext i;fin_cases i <;> simp [ready,state]
  have hbranch := FairCode.Runs.branchTrue (q:=(5:Fin 66))
    (E:=.block reject) (B:=.block reject) (C:=.block accept)
    (s:=ready graph n (List.ofFn (acceptedTape hn i)) [] [true]) (rest:=[]) rfl
    (by rw [hp];exact FairCode.Runs.block ha)
  have hh := FairCode.Runs.seq (draw_runs graph n (acceptedTape hn i))
    (FairCode.Runs.seq (FairCode.Runs.block ht) hbranch)
  refine ⟨8*width n+5+(t+(a+2)+2)+2,?_,?_⟩
  · simpa only [List.append_nil,List.nil_append] using hh
  · have hw := width_le_size n;omega

end HiddenCircuits.ExactSampling.Runtime.FairDraw
