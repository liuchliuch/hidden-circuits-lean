import HiddenCircuits.Approximation.SelfReduction.Runtime.CountFinishPrepare
import HiddenCircuits.Approximation.SelfReduction.Runtime.EstimateOutput
import HiddenCircuits.Complexity.OracleCleanup

/-! Final binary estimate assembly and whole-core cleanup, with a polynomial
bound derived from the preceding loop's actual stack-height bound. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity Complexity.OracleBlock Polynomial

def finishOutputPorts : Fin 21 ↪ Fin 73 where
  toFun i := i.castAdd 52
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 73 => x.val) h)

def finishAfter (graph : BitString) (T cap groups N : ℕ) (word : BitString) : Store 72 := fun i =>
  if i.val=0 then word else if i.val=62 then List.replicate (8*T) true else if i.val=63 then List.replicate cap true
  else if i.val=64 then List.replicate groups true else if i.val=65 then graph else if i.val=66 then List.replicate T true
  else if i.val=72 then List.replicate N true else []

noncomputable def countFinish : OracleBlock 72 :=
  seq finishPrepare (seq (rename EstimateOutput.program finishOutputPorts) (cleanup 0))
noncomputable def finishTime : Polynomial ℕ := 74*(22*X+EstimateOutput.time.comp (3*X+1)+35)+73*X+300

 theorem finishOutput_executes (g : BitString → ℕ) (graph : BitString) (M d T cap groups N : ℕ)
    (out alive word : BitString) (cost : ℕ)
    (h : EstimateOutput.program.Executes g
      (EstimateOutput.state (List.replicate M true) (List.replicate d true) out.reverse alive)
      (EstimateOutput.clean word) cost) :
    (rename EstimateOutput.program finishOutputPorts).Executes g
      (finishTarget graph M d T cap groups N out alive) (finishAfter graph T cap groups N word) cost := by
  apply rename_executes_to EstimateOutput.program finishOutputPorts g h
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · intro j hj
    have h0 : j.val≠0 := by intro h; exact hj 0 (Fin.ext h.symm)
    have h1 : j.val≠1 := by intro h; exact hj 1 (Fin.ext h.symm)
    have h2 : j.val≠2 := by intro h; exact hj 2 (Fin.ext h.symm)
    have h3 : j.val≠3 := by intro h; exact hj 3 (Fin.ext h.symm)
    simp [finishTarget,finishAfter,h0,h1,h2,h3]

 theorem countFinish_from_helper (g : BitString → ℕ) (coins graph : BitString) (width M T cap groups : ℕ)
    (out alive : BitString) (d N H : ℕ) (word : BitString)
    (hs : ∀ i, (finishSource coins graph width M T cap groups out alive d N i).length ≤ H)
    (hh : ∃ t, EstimateOutput.program.Executes g
      (EstimateOutput.state (List.replicate M true) (List.replicate d true) out.reverse alive)
      (EstimateOutput.clean word) t ∧ t ≤ EstimateOutput.time.eval (M+d+out.length+1)) :
    ∃ t, countFinish.Executes g (finishSource coins graph width M T cap groups out alive d N)
      (Function.update (fun _ : Fin 73 => []) 0 word) t ∧ t ≤ finishTime.eval H := by
  have hp := finishPrepare_executes g coins graph width M T cap groups out alive d N
  obtain ⟨th,hh,hbh⟩ := hh
  have he := finishOutput_executes g graph M d T cap groups N out alive word th hh
  have hc := hs 0
  have hm := hs 59
  have hd := hs 71
  have hw := hs 2
  have ho := hs 68
  have ha := hs 70
  change coins.length ≤ H at hc
  change (List.replicate M true).length ≤ H at hm
  change (List.replicate d true).length ≤ H at hd
  change (List.replicate width true).length ≤ H at hw
  change out.length ≤ H at ho
  change alive.length ≤ H at ha
  simp only [List.length_replicate] at hm hd hw
  let tp := coins.length+6*M+6*d+width+2*out.length+6*alive.length+28
  have htp : tp ≤ 22*H+28 := by dsimp [tp]; omega
  have hth : th ≤ EstimateOutput.time.eval (3*H+1) :=
    hbh.trans (polynomial_nat_eval_mono _ (by omega))
  have hcombined := seq_executes _ _ g hp he
  obtain ⟨tc,htc,hbtc⟩ := cleanup_executes g (0 : Fin 73) (finishAfter graph T cap groups N word)
    (H+(tp+th+2)) (hcombined.stack_bound hs)
  have hout : finishAfter graph T cap groups N word 0=word := rfl
  rw [hout] at htc
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g he htc),?_⟩
  simp only [finishTime,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat,eval_one]
  change tp+(th+tc+2)+2 ≤ 74*(22*H+EstimateOutput.time.eval (3*H+1)+35)+73*H+300
  omega

 theorem countFinish_success (g : BitString → ℕ) (coins graph : BitString) (width M T cap groups d N H : ℕ)
    (xs : List ℕ) (hlen : xs.length=d) (hpos : ∀ c ∈ xs, 0 < c)
    (hs : ∀ i, (finishSource coins graph width M T cap groups (unaryValues xs).reverse [true] d N i).length ≤ H) :
    ∃ t, countFinish.Executes g
      (finishSource coins graph width M T cap groups (unaryValues xs).reverse [true] d N)
      (Function.update (fun _ : Fin 73 => []) 0 (reciprocalProductOutput M xs)) t ∧ t ≤ finishTime.eval H := by
  apply countFinish_from_helper g coins graph width M T cap groups (unaryValues xs).reverse [true] d N H _ hs
  obtain ⟨t,ht,hb⟩ := EstimateOutput.program_success g M d xs hlen hpos
  refine ⟨t,?_,?_⟩
  · simpa only [List.reverse_reverse] using ht
  · simpa only [EstimateOutput.inputSize,List.length_reverse] using hb

 theorem countFinish_zero (g : BitString → ℕ) (coins graph : BitString) (width M T cap groups : ℕ)
    (out : BitString) (d N H : ℕ)
    (hs : ∀ i, (finishSource coins graph width M T cap groups out [] d N i).length ≤ H) :
    ∃ t, countFinish.Executes g (finishSource coins graph width M T cap groups out [] d N)
      (Function.update (fun _ : Fin 73 => []) 0 (encodeRatio 0 0)) t ∧ t ≤ finishTime.eval H := by
  apply countFinish_from_helper g coins graph width M T cap groups out [] d N H _ hs
  simpa only [List.length_reverse] using EstimateOutput.program_zero_raw g M d out.reverse

 theorem countFinish_queryFree : countFinish.QueryFree :=
  seq_queryFree _ _ finishPrepare_queryFree (seq_queryFree _ _
    (rename_queryFree _ _ EstimateOutput.program_queryFree) (cleanup_queryFree _))

end HiddenCircuits.Approximation.SelfReduction.Runtime
