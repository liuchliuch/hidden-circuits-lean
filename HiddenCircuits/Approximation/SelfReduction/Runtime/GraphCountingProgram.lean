import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingRawValue
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingCoreUniform
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetupCore

/-! A complete finite raw-input graph-counting machine: physical parsing,
validation, even-order guard, budget generation, sampling, deletion and output. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity Complexity.OracleBlock Polynomial

noncomputable def setup : OracleBlock 106 := rename GraphCountSetup.program basePorts
noncomputable def setupReject : OracleBlock 106 := rename GraphCountSetup.reject basePorts
noncomputable def program : OracleBlock 106 := seq setup (branchPop 69 setupReject setupReject core)
noncomputable def time : Polynomial ℕ := GraphCountSetup.time+uniformCountTime+
  finishTime.comp (X+GraphCountSetup.time+uniformCountTime)+GraphCountSetup.rejectTime.comp (X+GraphCountSetup.time)+6

lemma store_pop (s : Store 72) : Function.update (store s) (69 : Fin 107) []=
    store (Function.update s (69 : Fin 73) []) := by
  funext i; fin_cases i <;> rfl

 theorem program_executes (g : BitString → ℕ) (raw : BitString) :
    ∃t,program.Executes g (store (GraphCountSetup.input raw))
      (Function.update (fun _ : Fin 107 => []) 0 (evaluate raw)) t ∧t≤time.eval raw.length := by
  obtain ⟨ts,hs,hbs⟩ := GraphCountSetup.program_executes g raw
  have hs := store_rename g _ _ _ hs
  let H := raw.length+GraphCountSetup.time.eval raw.length
  let popped := Function.update (GraphCountSetup.output raw) (69 : Fin 73) []
  have hpopbound (i : Fin 73) : (popped i).length≤H := by
    by_cases hi : i=69
    · simp [popped,hi]
    · rw [show popped i=GraphCountSetup.output raw i from Function.update_of_ne hi _ _]
      exact GraphCountSetup.program_storage g raw i
  cases hr : GraphCountSetup.ready raw with
  | false =>
    obtain ⟨tc,hc,hbc⟩ := GraphCountSetup.reject_executes g popped H hpopbound
    have hc := store_rename g _ _ _ hc
    rw [store_clean] at hc
    have hd := branchPop_false (69 : Fin 107) setupReject setupReject core g
      (s:=store (GraphCountSetup.output raw)) (rest:=[])
      (by change GraphCountSetup.output raw 69=[false];rw [GraphCountSetup.output_gate,hr])
      (by rw [store_pop];exact hc)
    refine ⟨ts+(tc+2)+2,?_,?_⟩
    · simpa only [evaluate_reject raw hr,encodeRatio,if_pos rfl] using seq_executes _ _ g hs hd
    · simp only [time,eval_add,eval_comp,eval_X,eval_ofNat]
      dsimp only [H] at hbc
      omega
  | true =>
    obtain ⟨G,henc,hhead,hdim,heven,hlong⟩ := GraphCountSetup.accepted_input raw hr
    have he : GraphInput.decode (GraphCountSetup.graph raw)=some G := by rw [←henc];exact GraphInput.decode_encode G
    have hstate : store popped=uniformInitial (GraphCountSetup.size raw) G (GraphCountSetup.coins raw) := by
      dsimp only [popped]
      rw [GraphCountSetup.output_core raw G he,←henc]
      rfl
    have hfull (i : Fin 107) : (store popped i).length≤H := by
      refine Fin.addCases (m:=73) (n:=34) (fun j => ?_) (fun j => ?_) i
      · change (store popped (basePorts j)).length≤H
        simpa only [store_low] using hpopbound j
      · simp [store]
    obtain ⟨tc,hc,hbc⟩ := core_uniform_executes g (GraphCountSetup.size raw) H G heven hdim (GraphCountSetup.coins raw) hlong
      (by rw [←hstate];exact hfull)
    rw [←hstate] at hc
    have hd := branchPop_true (69 : Fin 107) setupReject setupReject core g
      (s:=store (GraphCountSetup.output raw)) (rest:=[])
      (by change GraphCountSetup.output raw 69=[true];rw [GraphCountSetup.output_gate,hr])
      (by rw [store_pop];exact hc)
    have hsize := (GraphCountSetup.lengths raw).1
    have hloop := polynomial_nat_eval_mono uniformCountTime hsize
    have hfinish := polynomial_nat_eval_mono finishTime (Nat.add_le_add_left hloop H)
    dsimp only at hloop hfinish
    refine ⟨ts+(tc+2)+2,?_,?_⟩
    · rw [evaluate_accept raw G hr he heven hdim]
      exact seq_executes _ _ g hs hd
    · simp only [time,eval_add,eval_comp,eval_X,eval_ofNat]
      dsimp only [H] at hbc hfinish
      omega

lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ GraphCountSetup.program_queryFree)
    (branchPop_queryFree _ _ _ _ (rename_queryFree _ _ GraphCountSetup.reject_queryFree)
      (rename_queryFree _ _ GraphCountSetup.reject_queryFree) core_queryFree)

/-- All raw inputs have an actual TM2 polynomial-time execution; no supplied
sampler, initializer, storage certificate or class test is present. -/
theorem evaluate_polyTime : PolyTime evaluate := by
  apply polyTime_of_block program program_queryFree time
  intro raw
  obtain ⟨t,ht,hb⟩ := program_executes (fun _ => 0) raw
  refine ⟨Function.update (fun _ : Fin 107 => []) 0 (evaluate raw),t,?_,by simp,hb⟩
  convert ht using 1
  funext i;fin_cases i <;> rfl
end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
