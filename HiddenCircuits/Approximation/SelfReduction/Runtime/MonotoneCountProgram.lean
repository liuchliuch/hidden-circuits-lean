import HiddenCircuits.Approximation.SelfReduction.Runtime.MonotoneCountValue
import HiddenCircuits.Approximation.SelfReduction.Runtime.CountCoreUniform
import HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetupCore

/-! The full encoded counting machine, from arbitrary raw binary input through
validation, polynomial budget generation, tape guard, adaptive counting and
binary estimate cleanup. No initialized state or runtime certificate is input. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.MonotoneCount
open Complexity Complexity.OracleBlock Polynomial
open GraphReduction.MonotoneEndpointEncoding

noncomputable def program : OracleBlock 72 :=
  seq CountSetup.program (branchPop 69 CountSetup.reject CountSetup.reject countCore)

noncomputable def time : Polynomial ℕ := CountSetup.time+uniformCountTime+
  finishTime.comp (X+CountSetup.time+uniformCountTime)+CountSetup.rejectTime.comp (X+CountSetup.time)+6

 theorem program_executes (g : BitString → ℕ) (raw : BitString) :
    ∃ t, program.Executes g (CountSetup.input raw)
      (Function.update (fun _ : Fin 73 => []) 0 (evaluate raw)) t ∧ t ≤ time.eval raw.length := by
  obtain ⟨ts,hs,hbs⟩ := CountSetup.program_executes g raw
  let H := raw.length+CountSetup.time.eval raw.length
  let popped := Function.update (CountSetup.output raw) (69 : Fin 73) []
  have hpopbound (i : Fin 73) : (popped i).length ≤ H := by
    by_cases hi : i=69
    · simp [popped,hi]
    · rw [show popped i=CountSetup.output raw i from Function.update_of_ne hi _ _]
      exact CountSetup.program_storage g raw i
  cases hr : CountSetup.ready raw with
  | false =>
    obtain ⟨tc,hc,hbc⟩ := CountSetup.reject_executes g popped H hpopbound
    have hd := branchPop_false (69 : Fin 73) CountSetup.reject CountSetup.reject countCore g
      (s:=CountSetup.output raw) (rest:=[]) (by rw [CountSetup.output_gate,hr]) hc
    refine ⟨ts+(tc+2)+2,?_,?_⟩
    · simpa only [evaluate_reject raw hr,encodeRatio,if_pos rfl] using seq_executes _ _ g hs hd
    · simp only [time,eval_add,eval_comp,eval_X,eval_ofNat]
      dsimp only [H] at hbc
      omega
  | true =>
    obtain ⟨E,henc,hhead,hdim,hlong⟩ := CountSetup.accepted_input raw hr
    have he : decode (CountSetup.graph raw)=some E := by rw [←henc]; exact decode_encode E
    have hstate : popped=uniformInitial (CountSetup.size raw) E hdim (CountSetup.coins raw) := by
      dsimp only [popped]
      rw [CountSetup.output_core raw E he]
      rw [←henc]
      rfl
    obtain ⟨tc,hc,hbc⟩ := countCore_uniform_executes g (CountSetup.size raw) H E hdim (CountSetup.coins raw) hlong
      (by rw [←hstate]; exact hpopbound)
    rw [←hstate] at hc
    have hd := branchPop_true (69 : Fin 73) CountSetup.reject CountSetup.reject countCore g
      (s:=CountSetup.output raw) (rest:=[]) (by rw [CountSetup.output_gate,hr]) hc
    have hsize := (CountSetup.lengths raw).1
    have hloop := polynomial_nat_eval_mono uniformCountTime hsize
    have hfinish := polynomial_nat_eval_mono finishTime (Nat.add_le_add_left hloop H)
    dsimp only at hloop hfinish
    refine ⟨ts+(tc+2)+2,?_,?_⟩
    · rw [evaluate_accept raw E hr he hdim]
      exact seq_executes _ _ g hs hd
    · simp only [time,eval_add,eval_comp,eval_X,eval_ofNat]
      dsimp only [H] at hbc hfinish
      omega

 theorem program_queryFree : program.QueryFree :=
  seq_queryFree _ _ CountSetup.program_queryFree
    (branchPop_queryFree _ _ _ _ CountSetup.reject_queryFree CountSetup.reject_queryFree countCore_queryFree)

/-- Genuine finite TM2 polynomial time on all raw inputs, including malformed
syntax, invalid graphs and short supplied coin tapes. -/
theorem evaluate_polyTime : PolyTime evaluate := by
  apply polyTime_of_block program program_queryFree time
  intro raw
  obtain ⟨t,ht,hb⟩ := program_executes (fun _ => 0) raw
  refine ⟨Function.update (fun _ : Fin 73 => []) 0 (evaluate raw),t,?_,by simp,hb⟩
  convert ht using 1
  funext i; fin_cases i <;> rfl

end HiddenCircuits.Approximation.SelfReduction.Runtime.MonotoneCount
