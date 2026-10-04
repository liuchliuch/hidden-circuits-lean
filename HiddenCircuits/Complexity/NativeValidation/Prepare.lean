import HiddenCircuits.Complexity.NativeValidation.Checks
import HiddenCircuits.Complexity.NativeValidation.ListLoop

namespace HiddenCircuits.Complexity.NativeValidation.Prepare
open OracleBlock GraphVerifier EvalValidation.Core
set_option maxHeartbeats 900000
noncomputable def program : OracleBlock 31 := seq Fields.program Checks.program
def output (xs : BitString) : Store 31 := state xs (Semantics.payload xs) [] (Semantics.header xs) (Semantics.flags xs) [] []
theorem program_executes (g : BitString→ℕ) (xs : BitString) :
    ∃c,program.Executes g (Function.update (fun _=>[]) 0 xs) (output xs) c ∧ c≤1000*(xs.length+1) := by
  obtain ⟨a,ha,hab⟩:=Fields.program_executes g xs
  obtain ⟨b,hb,hbb⟩:=Checks.program_executes g xs (Semantics.payload xs) (Semantics.source xs) (Semantics.target xs)
    (Fields.parsedFlags xs) (Semantics.header xs)
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  obtain ⟨hs,ht,hh,hp⟩:=Fields.lengths xs
  omega
noncomputable def run (deltaMode : Bool) : OracleBlock 31 := seq program (ListLoop.program deltaMode)
def finished (deltaMode : Bool) (xs : BitString) : Store 31 := state xs [] [] (Semantics.header xs)
  (Semantics.runFlags deltaMode (Semantics.header xs) (Semantics.payload xs) (Semantics.flags xs)) [] []
theorem run_executes (g : BitString→ℕ) (deltaMode : Bool) (xs : BitString) :
    ∃c,(run deltaMode).Executes g (Function.update (fun _=>[]) 0 xs) (finished deltaMode xs) c ∧ c≤100000*(xs.length+1)^2 := by
  obtain ⟨a,ha,hab⟩:=program_executes g xs
  obtain ⟨b,hb,hbb⟩:=ListLoop.program_executes g deltaMode xs [] (Semantics.header xs) (Semantics.payload xs) (Semantics.flags xs)
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  obtain ⟨hs,ht,hh,hp⟩:=Fields.lengths xs
  simp only [List.length_nil,Nat.add_zero] at hbb
  have hpow:((Semantics.payload xs).length+(Semantics.header xs).length+1)^2≤(2*xs.length+1)^2:=Nat.pow_le_pow_left (by omega) 2
  nlinarith
end HiddenCircuits.Complexity.NativeValidation.Prepare
