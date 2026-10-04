import HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioSign
import HiddenCircuits.DH.Runtime.FactorialInto
import HiddenCircuits.Complexity.BinaryArithmetic.PowerRuntime

/-! Fresh reconstruction: factorial and powering performed on physical stacks;
no arithmetic answer is supplied to the machine. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioNormalization
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 800000

def factorialEmbedding : Fin 9 ↪ Fin 22 where
  toFun i := ![0,3,5,6,7,8,9,10,11] i
  inj' := by decide +kernel
def powerEmbedding : Fin 17 ↪ Fin 22 where
  toFun i := ![3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20] i
  inj' := by decide +kernel
noncomputable def factorial : OracleBlock 21 := DH.Runtime.FactorialInto.on factorialEmbedding
noncomputable def power : OracleBlock 21 := rename PowerRuntime.program powerEmbedding
noncomputable def program : OracleBlock 21 := seq factorial
  (seq (copyOn 1 5 6 (by decide) (by decide) (by decide)) (seq power signProgram))
noncomputable def time : Polynomial ℕ := DH.Runtime.FactorialInto.time+
  PowerRuntime.time.comp (X^2+X+2)+6*X^2+14*X+20

lemma factorial_executes (g : BitString → ℕ) (s h p : ℕ) :
    ∃c, factorial.Executes g (state s h p [] [])
      (state s h p (signedBits (s.factorial:ℤ)) []) c ∧ c≤DH.Runtime.FactorialInto.time.eval s := by
  obtain ⟨c,hc,hb⟩ := DH.Runtime.FactorialInto.on_executes factorialEmbedding g
    (state s h p [] []) (List.replicate s true) (by funext i;fin_cases i <;> rfl)
  simp only [List.length_replicate] at hc hb
  refine ⟨c,?_,hb⟩
  convert hc using 1
  funext i;fin_cases i <;> rfl

lemma power_executes (g : BitString → ℕ) (s h p : ℕ) :
    ∃c, power.Executes g
      (Function.update (state s h p (signedBits (s.factorial:ℤ)) []) (5:Fin 22) (List.replicate h true))
      (state s h p (signedBits ((s.factorial:ℤ)^h)) []) c ∧
      c≤PowerRuntime.time.eval ((signedBits (s.factorial:ℤ)).length+h) := by
  obtain ⟨c,hc,hb⟩ := PowerRuntime.program_executes g (s.factorial:ℤ) (List.replicate h true)
  simp only [List.length_replicate] at hc hb
  refine ⟨c,?_,hb⟩
  apply rename_executes_to PowerRuntime.program powerEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h3 : i.val≠3 := by intro h;exact hi 0 (Fin.ext h.symm)
    have h5 : i.val≠5 := by intro h;exact hi 1 (Fin.ext h.symm)
    have hi5 : i≠(5:Fin 22) := fun h => h5 (congrArg Fin.val h)
    simp only [Function.update_of_ne hi5,state,h3,if_false]

theorem program_executes (g : BitString → ℕ) (s h p : ℕ) :
    ∃c, program.Executes g (state s h p [] [])
      (state s h p (signedBits ((s.factorial:ℤ)^h)) (signedBits ((-1:ℤ)^(p*h)))) c ∧
      c≤time.eval (s+h+p) := by
  obtain ⟨a,ha,hab⟩ := factorial_executes g s h p
  have hb := copyOn_executes g (1:Fin 22) 5 6 (by decide) (by decide) (by decide)
    (state s h p (signedBits (s.factorial:ℤ)) []) rfl
  change (copyOn (1:Fin 22) 5 6 (by decide) (by decide) (by decide)).Executes g _ _ (5*(List.replicate h true).length+2) at hb
  simp only [List.length_replicate] at hb
  simp [state] at hb
  obtain ⟨c,hc,hcb⟩ := power_executes g s h p
  have hd := signProgram_executes g s h p (signedBits ((s.factorial:ℤ)^h))
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd)),?_⟩
  have hf := polynomial_nat_eval_mono DH.Runtime.FactorialInto.time (show s≤s+h+p by omega)
  have hlen : (signedBits (s.factorial:ℤ)).length≤s*s+2 := by
    have hh := factorial_binary_length s
    simp only [DH.Runtime.FactorialInto.signed_nat,List.length_cons]
    omega
  have hp := polynomial_nat_eval_mono PowerRuntime.time
    (show (signedBits (s.factorial:ℤ)).length+h≤(s+h+p)^2+(s+h+p)+2 by nlinarith)
  simp only [time,eval_add,eval_mul,eval_comp,eval_pow,eval_X,eval_ofNat]
  dsimp only at hf hp
  nlinarith

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (DH.Runtime.FactorialInto.on_queryFree _)
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ PowerRuntime.program_queryFree) signProgram_queryFree))
end HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioNormalization
