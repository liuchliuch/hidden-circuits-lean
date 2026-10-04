import HiddenCircuits.GraphReduction.Runtime.WordGraph.OddFactorialRuntime
import HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioNormalization

/-! Fresh physical normalization for the unit/private clique-probe ratios. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.OddFactorialNormalization
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 900000
abbrev state := RatioNormalization.state
def exponent (mode : Bool) (h : ℕ) : ℕ := if mode then 2*h+1 else h+1
def signValue (mode : Bool) (h p : ℕ) : ℤ := if mode then 1 else (-1:ℤ)^(p*h)
noncomputable def factorial : OracleBlock 21 := seq (copyOn 0 3 5 (by decide) (by decide) (by decide))
  (rename OddFactorialRuntime.program RatioNormalization.powerEmbedding)
noncomputable def clock (mode : Bool) : OracleBlock 21 :=
  seq (copyOn 1 5 6 (by decide) (by decide) (by decide))
    (if mode then seq (copyOn 1 5 6 (by decide) (by decide) (by decide)) (push 5 true) else push 5 true)
noncomputable def sign (mode : Bool) : OracleBlock 21 :=
  if mode then seq (push 4 true) (push 4 false) else RatioNormalization.signProgram
noncomputable def program (mode : Bool) : OracleBlock 21 :=
  seq factorial (seq (clock mode) (seq RatioNormalization.power (sign mode)))
noncomputable def time : Polynomial ℕ := OddFactorialRuntime.time+
  PowerRuntime.time.comp (2*X^2+2*X+3)+6*X^2+24*X+40

lemma factorial_executes (g : BitString → ℕ) (s h p : ℕ) :
    ∃c, factorial.Executes g (state s h p [] []) (state s h p (signedBits (oddFactorial s:ℤ)) []) c ∧
      c ≤ OddFactorialRuntime.time.eval s+5*s+4 := by
  let start := state s h p [] []
  let middle := Function.update start (3:Fin 22) (List.replicate s true)
  have hcopy : (copyOn (0:Fin 22) 3 5 (by decide) (by decide) (by decide)).Executes g start middle (5*s+2) := by
    simpa [start,middle,RatioNormalization.state] using copyOn_executes g (0:Fin 22) 3 5 (by decide) (by decide) (by decide) start rfl
  obtain ⟨c,hc,hb⟩ := OddFactorialRuntime.program_executes g (List.replicate s true)
  simp only [List.length_replicate] at hc hb
  have hrun : (rename OddFactorialRuntime.program RatioNormalization.powerEmbedding).Executes g middle
      (state s h p (signedBits (oddFactorial s:ℤ)) []) c := by
    apply rename_executes_to OddFactorialRuntime.program RatioNormalization.powerEmbedding g hc
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have h3 : i.val≠3 := by intro h;exact hi 0 (Fin.ext h.symm)
      have hi3 : i≠(3:Fin 22) := fun h => h3 (congrArg Fin.val h)
      simp only [middle,start,Function.update_of_ne hi3,RatioNormalization.state,h3,if_false]
  exact ⟨_,seq_executes _ _ g hcopy hrun,by omega⟩

lemma clock_executes (g : BitString → ℕ) (mode : Bool) (s h p : ℕ) (factor : BitString) :
    ∃c, (clock mode).Executes g (state s h p factor [])
      (Function.update (state s h p factor []) (5:Fin 22) (List.replicate (exponent mode h) true)) c ∧ c ≤ 10*h+9 := by
  let start := state s h p factor []
  let one := Function.update start (5:Fin 22) (List.replicate h true)
  let two := Function.update start (5:Fin 22) (List.replicate (2*h) true)
  have h1 : (copyOn (1:Fin 22) 5 6 (by decide) (by decide) (by decide)).Executes g start one (5*h+2) := by
    simpa [start,one,RatioNormalization.state] using copyOn_executes g (1:Fin 22) 5 6 (by decide) (by decide) (by decide) start rfl
  have h2 : (copyOn (1:Fin 22) 5 6 (by decide) (by decide) (by decide)).Executes g one two (5*h+2) := by
    simpa [start,one,two,RatioNormalization.state,←List.replicate_add,two_mul] using
      copyOn_executes g (1:Fin 22) 5 6 (by decide) (by decide) (by decide) one rfl
  cases mode
  · have hp := push_executes g (5:Fin 22) true one
    simp only [one,Function.update_self,Function.update_idem] at hp
    rw [←List.replicate_succ] at hp
    exact ⟨_,seq_executes _ _ g h1 hp,by omega⟩
  · have hp := push_executes g (5:Fin 22) true two
    simp only [two,Function.update_self,Function.update_idem] at hp
    rw [←List.replicate_succ] at hp
    exact ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 hp),by omega⟩

lemma power_executes (g : BitString → ℕ) (s h p e : ℕ) (factor : ℤ) :
    ∃c, RatioNormalization.power.Executes g
      (Function.update (state s h p (signedBits factor) []) (5:Fin 22) (List.replicate e true))
      (state s h p (signedBits (factor^e)) []) c ∧ c ≤ PowerRuntime.time.eval ((signedBits factor).length+e) := by
  obtain ⟨c,hc,hb⟩ := PowerRuntime.program_executes g factor (List.replicate e true)
  simp only [List.length_replicate] at hc hb
  refine ⟨c,?_,hb⟩
  apply rename_executes_to PowerRuntime.program RatioNormalization.powerEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h3 : i.val≠3 := by intro h;exact hi 0 (Fin.ext h.symm)
    have h5 : i.val≠5 := by intro h;exact hi 1 (Fin.ext h.symm)
    have hi5 : i≠(5:Fin 22) := fun h => h5 (congrArg Fin.val h)
    simp only [Function.update_of_ne hi5,RatioNormalization.state,h3,if_false]

lemma sign_executes (g : BitString → ℕ) (mode : Bool) (s h p : ℕ) (factor : BitString) :
    ∃c, (sign mode).Executes g (state s h p factor [])
      (state s h p factor (signedBits (signValue mode h p))) c ∧ c ≤ 6*p*h+9*h+12 := by
  cases mode
  · exact ⟨_,RatioNormalization.signProgram_executes g s h p factor,le_refl _⟩
  · have h1 := push_executes g (4:Fin 22) true (state s h p factor [])
    have h2 := push_executes g (4:Fin 22) false (Function.update (state s h p factor []) (4:Fin 22) [true])
    have hh := seq_executes _ _ g h1 h2
    refine ⟨4,?_,by omega⟩
    convert hh using 1
    funext i;fin_cases i <;> first | rfl | (change signedBits (1:ℤ)=[false,true];decide)

theorem program_executes (g : BitString → ℕ) (mode : Bool) (s h p : ℕ) :
    ∃c, (program mode).Executes g (state s h p [] [])
      (state s h p (signedBits ((oddFactorial s:ℤ)^(exponent mode h))) (signedBits (signValue mode h p))) c ∧
      c ≤ time.eval (s+h+p) := by
  obtain ⟨a,ha,hab⟩ := factorial_executes g s h p
  obtain ⟨b,hb,hbb⟩ := clock_executes g mode s h p (signedBits (oddFactorial s:ℤ))
  obtain ⟨c,hc,hcb⟩ := power_executes g s h p (exponent mode h) (oddFactorial s:ℤ)
  obtain ⟨d,hd,hdb⟩ := sign_executes g mode s h p (signedBits ((oddFactorial s:ℤ)^(exponent mode h)))
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd)),?_⟩
  have hf := polynomial_nat_eval_mono OddFactorialRuntime.time (show s ≤ s+h+p by omega)
  have hlen : (signedBits (oddFactorial s:ℤ)).length ≤ 2*s*s+2 :=
    signedBits_length_of_abs_bound (by simpa using OddFactorialRuntime.oddFactorial_bound s)
  have he : exponent mode h ≤ 2*h+1 := by cases mode <;> simp [exponent] <;> omega
  have hp := polynomial_nat_eval_mono PowerRuntime.time
    (show (signedBits (oddFactorial s:ℤ)).length+exponent mode h ≤ 2*(s+h+p)^2+2*(s+h+p)+3 by nlinarith)
  simp only [time,eval_add,eval_mul,eval_comp,eval_pow,eval_X,eval_ofNat]
  dsimp only at hf hp
  nlinarith

lemma program_queryFree (mode : Bool) : (program mode).QueryFree := by
  apply seq_queryFree
  · exact seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (rename_queryFree _ _ OddFactorialRuntime.program_queryFree)
  · apply seq_queryFree
    · cases mode <;> exact seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (by
        first | exact push_queryFree _ _ | exact seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (push_queryFree _ _))
    · apply seq_queryFree
      · exact rename_queryFree _ _ PowerRuntime.program_queryFree
      · cases mode
        · exact RatioNormalization.signProgram_queryFree
        · exact seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _)
end HiddenCircuits.GraphReduction.Runtime.WordGraph.OddFactorialNormalization
