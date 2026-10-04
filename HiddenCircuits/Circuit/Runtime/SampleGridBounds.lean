import HiddenCircuits.Circuit.Runtime.SampleEmitterRuntime
import HiddenCircuits.Circuit.Runtime.SampleDimensions
import HiddenCircuits.Circuit.Runtime.SourceQueryRecovery

/-! Uniform dimensions, actual emission time and byte
bounds at every node of the real spectral/geometric source grid. -/
namespace HiddenCircuits.Circuit.Runtime.SampleGridBounds
open HiddenCircuits.Complexity OracleBlock Polynomial SourceQueryRecovery

noncomputable def inputSize : Polynomial ℕ := 11*(X+1)^3
noncomputable def sampleTime : Polynomial ℕ := SampleEmitter.time.comp inputSize
noncomputable def wordSize : Polynomial ℕ := inputSize+SampleEmitter.emitTime.comp inputSize

lemma spectral_bounds {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) :
    r.val≤((circuitBits n w).length+1)^2 ∧ s.val≤((circuitBits n w).length+1)^2 := by
  have hl:=(SampleEmitter.circuit_size_bounds w).2
  have hf:=constraintOccurrences_le_length w
  have hr:=(Nat.le_of_lt r.isLt).trans (spectralIndex_card_bound _)
  have hs:=(Nat.le_of_lt s.isLt).trans (spectralIndex_card_bound _)
  exact ⟨hr.trans (Nat.pow_le_pow_left (by omega) 2),hs.trans (Nat.pow_le_pow_left (by omega) 2)⟩

lemma degree_bound {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) :
    degree w r.val s.val≤8*((circuitBits n w).length+1)^3 := by
  have hspec:=spectral_bounds w r s
  have hl:=(SampleEmitter.circuit_size_bounds w).2
  have hf:=constraintOccurrences_le_length w
  have h1:=Nat.mul_le_mul hspec.1 (show forbidOccurrences w≤(circuitBits n w).length+1 by omega)
  have h2:=Nat.mul_le_mul hspec.2 (show signOccurrences w≤(circuitBits n w).length+1 by omega)
  rw [SourceQueryRecovery.degree,SampleDimensions.sampled_occurrences]
  simp only [pow_succ,pow_two,pow_one] at *
  nlinarith

lemma input_bound {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    SampleEmitter.inputSize w r.val s.val u.val≤ inputSize.eval (circuitBits n w).length := by
  have hspec:=spectral_bounds w r s
  have hd:=degree_bound w r s
  have hu : u.val≤ degree w r.val s.val := by have h:=u.isLt;change u.val<degree w r.val s.val+1 at h;omega
  have hp : ((circuitBits n w).length+1)^2≤((circuitBits n w).length+1)^3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hL : (circuitBits n w).length≤((circuitBits n w).length+1)^3 := by nlinarith
  simp only [SampleEmitter.inputSize,inputSize,eval_mul,eval_pow,eval_add,eval_X,eval_one,eval_ofNat]
  omega

theorem sample_executes (g : BitString → ℕ) {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    ∃c,SampleEmitter.program.Executes g
      (SampleEmitter.store (circuitBits n w) r.val s.val u.val 0 0 0 [] [] [] [] [] [])
      (SampleEmitter.outputStore (circuitBits n w) r.val s.val u.val 0
        (List.replicate (SampleScalar.sampleExponent w r.val s.val u.val) true) [SampleEmitter.sampleNegative w false]
        (wordBits (word hn w r s u))) c ∧ c≤ sampleTime.eval (circuitBits n w).length := by
  obtain ⟨c,hc,hb⟩:=SampleEmitter.program_executes g hn w r.val s.val u.val
  refine ⟨c,hc,hb.trans ?_⟩
  have h:=polynomial_nat_eval_mono SampleEmitter.time (input_bound w r s u)
  simpa only [sampleTime,eval_comp] using h

lemma emission_bounds {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    (wordBits (word hn w r s u)).length≤ wordSize.eval (circuitBits n w).length ∧
      SampleScalar.sampleExponent w r.val s.val u.val≤ wordSize.eval (circuitBits n w).length := by
  have h:=SampleEmitter.emitted_length_bound (fun _=>0) w r.val s.val u.val
  rw [SampleEmitter.rawBits_eq_wordBits hn] at h
  have hi:=input_bound w r s u
  have hm:=polynomial_nat_eval_mono SampleEmitter.emitTime hi
  dsimp only at hm
  simp only [wordSize,eval_add,eval_comp]
  exact ⟨h.1.trans (Nat.add_le_add hi hm),h.2.trans (Nat.add_le_add hi hm)⟩
end HiddenCircuits.Circuit.Runtime.SampleGridBounds
