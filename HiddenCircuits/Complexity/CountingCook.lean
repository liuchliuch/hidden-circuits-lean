import HiddenCircuits.Complexity.VerifierCompiler

/-! The machine-grounded counting Cook theorem. An arbitrary #P function is
reduced by a real fixed finite program to the total binary #SAT problem. The
compiler is parsimonious, and the sole oracle instruction is charged for the
entire query and binary answer. No source-hardness premise is used. -/
namespace HiddenCircuits.Complexity
open OracleBlock

namespace CountingCook
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v) (p : Polynomial ℕ)

noncomputable def program : OracleBlock 17 :=
  seq (VerifierCompiler.program M p) (query 0 0)

/-- Exact finite execution, including the fully charged oracle call. -/
theorem program_executes (x : BitString) :
    ∃ s : Store 17, ∃ cost, (program M p).Executes CNFInput.satProblem
      (Function.update (fun _ => []) 0 x) s cost ∧
      s 0 = Computability.encodeNat (certificateCount v x (p.eval x.length)) ∧
      cost ≤ (VerifierCompiler.time M p + VerifierTableau.formulaSizePolynomial M p + p + 4).eval x.length := by
  obtain ⟨s,c,hc,ho,hb⟩ := VerifierCompiler.program_executes M p CNFInput.satProblem x
  have hq := query_executes CNFInput.satProblem (0 : Fin 18) 0 s
  have he := seq_executes _ _ CNFInput.satProblem hc hq
  have ha : OracleMachine.answerBits CNFInput.satProblem (s 0) =
      Computability.encodeNat (certificateCount v x (p.eval x.length)) := by
    rw [OracleMachine.answerBits,ho,VerifierCompiler.emit_count]
  have hl := VerifierCompiler.emit_length M p x
  have hab : (Computability.encodeNat (certificateCount v x (p.eval x.length))).length ≤
      p.eval x.length+1 := by
    rw [encodeNat_length]
    have h := Nat.size_le_size (certificateCount_le v x (p.eval x.length))
    rwa [Nat.size_pow] at h
  refine ⟨_,_,he,?_,?_⟩
  · simpa only [Function.update_self] using ha
  · rw [ha,ho]
    simp only [Polynomial.eval_add,Polynomial.eval_ofNat]
    omega

end CountingCook

/-- Every machine-defined #P counting function has a proved polynomial-time
Turing reduction to binary #SAT. -/
theorem SharpP.reduces_to_sat {f : BitString → ℕ} (hf : SharpP f) :
    PolyTuringReduction f CNFInput.satProblem := by
  obtain ⟨p,v,⟨M⟩,hv⟩ := hf
  let B := CountingCook.program M p
  refine ⟨B.machine,VerifierCompiler.time M p + VerifierTableau.formulaSizePolynomial M p + p + 4,fun x => ?_⟩
  obtain ⟨s,c,hc,ho,hb⟩ := CountingCook.program_executes M p x
  refine ⟨B.config B.exit s,c,?_,?_,hb⟩
  · apply (OracleMachine.runs_iff_steps_halt B.machine).mpr
    exact ⟨hc,by simp [OracleMachine.step,machine,config,B.exit_halt]⟩
  · change s 0 = Computability.encodeNat (f x)
    rw [hv x]
    exact ho

/-- Counting Cook hardness is a theorem, not an assumption about #SAT. -/
theorem sat_sharpPHard : SharpPHard CNFInput.satProblem :=
  fun _ hf => hf.reduces_to_sat

/-- Stronger parsimonious form: an ordinary polynomial-time binary emitter
already preserves the exact counting value, without oracle computations. -/
theorem SharpP.parsimonious_sat {f : BitString → ℕ} (hf : SharpP f) :
    ∃ emit : BitString → BitString, PolyTime emit ∧ ∀ x, CNFInput.satProblem (emit x) = f x := by
  obtain ⟨p,v,⟨M⟩,hv⟩ := hf
  exact ⟨VerifierCompiler.emit M p,VerifierCompiler.emit_polyTime M p,
    fun x => (VerifierCompiler.emit_count M p x).trans (hv x).symm⟩

end HiddenCircuits.Complexity
