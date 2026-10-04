import HiddenCircuits.Complexity.CountingCook
import HiddenCircuits.Complexity.OraclePrecompose

/-! Reuse the actual Cook emitter before an actual canonical-CNF solver. Because
the emitter proves canonical bytes, the hardness chain need not parse malformed
CNF strings; no runtime is inferred merely from formula or query sizes. -/
namespace HiddenCircuits.Complexity
open OracleBlock

/-- Operational interface theorem: supplying a real finite canonical-CNF solver
is sufficient to close hardness. Its premise is not itself asserted here; the
source-reduction assembly must instantiate it with the concrete oracle program. -/
theorem sharpPHard_of_canonical_sat_block {k : ℕ} (g : BitString → ℕ) (B : OracleBlock k)
    (q : Polynomial ℕ)
    (hB : ∀ F : CNFInput, ∃ s : Store k, ∃ c,
      B.Executes g (Function.update (fun _ => []) 0 (CNFInput.encode F)) s c ∧
      s 0=Computability.encodeNat F.2.2.satCount ∧ c≤q.eval (CNFInput.encode F).length) :
    SharpPHard g := by
  intro f hf
  obtain ⟨p,v,⟨M⟩,hv⟩ := hf
  let C : OracleBlock (k+17) := resize (VerifierCompiler.program M p) (by omega)
  let D : OracleBlock (k+17) := resize B (by omega)
  let emit := VerifierCompiler.emit M p
  let size := VerifierTableau.formulaSizePolynomial M p
  let P := VerifierCompiler.time M p
  have hC : ∀ x, ∃ s : Store (k+17), ∃ c,
      C.Executes g (Function.update (fun _ => []) 0 x) s c ∧ s 0=emit x ∧ c≤P.eval x.length := by
    intro x
    obtain ⟨s,c,hc,ho,hbound⟩ := VerifierCompiler.program_executes M p g x
    obtain ⟨t,ht,hto⟩ := resize_executes (VerifierCompiler.program M p) (show 17≤k+17 by omega) g x s c hc
    exact ⟨t,c,ht,hto.trans ho,hbound⟩
  have hD : ∀ x, ∃ s : Store (k+17), ∃ c,
      D.Executes g (Function.update (fun _ => []) 0 (emit x)) s c ∧
      s 0=Computability.encodeNat (f x) ∧ c≤q.eval (emit x).length := by
    intro x
    let F := VerifierTableau.uniformFormula M x (p.eval x.length)
    obtain ⟨s,c,hc,ho,hbound⟩ := hB F
    obtain ⟨t,ht,hto⟩ := resize_executes B (show k≤k+17 by omega) g (CNFInput.encode F) s c hc
    refine ⟨t,c,ht,?_,hbound⟩
    rw [hto,ho]
    congr 1
    exact (VerifierTableau.uniformFormula_count M x (p.eval x.length)).trans (hv x).symm
  let A := precompose C D
  refine ⟨A.machine,precomposeTime (k := k+17) P q size,fun x => ?_⟩
  obtain ⟨s,c,hc,ho,hbound⟩ := precompose_executes C D g emit (fun x => Computability.encodeNat (f x))
    P q size hC (VerifierCompiler.emit_length M p) hD x
  refine ⟨A.config A.exit s,c,?_,ho,hbound⟩
  apply (OracleMachine.runs_iff_steps_halt A.machine).mpr
  exact ⟨hc,by simp [OracleMachine.step,machine,config,A.exit_halt]⟩

end HiddenCircuits.Complexity
