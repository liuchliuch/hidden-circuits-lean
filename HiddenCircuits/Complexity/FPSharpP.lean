import HiddenCircuits.Complexity.FPSharpPVerifier
import HiddenCircuits.Complexity.OracleElimination.Blocks

/-! Natural-valued deterministic FP is included in machine-defined #P, with
exactly one fixed-length binary witness for each integer below the output. -/
namespace HiddenCircuits.Complexity

lemma FPSharpP.polyVerifier {f : BitString→ℕ} (hf : FP f) : PolyVerifier (FPSharpP.verifier f) := by
  obtain ⟨p,hp⟩:=hf.binary_output_bound
  apply OracleBlock.polyVerifier_of_oracleBlock (FPSharpP.verifier f) FPSharpP.program (FPSharpP.time p) hf
  intro xs
  obtain ⟨c,hc,hb⟩:=FPSharpP.program_executes f p hp xs
  exact ⟨_,c,hc,Function.update_self _ _ _,hb⟩

theorem FP.sharpP {f : BitString→ℕ} (hf : FP f) : SharpP f := by
  obtain ⟨p,hp⟩:=FPSharpP.fp_value_bound hf
  refine ⟨p,FPSharpP.verifier f,FPSharpP.polyVerifier hf,?_⟩
  intro xs
  exact (FPSharpP.certificate_count f xs (p.eval xs.length) (hp xs)).symm
end HiddenCircuits.Complexity
