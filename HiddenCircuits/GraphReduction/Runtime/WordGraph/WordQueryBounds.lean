import HiddenCircuits.GraphReduction.Runtime.WordGraph.WordQuery

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.WordQuery
open Complexity OracleBlock BinaryArithmetic Polynomial
noncomputable def time : Polynomial ℕ := WordSample.time+10*X+PairedQuery.time.comp (3*(X+1)^2)+10

theorem program_polynomial (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c,program.Executes g (input w t s) (output w t s) c ∧ c≤time.eval ((wordBits w).length+t+s) := by
  obtain ⟨c,hc,hb⟩ := program_executes g w t s
  refine ⟨c,hc,hb.trans ?_⟩
  let N := (wordBits w).length+t+s
  have hin := wordBits_length_lower w
  have hp : w.particles≤N := by dsimp [N];omega
  have hn : w.word.length≤N := by dsimp [N];omega
  have ht : t≤N := by dsimp [N];omega
  have hs : s≤N := by dsimp [N];omega
  have hh : w.word.length*(t+1)≤N*(N+1) := Nat.mul_le_mul hn (by omega)
  have hq : w.particles+(sampleWord w.word t).length+s≤3*(N+1)^2 := by
    rw [sampleWord_length]
    nlinarith
  have ha := polynomial_nat_eval_mono WordSample.time (show (wordBits w).length+t≤N by dsimp[N];omega)
  have hb := polynomial_nat_eval_mono PairedQuery.time hq
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat,eval_comp,eval_pow,eval_one]
  dsimp only [N] at *
  omega
end HiddenCircuits.GraphReduction.Runtime.WordGraph.WordQuery
