import HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSample
import HiddenCircuits.Complexity.PolynomialBounds

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSample
open Complexity OracleBlock BinaryArithmetic Polynomial
noncomputable def time : Polynomial ℕ := 10000*(X+1)^3

lemma letter_stream_bound (w : WordInstance) : (encodeBitList (w.word.map letterBits)).length≤(wordBits w).length := by
  simp only [wordBits,pairBits_length,encodeBitList,List.length_cons,List.length_replicate]
  omega

theorem program_polynomial (g : BitString → ℕ) (w : WordInstance) (t : ℕ) :
    ∃c,program.Executes g (WordParser.store (wordBits w) [] [] [] [] [] (List.replicate t true)) (output w t) c ∧
      c≤time.eval ((wordBits w).length+t) := by
  obtain ⟨c,hc,hb⟩ := program_executes g w t
  refine ⟨c,hc,hb.trans ?_⟩
  let L := (wordBits w).length
  let M := L+t+1
  have hL : L≤M := by dsimp [M];omega
  have ht : t+1≤M := by dsimp [M];omega
  have hM : 1≤M := by dsimp [M];omega
  have hl := wordBits_length_lower w
  have hp : w.particles≤M := by dsimp [M,L];omega
  have hn : w.word.length≤M := by dsimp [M,L];omega
  have hs : (encodeBitList (w.word.map letterBits)).length≤M := (letter_stream_bound w).trans hL
  have hpair := pairStream_length_bound (sampleWord w.word t)
  rw [sampleWord_length] at hpair
  have hpairs : (pairStream (sampleWord w.word t)).length≤14*M^3 := by
    calc
      _≤(w.word.length*(t+1))*(10+4*w.particles) := hpair
      _≤(M*M)*(14*M) := Nat.mul_le_mul (Nat.mul_le_mul hn ht) (by omega)
      _=14*M^3 := by ring
  have hbody : w.word.length*(34*w.particles+41*t+122)≤197*M^2 := by
    calc
      _≤M*(197*M) := Nat.mul_le_mul hn (by omega)
      _=197*M^2 := by ring
  have hpow1 : M≤M^3 := by nlinarith [Nat.mul_le_mul_left M hM,Nat.mul_le_mul_left (M*M) hM]
  have hpow2 : M^2≤M^3 := by nlinarith [Nat.mul_le_mul_left (M*M) hM]
  simp only [time,eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change _≤10000*M^3
  change (wordBits w).length≤M at hL
  nlinarith
end HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSample
