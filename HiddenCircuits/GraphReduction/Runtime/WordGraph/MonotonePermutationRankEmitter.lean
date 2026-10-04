import HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotonePermutationOrderTranspose
import HiddenCircuits.GraphReduction.Runtime.RankEmitterEncoding

namespace HiddenCircuits.GraphReduction.Runtime.MonotonePermutationRankEmitter
open Complexity OracleBlock Polynomial
set_option maxHeartbeats 800000

def edge (lower : Bool) (records : List VertexRecord) (i j : ℕ) := MonotonePermutationOrderRuntime.recordLT lower records j i
def bits (lower : Bool) (records : List VertexRecord) : BitString := RankEmitter.bits records.length (edge lower records)
noncomputable def program (lower : Bool) : OracleBlock 56 := RankEmitter.block (MonotonePermutationOrderTranspose.program lower)
noncomputable def time : Polynomial ℕ := 20000*(X+1)^4

lemma cost_bound (n L : ℕ) : n*n*(MonotonePermutationOrderRuntime.bound n L+30)+40*n+20≤time.eval (n+L) := by
  let M:=n+L
  have hn:n≤M:=by dsimp[M];omega
  have hL:L≤M:=by dsimp[M];omega
  calc
    _≤M*M*(MonotonePermutationOrderRuntime.bound M M+30)+40*M+20 := by unfold MonotonePermutationOrderRuntime.bound lookupBound;gcongr
    _≤_ := by
      change _≤time.eval M
      simp only [time,eval_mul,eval_pow,eval_add,eval_X,eval_ofNat,eval_one]
      unfold MonotonePermutationOrderRuntime.bound lookupBound
      ring_nf
      omega

theorem program_executes (g : BitString→ℕ) (lower : Bool) (records : List VertexRecord) :
    ∃c,(program lower).Executes g
      (MatrixEmitter.store (k:=49) records.length 0 0 [] [] [] [] (callbackParams (encodeBitList (records.map encodeVertex))))
      (Function.update (MatrixEmitter.store (k:=49) records.length 0 0 [] [] [] [] (callbackParams (encodeBitList (records.map encodeVertex))))
        (MatrixEmitter.port 7) (bits lower records)) c ∧
      c≤time.eval (records.length+(encodeBitList (records.map encodeVertex)).length) := by
  obtain ⟨c,hc,hb⟩:=RankEmitter.block_executes (MonotonePermutationOrderTranspose.program lower) (edge lower records) records.length
    (MonotonePermutationOrderRuntime.bound records.length (encodeBitList (records.map encodeVertex)).length)
    (callbackParams (encodeBitList (records.map encodeVertex)))
    (by intro g i j out inner outer hi hj;exact MonotonePermutationOrderTranspose.framed g lower records i j hi hj out inner outer) g
  exact ⟨c,hc,hb.trans (cost_bound _ _)⟩
lemma program_queryFree (lower : Bool) : (program lower).QueryFree := RankEmitter.block_queryFree _ (MonotonePermutationOrderTranspose.program_queryFree lower)
end HiddenCircuits.GraphReduction.Runtime.MonotonePermutationRankEmitter
