import HiddenCircuits.GraphReduction.Runtime.PrivateIntervalCallback
import HiddenCircuits.GraphReduction.Runtime.RankEmitterEncoding

namespace HiddenCircuits.GraphReduction.Runtime.PrivateIntervalEmitter
open Complexity OracleBlock Polynomial
set_option maxHeartbeats 800000

def edge (lower : Bool) (records : List VertexRecord) (i j : ℕ) := PrivateInterval.endpointEdge lower records i j
def bits (lower : Bool) (records : List VertexRecord) : BitString := RankEmitter.bits records.length (edge lower records)
noncomputable def program (lower : Bool) : OracleBlock 56 := RankEmitter.block (PrivateIntervalCallback.program lower)
noncomputable def time : Polynomial ℕ := 40000*(X+1)^4

lemma cost_bound (n L : ℕ) : n*n*(PrivateIntervalCallback.bound n L+30)+40*n+20≤time.eval (n+L) := by
  let M:=n+L
  have hn:n≤M:=by dsimp[M];omega
  have hL:L≤M:=by dsimp[M];omega
  calc
    _≤M*M*(PrivateIntervalCallback.bound M M+30)+40*M+20 := by unfold PrivateIntervalCallback.bound PrivateIntervalOrderRuntime.bound CliqueCallback.bound lookupBound;gcongr
    _≤_ := by
      change _≤time.eval M
      simp only [time,eval_mul,eval_pow,eval_add,eval_X,eval_ofNat,eval_one]
      unfold PrivateIntervalCallback.bound PrivateIntervalOrderRuntime.bound CliqueCallback.bound lookupBound
      ring_nf
      omega

theorem program_executes (g : BitString→ℕ) (lower : Bool) (records : List VertexRecord) :
    ∃c,(program lower).Executes g
      (MatrixEmitter.store (k:=49) records.length 0 0 [] [] [] [] (callbackParams (encodeBitList (records.map encodeVertex))))
      (Function.update (MatrixEmitter.store (k:=49) records.length 0 0 [] [] [] [] (callbackParams (encodeBitList (records.map encodeVertex))))
        (MatrixEmitter.port 7) (bits lower records)) c ∧
      c≤time.eval (records.length+(encodeBitList (records.map encodeVertex)).length) := by
  obtain ⟨c,hc,hb⟩:=RankEmitter.block_executes (PrivateIntervalCallback.program lower) (edge lower records) records.length
    (PrivateIntervalCallback.bound records.length (encodeBitList (records.map encodeVertex)).length)
    (callbackParams (encodeBitList (records.map encodeVertex)))
    (by intro g i j out inner outer hi hj;exact PrivateIntervalCallback.framed g lower records i j hi hj out inner outer) g
  exact ⟨c,hc,hb.trans (cost_bound _ _)⟩
lemma program_queryFree (lower : Bool) : (program lower).QueryFree := RankEmitter.block_queryFree _ (PrivateIntervalCallback.program_queryFree lower)
end HiddenCircuits.GraphReduction.Runtime.PrivateIntervalEmitter
