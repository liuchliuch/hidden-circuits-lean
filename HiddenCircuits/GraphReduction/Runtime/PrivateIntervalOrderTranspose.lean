import HiddenCircuits.GraphReduction.Runtime.PrivateIntervalOrderCallback

namespace HiddenCircuits.GraphReduction.Runtime.PrivateIntervalOrderTranspose
open Complexity OracleBlock
set_option maxHeartbeats 800000

def embedding : Fin 57 ↪ Fin 57 where
  toFun i := if i=1 then 2 else if i=2 then 1 else i
  inj' := by decide +kernel
lemma embedding_involutive (i : Fin 57) : embedding (embedding i)=i := by
  fin_cases i <;> rfl
noncomputable def program (lower : Bool) : OracleBlock 56 := rename (PrivateIntervalOrderRuntime.program lower) embedding

theorem framed (g : BitString→ℕ) (lower : Bool) (records : List VertexRecord) (i j : ℕ)
    (hi:i<records.length) (hj:j<records.length) (out inner outer : BitString) :
    ∃t,(program lower).Executes g
      (MatrixEmitter.store (k:=49) records.length i j [] out inner outer (callbackParams (encodeBitList (records.map encodeVertex))))
      (MatrixEmitter.store (k:=49) records.length i j [PrivateIntervalOrderRuntime.recordLT lower records j i] out inner outer (callbackParams (encodeBitList (records.map encodeVertex)))) t ∧
      t≤PrivateIntervalOrderRuntime.bound records.length (encodeBitList (records.map encodeVertex)).length := by
  obtain ⟨t,hc,hb⟩:=PrivateIntervalOrderRuntime.framed g lower records j i hj hi out inner outer
  refine ⟨t,?_,hb⟩
  apply rename_executes_to (PrivateIntervalOrderRuntime.program lower) embedding g hc
  · funext q;fin_cases q <;> rfl
  · funext q;fin_cases q <;> rfl
  · intro q hq;exact False.elim (hq (embedding q) (embedding_involutive q))
lemma program_queryFree (lower : Bool) : (program lower).QueryFree := rename_queryFree _ _ (PrivateIntervalOrderRuntime.program_queryFree lower)
end HiddenCircuits.GraphReduction.Runtime.PrivateIntervalOrderTranspose
