import HiddenCircuits.GraphReduction.Runtime.MonotoneOrderCallback

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneOrderTranspose
open Complexity OracleBlock
set_option maxHeartbeats 800000

def embedding : Fin 57 ↪ Fin 57 where
  toFun i := if i=1 then 2 else if i=2 then 1 else i
  inj' := by decide +kernel
lemma embedding_involutive (i : Fin 57) : embedding (embedding i)=i := by
  fin_cases i <;> rfl
noncomputable def program (lower rightPart isLeft : Bool) : OracleBlock 56 := rename (MonotoneOrderRuntime.program lower rightPart isLeft) embedding

theorem framed (g : BitString→ℕ) (lower rightPart isLeft : Bool) (records : List VertexRecord) (i j : ℕ)
    (hi:i<records.length) (hj:j<records.length) (out inner outer : BitString) :
    ∃t,(program lower rightPart isLeft).Executes g
      (MatrixEmitter.store (k:=49) records.length i j [] out inner outer (callbackParams (encodeBitList (records.map encodeVertex))))
      (MatrixEmitter.store (k:=49) records.length i j [MonotoneOrderRuntime.recordLT lower rightPart isLeft records j i] out inner outer (callbackParams (encodeBitList (records.map encodeVertex)))) t ∧
      t≤MonotoneOrderRuntime.bound records.length (encodeBitList (records.map encodeVertex)).length := by
  obtain ⟨t,hc,hb⟩:=MonotoneOrderRuntime.framed g lower rightPart isLeft records j i hj hi out inner outer
  refine ⟨t,?_,hb⟩
  apply rename_executes_to (MonotoneOrderRuntime.program lower rightPart isLeft) embedding g hc
  · funext q;fin_cases q <;> rfl
  · funext q;fin_cases q <;> rfl
  · intro q hq;exact False.elim (hq (embedding q) (embedding_involutive q))
lemma program_queryFree (lower rightPart isLeft : Bool) : (program lower rightPart isLeft).QueryFree := rename_queryFree _ _ (MonotoneOrderRuntime.program_queryFree lower rightPart isLeft)
end HiddenCircuits.GraphReduction.Runtime.MonotoneOrderTranspose
