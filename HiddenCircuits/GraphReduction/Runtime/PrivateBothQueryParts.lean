import HiddenCircuits.GraphReduction.Runtime.PrivateIntervalEmitter
import HiddenCircuits.GraphReduction.Runtime.PrivateIntervalPacket

namespace HiddenCircuits.GraphReduction.Runtime.PrivateBothQuery
open Complexity OracleBlock Polynomial
open PrivateSuppliedQuery (state embedding saveGraph saveUpper saveLower serialize
  saveGraph_executes saveUpper_executes saveLower_executes serialize_executes)
set_option maxHeartbeats 900000

noncomputable def rank (left : Bool) : OracleBlock 63 := rename (PrivateIntervalEmitter.program left) embedding

lemma rank_executes (g : BitString→ℕ) (lower : Bool) (records : List VertexRecord) (a b c : BitString) :
    ∃t,(rank lower).Executes g (state records.length (encodeBitList (records.map encodeVertex)) [] a b c)
      (state records.length (encodeBitList (records.map encodeVertex)) (PrivateIntervalEmitter.bits lower records) a b c) t ∧
      t≤PrivateIntervalEmitter.time.eval (records.length+(encodeBitList (records.map encodeVertex)).length) := by
  obtain ⟨t,ht,hb⟩:=PrivateIntervalEmitter.program_executes g lower records
  refine ⟨t,?_,hb⟩
  apply rename_executes_to (PrivateIntervalEmitter.program lower) embedding g ht
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · clear ht hb
    intro i hi
    have h7:i.val≠7:=by intro h;exact hi 7 (Fin.ext h.symm)
    simp only [state,h7,if_false]

end HiddenCircuits.GraphReduction.Runtime.PrivateBothQuery
