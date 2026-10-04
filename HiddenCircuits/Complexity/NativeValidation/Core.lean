import HiddenCircuits.Complexity.NativeValidation.Semantics
import HiddenCircuits.Complexity.EvalValidation.Core

namespace HiddenCircuits.Complexity.NativeValidation.Core
open OracleBlock GraphVerifier EvalValidation.Core
set_option maxHeartbeats 1000000
noncomputable def atom (deltaMode : Bool) : OracleBlock 31 := rename (Gate.program deltaMode) pairPorts
lemma atom_executes (g : BitString→ℕ) (deltaMode : Bool) (input data p width flags word : BitString) :
    ∃c,(atom deltaMode).Executes g (state input data p width flags word [])
      (state input data p width flags [] [Gate.valid deltaMode word width]) c ∧ c≤250*(word.length+width.length+1) := by
  obtain ⟨c,hc,hb⟩:=Gate.program_executes g deltaMode word width
  refine ⟨c,?_,hb⟩
  apply rename_executes_to (Gate.program deltaMode) pairPorts g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h5:i.val≠5:=by intro h;exact hi 0 (Fin.ext h.symm)
    have h6:i.val≠6:=by intro h;exact hi 2 (Fin.ext h.symm)
    simp only [state,h5,h6,if_false]
noncomputable def takeAtom (deltaMode : Bool) : OracleBlock 31 := seq field (seq collect (seq (atom deltaMode) collect))
lemma takeAtom_executes (g : BitString→ℕ) (deltaMode : Bool) (input data p width flags : BitString) :
    ∃c,(takeAtom deltaMode).Executes g (state input data p width flags [] [])
      (state input (EvalValidation.Field.item data).right p width
        (Gate.valid deltaMode (EvalValidation.Field.item data).left width::EvalValidation.Field.valid data::flags) [] []) c ∧
      c≤600*(data.length+p.length+width.length+1) := by
  obtain ⟨a,ha,hab⟩:=field_executes g input data p width flags
  have hb:=collect_executes g input (EvalValidation.Field.item data).right p width flags (EvalValidation.Field.item data).left (EvalValidation.Field.valid data)
  obtain ⟨c,hc,hcb⟩:=atom_executes g deltaMode input (EvalValidation.Field.item data).right p width (EvalValidation.Field.valid data::flags) (EvalValidation.Field.item data).left
  have hd:=collect_executes g input (EvalValidation.Field.item data).right p width (EvalValidation.Field.valid data::flags) [] (Gate.valid deltaMode (EvalValidation.Field.item data).left width)
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd)),?_⟩
  have hlen:=(EvalValidation.Field.lengths data).1
  omega
end HiddenCircuits.Complexity.NativeValidation.Core
