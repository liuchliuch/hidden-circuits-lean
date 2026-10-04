import HiddenCircuits.Complexity.EvalValidation.Field
import HiddenCircuits.Complexity.EvalValidation.Mask
import HiddenCircuits.Complexity.EvalValidation.Semantics
import HiddenCircuits.Complexity.OracleMove

namespace HiddenCircuits.Complexity.EvalValidation.Core
open OracleBlock GraphVerifier
set_option maxHeartbeats 1000000

def state (input data p width flags atom out : BitString) : Store 31 := fun i=>
  if i.val=0 then input else if i.val=1 then data else if i.val=2 then p else if i.val=3 then width
  else if i.val=4 then flags else if i.val=5 then atom else if i.val=6 then out else []
def fieldPorts : Fin 6 ↪ Fin 32 where
  toFun i:=![1,5,6,7,8,9] i
  inj' := by decide +kernel
def maskPorts : Fin 14 ↪ Fin 32 where
  toFun i:=![5,2,3,6,10,11,12,13,14,15,16,17,18,19] i
  inj' := by decide +kernel
def pairPorts : Fin 9 ↪ Fin 32 where
  toFun i:=![5,3,6,10,11,12,13,14,15] i
  inj' := by decide +kernel
noncomputable def field : OracleBlock 31 := rename Field.program fieldPorts
noncomputable def mask : OracleBlock 31 := rename Mask.program maskPorts
noncomputable def pairAtom : OracleBlock 31 := rename PairAtom.program pairPorts
noncomputable def collect : OracleBlock 31 := reverseOn 6 4 (by decide)

lemma field_executes (g : BitString→ℕ) (input data p width flags : BitString) :
    ∃c,field.Executes g (state input data p width flags [] [])
      (state input (Field.item data).right p width flags (Field.item data).left [Field.valid data]) c ∧ c≤3*data.length+19 := by
  obtain ⟨c,hc,hb⟩:=Field.program_executes g data
  refine ⟨c,?_,hb⟩
  apply rename_executes_to Field.program fieldPorts g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h1:i.val≠1:=by intro h;exact hi 0 (Fin.ext h.symm)
    have h5:i.val≠5:=by intro h;exact hi 1 (Fin.ext h.symm)
    have h6:i.val≠6:=by intro h;exact hi 2 (Fin.ext h.symm)
    simp only [state,h1,h5,h6,if_false]
lemma mask_executes (g : BitString→ℕ) (input data p width flags atom : BitString) :
    ∃c,mask.Executes g (state input data p width flags atom [])
      (state input data p width flags [] [Mask.valid atom p width]) c ∧ c≤1000*(atom.length+p.length+width.length+1)^2 := by
  obtain ⟨c,hc,hb⟩:=Mask.program_executes g atom p width
  refine ⟨c,?_,hb⟩
  apply rename_executes_to Mask.program maskPorts g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h5:i.val≠5:=by intro h;exact hi 0 (Fin.ext h.symm)
    have h6:i.val≠6:=by intro h;exact hi 3 (Fin.ext h.symm)
    simp only [state,h5,h6,if_false]
lemma pairAtom_executes (g : BitString→ℕ) (input data p width flags atom : BitString) :
    ∃c,pairAtom.Executes g (state input data p width flags atom [])
      (state input data p width flags [] [PairAtom.valid atom width]) c ∧ c≤200*(atom.length+width.length+1) := by
  obtain ⟨c,hc,hb⟩:=PairAtom.program_executes g atom width
  refine ⟨c,?_,hb⟩
  apply rename_executes_to PairAtom.program pairPorts g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h5:i.val≠5:=by intro h;exact hi 0 (Fin.ext h.symm)
    have h6:i.val≠6:=by intro h;exact hi 2 (Fin.ext h.symm)
    simp only [state,h5,h6,if_false]
lemma collect_executes (g : BitString→ℕ) (input data p width flags atom : BitString) (b : Bool) :
    collect.Executes g (state input data p width flags atom [b]) (state input data p width (b::flags) atom []) 3 := by
  convert reverseOn_executes g (6:Fin 32) 4 (by decide) (state input data p width flags atom [b]) using 1
  funext i;fin_cases i <;> rfl
noncomputable def takeMask : OracleBlock 31 := seq field (seq collect (seq mask collect))
def maskFlags (data p width flags : BitString) : BitString :=
  Mask.valid (Field.item data).left p width::Field.valid data::flags
lemma takeMask_executes (g : BitString→ℕ) (input data p width flags : BitString) :
    ∃c,takeMask.Executes g (state input data p width flags [] [])
      (state input (Field.item data).right p width (maskFlags data p width flags) [] []) c ∧
      c≤1100*(data.length+p.length+width.length+1)^2 := by
  obtain ⟨a,ha,hab⟩:=field_executes g input data p width flags
  have hb:=collect_executes g input (Field.item data).right p width flags (Field.item data).left (Field.valid data)
  obtain ⟨c,hc,hcb⟩:=mask_executes g input (Field.item data).right p width (Field.valid data::flags) (Field.item data).left
  have hd:=collect_executes g input (Field.item data).right p width (Field.valid data::flags) [] (Mask.valid (Field.item data).left p width)
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd)),?_⟩
  have hlen:=(Field.lengths data).1
  have hpow:((Field.item data).left.length+p.length+width.length+1)^2≤(data.length+p.length+width.length+1)^2:=Nat.pow_le_pow_left (by omega) 2
  have hn:1≤data.length+p.length+width.length+1:=by omega
  nlinarith
abbrev wordPorts : Fin 9 ↪ Fin 32 := pairPorts
noncomputable def wordAtom : OracleBlock 31 := rename WordAtom.program wordPorts
noncomputable def atom (pairMode : Bool) : OracleBlock 31 := if pairMode then pairAtom else wordAtom
lemma wordAtom_executes (g : BitString→ℕ) (input data p width flags word : BitString) :
    ∃c,wordAtom.Executes g (state input data p width flags word [])
      (state input data p width flags [] [WordAtom.valid word width]) c ∧ c≤500*(word.length+width.length+1) := by
  obtain ⟨c,hc,hb⟩:=WordAtom.program_executes g word width
  refine ⟨c,?_,hb⟩
  apply rename_executes_to WordAtom.program wordPorts g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h5:i.val≠5:=by intro h;exact hi 0 (Fin.ext h.symm)
    have h6:i.val≠6:=by intro h;exact hi 2 (Fin.ext h.symm)
    simp only [state,h5,h6,if_false]
lemma atom_executes (g : BitString→ℕ) (pairMode : Bool) (input data p width flags word : BitString) :
    ∃c,(atom pairMode).Executes g (state input data p width flags word [])
      (state input data p width flags [] [Semantics.atomValid pairMode width word]) c ∧ c≤500*(word.length+p.length+width.length+1) := by
  cases pairMode
  · obtain ⟨c,hc,hb⟩:=wordAtom_executes g input data p width flags word
    exact ⟨c,hc,by omega⟩
  · obtain ⟨c,hc,hb⟩:=pairAtom_executes g input data p width flags word
    exact ⟨c,hc,by omega⟩
noncomputable def takeAtom (pairMode : Bool) : OracleBlock 31 := seq field (seq collect (seq (atom pairMode) collect))
lemma takeAtom_executes (g : BitString→ℕ) (pairMode : Bool) (input data p width flags : BitString) :
    ∃c,(takeAtom pairMode).Executes g (state input data p width flags [] [])
      (state input (Field.item data).right p width
        (Semantics.atomValid pairMode width (Field.item data).left::Field.valid data::flags) [] []) c ∧
      c≤600*(data.length+p.length+width.length+1) := by
  obtain ⟨a,ha,hab⟩:=field_executes g input data p width flags
  have hb:=collect_executes g input (Field.item data).right p width flags (Field.item data).left (Field.valid data)
  obtain ⟨c,hc,hcb⟩:=atom_executes g pairMode input (Field.item data).right p width (Field.valid data::flags) (Field.item data).left
  have hd:=collect_executes g input (Field.item data).right p width (Field.valid data::flags) [] (Semantics.atomValid pairMode width (Field.item data).left)
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd)),?_⟩
  have hlen:=(Field.lengths data).1
  omega
end HiddenCircuits.Complexity.EvalValidation.Core
