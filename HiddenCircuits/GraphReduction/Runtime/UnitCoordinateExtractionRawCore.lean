import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionProgram
import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionSerialize
import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionResult

/-! Physical composition from the internally computed raw graph order to
native bounded-grid bytes; the original graph and labels stay in the frame. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionRaw
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic Polynomial
open UnitCoordinateExtractionResult

abbrev input:=UnitOrderProgram.input
def ready (raw : BitString) : Store 47:=Function.update (UnitOrderProgram.output raw) 1 []
def embedding : Fin 23 ↪ Fin 48 where
  toFun i:=⟨if i.val=0 then 2 else if i.val=1 then 3 else if i.val=2 then 47 else i.val+2,by split_ifs <;> omega⟩
  inj':=by
    intro i j h;apply Fin.ext;have hv:=congrArg Fin.val h
    dsimp only at hv
    split_ifs at hv <;> omega
noncomputable def numeric : OracleBlock 47:=rename UnitCoordinateExtractionMachine.program embedding
noncomputable def serialize : OracleBlock 47:=rename UnitCoordinateExtractionSerialize.program embedding
noncomputable def compute : OracleBlock 47:=seq numeric serialize
noncomputable def magnitude : Polynomial ℕ:=2*(X+1)^2
noncomputable def serializationTime : Polynomial ℕ:=X*(4*magnitude^2+36*magnitude+60)+4*(X+1)^2+26*(X+1)+60
noncomputable def computeTime : Polynomial ℕ:=UnitCoordinateExtractionMachine.time+serializationTime+2

lemma ready_restrict (raw : BitString) (G : GraphInput) (hd:GraphInput.decode raw=some G) :
    ready raw∘embedding=UnitCoordinateExtractionMachine.input G.1 G.2.bits
      (UnitCoordinateExtractionMachine.labelBits (order G)) := by
  funext i;fin_cases i <;> simp [ready,UnitOrderProgram.output,hd,UnitOrderProgram.completed,embedding,
    UnitCoordinateExtractionMachine.input,UnitCoordinateExtractionMachine.state,
    UnitCoordinateExtractionMachine.inputFrame,order,UnitCoordinateExtractionMachine.labelBits,
    UnitOrderRounds.labelBits,Function.comp_def] <;> rfl

lemma compute_executes (g : BitString→ℕ) (raw : BitString) (G : GraphInput)
    (hd:GraphInput.decode raw=some G) (hu:RealUnitInterval.UnitIntervalGraph G.2.graph) :
    ∃s c,compute.Executes g (ready raw) s c ∧s 15=bytes G ∧c≤computeTime.eval G.1 := by
  obtain ⟨hn,hcover,horder⟩:=UnitOrderSemantics.order_ofGraph_correct G.2 hu
  obtain ⟨a,ha,hab⟩:=UnitCoordinateExtractionMachine.program_executes g G.2 (order G) hn hcover horder
  let f:=UnitCoordinateExtractionMachine.readyFrame G.1 G.2.bits (UnitCoordinateExtractionMachine.labelBits (order G))
  let x:=coordinates G
  let inner:=UnitCoordinateExtractionMachine.state f (UnitCoordinateExtractionMachine.encoded x) 0 0 [] [] []
  let middle:=install embedding (ready raw) inner
  have hnum:numeric.Executes g (ready raw) middle a:=
    rename_executes _ embedding g (ready raw) (by rw [ready_restrict raw G hd];exact ha)
  have hx:∀i,x i≤2*(G.1+1)^2:=by
    intro i
    have h:coordinates G i+max 1 G.1<2*G.1*max 1 G.1:=(coordinates_correct G hu).1 i
    have hm:2*G.1*max 1 G.1 ≤2*(G.1+1)^2:=by
      calc 2*G.1*max 1 G.1 ≤2*(G.1+1)*(G.1+1):=by gcongr <;> omega
           _ = _:=by ring
    dsimp only [x];omega
  obtain ⟨b,hb,hbb⟩:=UnitCoordinateExtractionSerialize.program_executes g f x (2*(G.1+1)^2) hx rfl
  have hmid:middle∘embedding=inner:=by funext i;exact install_image _ _ _ i
  have hser:=rename_executes UnitCoordinateExtractionSerialize.program embedding g middle (by rw [hmid];exact hb)
  refine ⟨_,a+b+2,seq_executes _ _ g hnum hser,?_,?_⟩
  · change install embedding middle _ (embedding 13)=_
    rw [install_image]
    change UnitCoordinateExtractionSerialize.bits (max 1 G.1) x=bytes G
    rfl
  · have hs:UnitCoordinateExtractionSerialize.bound G.1 (max 1 G.1) (2*(G.1+1)^2)≤serializationTime.eval G.1:=by
      calc
        _ = G.1*(4*(2*(G.1+1)^2)^2+36*(2*(G.1+1)^2)+60)+4*(max 1 G.1)^2+26*(max 1 G.1)+60 := by
          unfold UnitCoordinateExtractionSerialize.bound UnitCoordinateExtractionSerialize.cellBound
          ring
        _ ≤ _ := by
          simp only [serializationTime,magnitude,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
          gcongr <;> omega
    change b≤UnitCoordinateExtractionSerialize.bound G.1 (max 1 G.1) (2*(G.1+1)^2) at hbb
    simp only [computeTime,eval_add,eval_ofNat]
    omega
lemma compute_queryFree : compute.QueryFree:=seq_queryFree _ _
  (rename_queryFree _ _ UnitCoordinateExtractionMachine.program_queryFree)
  (rename_queryFree _ _ UnitCoordinateExtractionSerialize.program_queryFree)
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionRaw
