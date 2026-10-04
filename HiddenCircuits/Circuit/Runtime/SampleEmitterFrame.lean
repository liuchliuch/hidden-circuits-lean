import HiddenCircuits.Circuit.Runtime.SampleLocalCorrectness
import HiddenCircuits.Circuit.Runtime.SampleGateDispatch
import HiddenCircuits.Circuit.Runtime.ProjectionStream

/-! Explicit finite register wiring for the physical-word sample compiler. -/
namespace HiddenCircuits.Circuit.Runtime.SampleEmitter
open HiddenCircuits.Complexity OracleBlock

def store (circuit : BitString) (r s u n base clock : ℕ)
    (gates atom tag out exponent sign : BitString) : Store 31 := fun i =>
  if i.val=0 then circuit else if i.val=1 then List.replicate r true else if i.val=2 then List.replicate s true
  else if i.val=3 then List.replicate u true else if i.val=4 then List.replicate n true
  else if i.val=5 then out else if i.val=6 then exponent else if i.val=7 then sign
  else if i.val=8 then gates else if i.val=9 then atom else if i.val=10 then tag
  else if i.val=12 then List.replicate base true else if i.val=13 then List.replicate clock true else []

def localEmbedding : Fin 9 ↪ Fin 32 where
  toFun i := (![12,3,5,6,7,14,15,16,17] : Fin 9 → Fin 32) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def projectionEmbedding : Fin 11 ↪ Fin 32 where
  toFun i := (![4,5,6,14,15,16,17,18,19,20,21] : Fin 11 → Fin 32) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def localOne (a : OneGate) : OracleBlock 31 := rename (SampleLocalEmitter.one a) localEmbedding
noncomputable def localSample : OracleBlock 31 := rename SampleLocalEmitter.sample localEmbedding
noncomputable def projection : OracleBlock 31 := rename ProjectionStream.program projectionEmbedding
noncomputable def oneDelta (a : OneGate) : OracleBlock 31 := seq (localOne a) projection
noncomputable def sampleDelta : OracleBlock 31 := seq localSample projection

theorem localOne_executes (g : BitString → ℕ) (a : OneGate) (circuit : BitString) (r s u n base clock : ℕ)
    (gates atom tag out exponent : BitString) (negative : Bool) :
    (localOne a).Executes g (store circuit r s u n base clock gates atom tag out exponent [negative])
      (store circuit r s u n base clock gates atom tag
        ((LetterEmitter.wordBitsAt base (oneGateWord a).word).reverse++out)
        (List.replicate (SampleScalar.oneExponent a) true++exponent) [SampleLocalEmitter.oneNegative a negative])
      (LetterEmitter.wordCost base (oneGateWord a).word+SampleLocalEmitter.oneMetadataCost a+2) := by
  apply rename_executes_to _ localEmbedding g (SampleLocalEmitter.one_executes g a base u out exponent negative)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim | exact (hi 4 rfl).elim

theorem localSample_executes (g : BitString → ℕ) (circuit : BitString) (r s u n base clock : ℕ)
    (gates atom tag out exponent sign : BitString) :
    localSample.Executes g (store circuit r s u n base clock gates atom tag out exponent sign)
      (store circuit r s u n base clock gates atom tag ((SampleLocalEmitter.sampleBits base u).reverse++out)
        (List.replicate (290*u+372) true++exponent) sign)
      (SampleLocalEmitter.sampleCost base u+878*u+1126) := by
  apply rename_executes_to _ localEmbedding g (SampleLocalEmitter.sample_executes g base u out exponent sign)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim

theorem projection_executes (g : BitString → ℕ) (circuit : BitString) (r s u n base clock : ℕ)
    (gates atom tag out exponent sign : BitString) :
    ∃cost, projection.Executes g (store circuit r s u n base clock gates atom tag out exponent sign)
      (store circuit r s u n base clock gates atom tag
        ((encodeBitList ((globalProjectionWord n).map letterBits)).reverse++out)
        (List.replicate (SampleScalar.projectionExponent n) true++exponent) sign) cost ∧
      cost≤ProjectionStream.time.eval n := by
  obtain ⟨cost,h,hb⟩ := ProjectionStream.program_executes g n out exponent
  refine ⟨cost,?_,hb⟩
  apply rename_executes_to _ projectionEmbedding g h
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim

lemma localOne_queryFree (a : OneGate) : (localOne a).QueryFree := rename_queryFree _ _ (SampleLocalEmitter.one_queryFree a)
lemma localSample_queryFree : localSample.QueryFree := rename_queryFree _ _ SampleLocalEmitter.sample_queryFree
lemma projection_queryFree : projection.QueryFree := rename_queryFree _ _ ProjectionStream.program_queryFree
lemma oneDelta_queryFree (a : OneGate) : (oneDelta a).QueryFree := seq_queryFree _ _ (localOne_queryFree a) projection_queryFree
lemma sampleDelta_queryFree : sampleDelta.QueryFree := seq_queryFree _ _ localSample_queryFree projection_queryFree

end HiddenCircuits.Circuit.Runtime.SampleEmitter
