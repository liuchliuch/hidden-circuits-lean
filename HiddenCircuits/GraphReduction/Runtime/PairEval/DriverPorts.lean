import HiddenCircuits.GraphReduction.Runtime.PairEval.GraphRatio
import HiddenCircuits.GraphReduction.Runtime.PairEval.DriverAccumulate

/-! Fresh reconstruction: injective physical layouts for the ordinary query
and ratio cells inside the fixed 98-stack driver. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.Driver
open Complexity OracleBlock BinaryArithmetic WordGraph
set_option maxHeartbeats 900000

def queryPort (i : ℕ) : ℕ := if i=0 then 0 else if i=1 then 15 else if i=2 then 6 else if i=3 then 12 else i+12
lemma queryPort_injective : Function.Injective queryPort := by
  intro i j h
  unfold queryPort at h
  split_ifs at h <;> omega
def queryEmbedding : Fin 86 ↪ Fin 98 where
  toFun i := ⟨queryPort i.val,by unfold queryPort;split_ifs <;> have := i.isLt <;> omega⟩
  inj' := by intro i j h;apply Fin.ext;exact queryPort_injective (congrArg Fin.val h)

def ratioLow : Fin 9 ↪ Fin 18 where
  toFun i := ![16,17,6,5,1,2,12,13,14] i
  inj' := by decide +kernel
def ratioPort (i : ℕ) : ℕ := if h : i < 9 then (ratioLow ⟨i,h⟩).val else i+9
lemma ratioPort_low {i : ℕ} (hi : i < 9) : ratioPort i < 18 := by
  simpa only [ratioPort,dif_pos hi] using (ratioLow ⟨i,hi⟩).isLt
lemma ratioPort_high {i : ℕ} (hi : 9 ≤ i) : ratioPort i=i+9 := by
  simp only [ratioPort,dif_neg (by omega : ¬i < 9)]
lemma ratioPort_injective : Function.Injective ratioPort := by
  intro i j h
  by_cases hi : i < 9
  · by_cases hj : j < 9
    · simp only [ratioPort,dif_pos hi,dif_pos hj] at h
      exact congrArg Fin.val (ratioLow.injective (Fin.ext h))
    · have hb := ratioPort_low hi
      rw [ratioPort_high (i := j) (by omega)] at h
      omega
  · by_cases hj : j < 9
    · have hb := ratioPort_low hj
      rw [ratioPort_high (i := i) (by omega)] at h
      omega
    · rw [ratioPort_high (i := i) (by omega),ratioPort_high (i := j) (by omega)] at h
      omega

def ratioEmbedding : Fin 53 ↪ Fin 98 where
  toFun i := ⟨ratioPort i.val,by
    by_cases hi:i.val<9
    · exact (ratioPort_low hi).trans (by decide)
    · rw [ratioPort_high (by omega)];have := i.isLt;omega⟩
  inj' := by intro i j h;apply Fin.ext;exact ratioPort_injective (congrArg Fin.val h)
noncomputable def ratioCell (kind : GraphRecovery.Kind) : OracleBlock 97 := rename (GraphRatio.program kind) ratioEmbedding

lemma ratioCell_executes (g : BitString → ℕ) (kind : GraphRecovery.Kind) (w : PairInput) (s : GraphRecovery.Index w)
    (a : ℤ×ℤ) (answer B : ℕ) (hB : GraphRatio.componentBound kind w s answer B) :
    ∃c,(ratioCell kind).Executes g
      (state w (degree w-s.val) s.val a (signedBits (answer:ℤ)) [] [])
      (state w (degree w-s.val) s.val a (signedBits (answer:ℤ))
        (signedBits (GraphRecovery.ratio kind w s answer).1) (signedBits (GraphRecovery.ratio kind w s answer).2)) c ∧
      c≤GraphRatio.costBound kind w s answer B := by
  obtain ⟨c,hc,hb⟩ := GraphRatio.program_executes g kind w s answer B hB
  refine ⟨c,?_,hb⟩
  apply rename_executes_to (GraphRatio.program kind) ratioEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h13 : i.val≠13 := by intro h;exact hi 7 (Fin.ext h.symm)
    have h14 : i.val≠14 := by intro h;exact hi 8 (Fin.ext h.symm)
    simp only [state,h13,h14,if_false]
end HiddenCircuits.GraphReduction.Runtime.PairEval.Driver
