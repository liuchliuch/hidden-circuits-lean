import HiddenCircuits.GraphReduction.Runtime.UnitCorrectionCompare

namespace HiddenCircuits.GraphReduction.Runtime.UnitCorrection
open Complexity Complexity.OracleBlock
set_option maxRecDepth 2000

def gateInputs (j : Fin 6) : Fin 8 → Fin 49 :=
  ![![0,1,22,2,4,3,5,23],![30,26,28,0,1,2,3,4],![30,27,29,0,1,2,3,4],
    ![11,14,32,31,9,10,24,25],![13,12,32,31,9,10,24,25],![33,34,0,1,2,3,4,5]] j
def gateMap (j : Fin 6) : Fin 18 ↪ Fin 49 where
  toFun i := if h : i.val<8 then gateInputs j ⟨i.val,h⟩ else
    if h : i.val<16 then ⟨28+i.val,by omega⟩ else
    if i.val=16 then ⟨30+j.val,by omega⟩ else 44
  inj' := by fin_cases j <;> decide +kernel

def arg (bs : List Bool) (i : ℕ) : Bool := bs[i]?.getD false
def gateFunction (second : Bool) (j : Fin 6) (bs : List Bool) : Bool :=
  if j=0 then arg bs 0 && !(arg bs 1) &&
    ((arg bs 2 && (arg bs 3 || arg bs 4)) ||
      (!(arg bs 2 && (arg bs 3 || arg bs 4 || arg bs 5 || arg bs 6)) && second && arg bs 7)) else
  if j=1 ∨ j=2 then if arg bs 0 then arg bs 2 else arg bs 1 else
  if j=3 ∨ j=4 then arg bs 4 && !(arg bs 5) && arg bs 6 && arg bs 7 &&
    ((arg bs 0 && arg bs 2) || (arg bs 1 && arg bs 3)) else
  !(arg bs 0) && arg bs 1

def gateBits (second : Bool) (width : ℕ) (x y : VertexRecord) (j : Fin 6) : Fin 8 → Bool :=
  ![![x.side,x.probe,bits second width x y 0,x.cut.leftRise,x.cut.rightRise,x.cut.leftDrop,x.cut.rightDrop,bits second width x y 1],
    ![bits second width x y 8,bits second width x y 4,bits second width x y 6,x.side,x.probe,x.cut.leftRise,x.cut.leftDrop,x.cut.rightRise],
    ![bits second width x y 8,bits second width x y 5,bits second width x y 7,x.side,x.probe,x.cut.leftRise,x.cut.leftDrop,x.cut.rightRise],
    ![y.cut.leftRise,y.cut.rightDrop,bits second width x y 10,bits second width x y 9,y.side,y.probe,bits second width x y 2,bits second width x y 3],
    ![y.cut.rightRise,y.cut.leftDrop,bits second width x y 10,bits second width x y 9,y.side,y.probe,bits second width x y 2,bits second width x y 3],
    ![bits second width x y 11,bits second width x y 12,x.side,x.probe,x.cut.leftRise,x.cut.leftDrop,x.cut.rightRise,x.cut.rightDrop]] j

lemma gateFunction_correct (second : Bool) (width : ℕ) (x y : VertexRecord) (j : Fin 6) :
    gateFunction second j (gate8Args (gateBits second width x y j))=
      bits second width x y ⟨8+j.val,by omega⟩ := by
  fin_cases j
  · rfl
  · simp only [gateFunction,gateBits,gate8Args,arg,bits]
    rw [correctionTrack_shifted]
    cases shifted second width x <;> rfl
  · simp only [gateFunction,gateBits,gate8Args,arg,bits]
    rw [correctionTrack_shifted]
    cases shifted second width x <;> rfl
  · rfl
  · rfl
  · rfl

noncomputable def gate (second : Bool) (j : Fin 6) : OracleBlock 48 := gate8On (gateMap j) (gateFunction second j)

theorem gate_executes (g : BitString → ℕ) (second : Bool) (width : ℕ) (x y : VertexRecord) (j : Fin 6) :
    (gate second j).Executes g (state second width x y 2 (8+j.val))
      (state second width x y 2 (8+j.val+1)) 92 := by
  have h := gate8On_executes (gateMap j) g (gateFunction second j) (gateBits second width x y j)
    (state second width x y 2 (8+j.val)) (by fin_cases j <;> funext i <;> fin_cases i <;> rfl)
  rw [gateFunction_correct] at h
  convert h using 1
  fin_cases j <;> funext i <;> fin_cases i <;> rfl

noncomputable def gateAll (second : Bool) : OracleBlock 48 := seq (gate second 0) (seq (gate second 1)
  (seq (gate second 2) (seq (gate second 3) (seq (gate second 4) (gate second 5)))))
theorem gateAll_executes (g : BitString → ℕ) (second : Bool) (width : ℕ) (x y : VertexRecord) :
    (gateAll second).Executes g (state second width x y 2 8) (state second width x y 2 14) 562 :=
  seq_executes _ _ g (gate_executes g second width x y 0) (seq_executes _ _ g (gate_executes g second width x y 1)
    (seq_executes _ _ g (gate_executes g second width x y 2) (seq_executes _ _ g (gate_executes g second width x y 3)
      (seq_executes _ _ g (gate_executes g second width x y 4) (gate_executes g second width x y 5)))))
lemma gateAll_queryFree (second : Bool) : (gateAll second).QueryFree :=
  seq_queryFree _ _ (gate8On_queryFree _ _) (seq_queryFree _ _ (gate8On_queryFree _ _)
    (seq_queryFree _ _ (gate8On_queryFree _ _) (seq_queryFree _ _ (gate8On_queryFree _ _)
      (seq_queryFree _ _ (gate8On_queryFree _ _) (gate8On_queryFree _ _)))))
end HiddenCircuits.GraphReduction.Runtime.UnitCorrection
