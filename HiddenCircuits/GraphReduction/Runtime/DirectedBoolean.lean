import HiddenCircuits.GraphReduction.Runtime.DirectedCore

/-! Fixed Boolean decision gates for the actual local cut/probe rule. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

def dirRiseEmbedding : Fin 18 ↪ Fin 41 where
  toFun i := ![25,26,21,22,23,24,0,9,32,33,34,35,36,37,38,39,27,40] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
noncomputable def dirRiseGate : OracleBlock 40 := gate8On dirRiseEmbedding andGate

theorem dirRiseGate_executes (g : BitString → ℕ) (x y : VertexRecord) :
    dirRiseGate.Executes g (dirState x y 6) (dirState x y 7) 92 := by
  let bits : Fin 8 → Bool := ![dirBits x y 4,dirBits x y 5,dirBits x y 0,dirBits x y 1,dirBits x y 2,dirBits x y 3,x.side,y.side]
  have h := gate8On_executes dirRiseEmbedding g andGate bits (dirState x y 6)
    (by funext i; fin_cases i <;> rfl)
  convert h using 1
  funext i; fin_cases i <;> rfl

def dirDropEmbedding : Fin 18 ↪ Fin 41 where
  toFun i := ![24,26,21,22,23,25,0,9,32,33,34,35,36,37,38,39,28,40] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
noncomputable def dirDropGate : OracleBlock 40 := gate8On dirDropEmbedding andGate

theorem dirDropGate_executes (g : BitString → ℕ) (x y : VertexRecord) :
    dirDropGate.Executes g (dirState x y 7) (dirState x y 8) 92 := by
  let bits : Fin 8 → Bool := ![dirBits x y 3,dirBits x y 5,dirBits x y 0,dirBits x y 1,dirBits x y 2,dirBits x y 4,x.side,y.side]
  have h := gate8On_executes dirDropEmbedding g andGate bits (dirState x y 7)
    (by funext i; fin_cases i <;> rfl)
  convert h using 1
  funext i; fin_cases i <;> rfl

def dirBaseEmbedding : Fin 18 ↪ Fin 41 where
  toFun i := ![23,21,22,24,25,26,0,9,32,33,34,35,36,37,38,39,29,40] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
noncomputable def dirBaseGate : OracleBlock 40 := gate8On dirBaseEmbedding notGate

theorem dirBaseGate_executes (g : BitString → ℕ) (x y : VertexRecord) :
    dirBaseGate.Executes g (dirState x y 8) (dirState x y 9) 92 := by
  let bits : Fin 8 → Bool := ![dirBits x y 2,dirBits x y 0,dirBits x y 1,dirBits x y 3,dirBits x y 4,dirBits x y 5,x.side,y.side]
  have h := gate8On_executes dirBaseEmbedding g notGate bits (dirState x y 8)
    (by funext i; fin_cases i <;> rfl)
  convert h using 1
  funext i; fin_cases i <;> rfl

def dirFirstEmbedding : Fin 18 ↪ Fin 41 where
  toFun i := ![29,11,12,27,28,21,22,23,32,33,34,35,36,37,38,39,30,40] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
noncomputable def dirFirstGate : OracleBlock 40 := gate8On dirFirstEmbedding cutGate

theorem dirFirstGate_executes (g : BitString → ℕ) (x y : VertexRecord) :
    dirFirstGate.Executes g (dirState x y 9) (dirState x y 10) 92 := by
  let bits : Fin 8 → Bool := ![dirBits x y 8,y.cut.leftRise,y.cut.leftDrop,dirBits x y 6,dirBits x y 7,dirBits x y 0,dirBits x y 1,dirBits x y 2]
  have h := gate8On_executes dirFirstEmbedding g cutGate bits (dirState x y 9)
    (by funext i; fin_cases i <;> rfl)
  have he : cutGate (gate8Args bits)=dirBits x y 9 := by
    simp [bits,gate8Args,cutGate,dirBits,cutBit,reverse_lt_neg,Bool.and_assoc]
  rw [he] at h
  convert h using 1
  funext i; fin_cases i <;> rfl

def dirSecondEmbedding : Fin 18 ↪ Fin 41 where
  toFun i := ![29,13,14,27,28,21,22,23,32,33,34,35,36,37,38,39,31,40] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
noncomputable def dirSecondGate : OracleBlock 40 := gate8On dirSecondEmbedding cutGate

theorem dirSecondGate_executes (g : BitString → ℕ) (x y : VertexRecord) :
    dirSecondGate.Executes g (dirState x y 10) (dirState x y 11) 92 := by
  let bits : Fin 8 → Bool := ![dirBits x y 8,y.cut.rightRise,y.cut.rightDrop,dirBits x y 6,dirBits x y 7,dirBits x y 0,dirBits x y 1,dirBits x y 2]
  have h := gate8On_executes dirSecondEmbedding g cutGate bits (dirState x y 10)
    (by funext i; fin_cases i <;> rfl)
  have he : cutGate (gate8Args bits)=dirBits x y 10 := by
    simp [bits,gate8Args,cutGate,dirBits,cutBit,reverse_lt_neg,Bool.and_assoc]
  rw [he] at h
  convert h using 1
  funext i; fin_cases i <;> rfl

def dirFinalEmbedding : Fin 18 ↪ Fin 41 where
  toFun i := ![0,9,1,10,21,22,30,31,32,33,34,35,36,37,38,39,18,40] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
noncomputable def dirFinalGate : OracleBlock 40 := gate8On dirFinalEmbedding directedGate

theorem dirFinalGate_executes (g : BitString → ℕ) (x y : VertexRecord) :
    dirFinalGate.Executes g (dirState x y 11) (dirState x y 11 [directedRecordAdj x y]) 92 := by
  let bits : Fin 8 → Bool := ![x.side,y.side,x.probe,y.probe,dirBits x y 0,dirBits x y 1,dirBits x y 9,dirBits x y 10]
  have h := gate8On_executes dirFinalEmbedding g directedGate bits (dirState x y 11)
    (by funext i; fin_cases i <;> rfl)
  have he : directedGate (gate8Args bits)=directedRecordAdj x y := by
    simp [bits,gate8Args,directedGate,dirBits,directedRecordAdj]
  rw [he] at h
  convert h using 1
  funext i; fin_cases i <;> rfl

noncomputable def dirBoolean : OracleBlock 40 := seq dirRiseGate (seq dirDropGate (seq dirBaseGate (seq dirFirstGate (seq dirSecondGate (dirFinalGate)))))

theorem dirBoolean_executes (g : BitString → ℕ) (x y : VertexRecord) :
    dirBoolean.Executes g (dirState x y 6) (dirState x y 11 [directedRecordAdj x y]) 562 :=
  seq_executes _ _ g (dirRiseGate_executes g x y) (seq_executes _ _ g (dirDropGate_executes g x y) (seq_executes _ _ g (dirBaseGate_executes g x y) (seq_executes _ _ g (dirFirstGate_executes g x y) (seq_executes _ _ g (dirSecondGate_executes g x y) ((dirFinalGate_executes g x y))))))

lemma dirBoolean_queryFree : dirBoolean.QueryFree :=
  seq_queryFree _ _ (gate8On_queryFree _ _) (seq_queryFree _ _ (gate8On_queryFree _ _) (seq_queryFree _ _ (gate8On_queryFree _ _) (seq_queryFree _ _ (gate8On_queryFree _ _) (seq_queryFree _ _ (gate8On_queryFree _ _) ((gate8On_queryFree _ _))))))

end HiddenCircuits.GraphReduction.Runtime
