import HiddenCircuits.Complexity.GridRuntime.Frame
import HiddenCircuits.Complexity.GridWeightsRuntime
import HiddenCircuits.Complexity.GridTermRuntime
import HiddenCircuits.Complexity.GridPrefixBounds

/-! Physical register layout shared by the actual source-query grid body. -/
namespace HiddenCircuits.Complexity.SourceGrid
open OracleBlock BinaryArithmetic

structure Values where
  formula : BitString := []
  denominator : BitString := []
  accumulator : BitString := []
  leftWeight : BitString := []
  rightWeight : BitString := []
  numeratorWeight : BitString := []
  value : BitString := []
  temporary : BitString := []

def frame (v : Values) : GridRuntime.Frame 34 := fun q =>
  if q.val=0 then v.formula else if q.val=1 then v.denominator else if q.val=2 then v.accumulator else
  if q.val=3 then v.leftWeight else if q.val=4 then v.rightWeight else if q.val=5 then v.numeratorWeight else
  if q.val=6 then v.value else if q.val=7 then v.temporary else []

def store (n m i j : ℕ) (inner outer : BitString) (v : Values) : Store 42 :=
  GridRuntime.store n m i j inner outer (frame v)

def queryEmbedding : Fin 30 ↪ Fin 43 where
  toFun q := if q.val=7 then 15 else if q.val=8 then 9 else if q.val=9 then 2 else if q.val=10 then 4 else
    if h : q.val<7 then ⟨17+q.val,by omega⟩ else ⟨q.val+13,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def weightsEmbedding : Fin 20 ↪ Fin 43 where
  toFun q := if q.val=0 then 2 else if q.val=1 then 3 else if q.val=2 then 4 else if q.val=3 then 5 else
    if q.val=4 then 12 else if q.val=5 then 13 else if q.val=6 then 14 else if q.val=7 then 17 else ⟨q.val+10,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def arithmeticEmbedding : Fin 16 ↪ Fin 43 where
  toFun q := if q.val=9 then 10 else if q.val=10 then 12 else if q.val=11 then 13 else if q.val=12 then 14 else
    if q.val=13 then 15 else if q.val=14 then 11 else if q.val=15 then 16 else ⟨17+q.val,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def queryStore (formula : BitString) (a b : ℕ) (output : BitString) : Store 29 := fun q =>
  if q.val=7 then output else if q.val=8 then formula else if q.val=9 then List.replicate a true else
  if q.val=10 then List.replicate b true else []

lemma restrict_query (n m i j : ℕ) (inner outer : BitString) (v : Values) :
    store n m i j inner outer v ∘ queryEmbedding = queryStore v.formula i j v.value := by
  funext q;fin_cases q <;> rfl

lemma restrict_weights (n m i j : ℕ) (inner outer : BitString) (v : Values) :
    store n m i j inner outer v ∘ weightsEmbedding =
      GridWeightsRuntime.gridStore i (n-i) j (m-j) v.leftWeight v.rightWeight v.numeratorWeight [] := by
  funext q;fin_cases q <;> rfl

lemma restrict_arithmetic (n m i j : ℕ) (inner outer : BitString) (formula : BitString)
    (D di dj nu value acc temp : ℤ) :
    store n m i j inner outer
      {formula:=formula,denominator:=signedBits D,accumulator:=signedBits acc,
       leftWeight:=signedBits di,rightWeight:=signedBits dj,numeratorWeight:=signedBits nu,
       value:=signedBits value,temporary:=signedBits temp} ∘ arithmeticEmbedding =
      BinaryArithmetic.RegisterMachine.store [] [] (signedBits ∘ GridTermRuntime.registers D di dj nu value acc temp) := by
  funext q;fin_cases q <;> rfl

@[simp] lemma update_formula (n m i j : ℕ) (inner outer z : BitString) (v : Values) :
    Function.update (store n m i j inner outer v) (9 : Fin 43) z =
      store n m i j inner outer {v with formula:=z} := by
  funext q;fin_cases q <;> rfl

@[simp] lemma update_denominator (n m i j : ℕ) (inner outer z : BitString) (v : Values) :
    Function.update (store n m i j inner outer v) (10 : Fin 43) z =
      store n m i j inner outer {v with denominator:=z} := by
  funext q;fin_cases q <;> rfl

@[simp] lemma update_accumulator (n m i j : ℕ) (inner outer z : BitString) (v : Values) :
    Function.update (store n m i j inner outer v) (11 : Fin 43) z =
      store n m i j inner outer {v with accumulator:=z} := by
  funext q;fin_cases q <;> rfl

@[simp] lemma update_leftWeight (n m i j : ℕ) (inner outer z : BitString) (v : Values) :
    Function.update (store n m i j inner outer v) (12 : Fin 43) z =
      store n m i j inner outer {v with leftWeight:=z} := by
  funext q;fin_cases q <;> rfl

@[simp] lemma update_rightWeight (n m i j : ℕ) (inner outer z : BitString) (v : Values) :
    Function.update (store n m i j inner outer v) (13 : Fin 43) z =
      store n m i j inner outer {v with rightWeight:=z} := by
  funext q;fin_cases q <;> rfl

@[simp] lemma update_numeratorWeight (n m i j : ℕ) (inner outer z : BitString) (v : Values) :
    Function.update (store n m i j inner outer v) (14 : Fin 43) z =
      store n m i j inner outer {v with numeratorWeight:=z} := by
  funext q;fin_cases q <;> rfl

@[simp] lemma update_value (n m i j : ℕ) (inner outer z : BitString) (v : Values) :
    Function.update (store n m i j inner outer v) (15 : Fin 43) z =
      store n m i j inner outer {v with value:=z} := by
  funext q;fin_cases q <;> rfl

@[simp] lemma update_temporary (n m i j : ℕ) (inner outer z : BitString) (v : Values) :
    Function.update (store n m i j inner outer v) (16 : Fin 43) z =
      store n m i j inner outer {v with temporary:=z} := by
  funext q;fin_cases q <;> rfl

end HiddenCircuits.Complexity.SourceGrid
