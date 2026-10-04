import HiddenCircuits.GraphReduction.Runtime.MonotoneOrderTranspose
import HiddenCircuits.GraphReduction.Runtime.UnaryCount
import HiddenCircuits.GraphReduction.Runtime.TripleSerialization

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 900000
structure Accum where
  lows : BitString
  highs : BitString
  count : ℕ

def initialAccum : Accum := ⟨[],[],0⟩
def emitValues (A : Accum) (u v : ℕ) : Accum :=
  ⟨(wordChunk (List.replicate (min u v) true)).reverse++A.lows,
   (wordChunk (List.replicate (max u v) true)).reverse++A.highs,A.count+1⟩
def high (k : ℕ) (ranks : BitString) (A : Accum) (upper lower flag : BitString) : Fin 13→BitString :=
  ![List.replicate k true,ranks,A.lows,A.highs,List.replicate A.count true,upper,lower,flag,[],[],[],[],[]]
def combine (low : Store 56) (hi : Fin 13→BitString) : Store 69 := fun i=>
  if h:i.val<57 then low ⟨i.val,h⟩ else hi ⟨i.val-57,by omega⟩
def state (R : List VertexRecord) (i k : ℕ) (candidates ranks : BitString) (A : Accum)
    (count upper lower flag side : BitString := []) : Store 69 :=
  combine (MatrixEmitter.store (k:=49) R.length i 0 side count [] candidates
    (callbackParams (encodeBitList (R.map encodeVertex)))) (high k ranks A upper lower flag)
def embedding : Fin 57 ↪ Fin 70 := Fin.castAddEmb 13
noncomputable def countProgram (lower right : Bool) : OracleBlock 69 :=
  rename (UnaryCount.program (MonotoneOrderTranspose.program lower right false)) embedding
noncomputable def leftProgram : OracleBlock 69 := rename (MonotoneOrderTranspose.program false false true) embedding

def edge (lower right : Bool) (R : List VertexRecord) (i j : ℕ) : Bool :=
  MonotoneOrderRuntime.recordLT lower right false R j i
def countValue (lower right : Bool) (R : List VertexRecord) (i : ℕ) : ℕ :=
  UnaryCount.rowCount (edge lower right R) i 0 R.length
lemma countValue_le (lower right : Bool) (R : List VertexRecord) (i : ℕ) : countValue lower right R i≤R.length :=
  UnaryCount.rowCount_le _ _ _ _
def countBound (n L : ℕ) := n*(MonotoneOrderRuntime.bound n L+16)+8

lemma count_executes (g : BitString→ℕ) (lower right : Bool) (R : List VertexRecord) (i k : ℕ)
    (candidates ranks : BitString) (A : Accum) (upper down : BitString) (hi:i<R.length) :
    ∃c,(countProgram lower right).Executes g (state R i k candidates ranks A [] upper down)
      (state R i k candidates ranks A (List.replicate (countValue lower right R i) true) upper down) c ∧
      c≤countBound R.length (encodeBitList (R.map encodeVertex)).length := by
  obtain ⟨c,hc,hb⟩:=UnaryCount.program_executes (MonotoneOrderTranspose.program lower right false)
    (edge lower right R) R.length (MonotoneOrderRuntime.bound R.length (encodeBitList (R.map encodeVertex)).length)
    (callbackParams (encodeBitList (R.map encodeVertex)))
    (by intro g i j out inner outer hi hj;exact MonotoneOrderTranspose.framed g lower right false R i j hi hj out inner outer)
    g i candidates hi
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ embedding g hc
  · funext j;fin_cases j <;> rfl
  · funext j;fin_cases j <;> rfl
  · intro j hj
    have hlo:¬j.val<57:=by intro h;exact hj ⟨j.val,h⟩ (Fin.ext rfl)
    simp only [state,combine,hlo,↓reduceDIte]
lemma left_executes (g : BitString→ℕ) (R : List VertexRecord) (i k : ℕ)
    (candidates ranks : BitString) (A : Accum) (flag : BitString) (hi:i<R.length) :
    ∃c,leftProgram.Executes g (state R i k candidates ranks A [] [] [] flag)
      (state R i k candidates ranks A [] [] [] flag [!(R[i]?.getD defaultRecord).side]) c ∧
      c≤MonotoneOrderRuntime.bound R.length (encodeBitList (R.map encodeVertex)).length := by
  obtain ⟨c,hc,hb⟩:=MonotoneOrderTranspose.framed g false false true R i 0 hi (by omega) [] [] candidates
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ embedding g hc
  · funext j;fin_cases j <;> rfl
  · funext j;fin_cases j <;> rfl
  · intro j hj
    have hlo:¬j.val<57:=by intro h;exact hj ⟨j.val,h⟩ (Fin.ext rfl)
    simp only [state,combine,hlo,↓reduceDIte]
lemma count_queryFree (lower right : Bool) : (countProgram lower right).QueryFree := rename_queryFree _ _
  (UnaryCount.program_queryFree _ (MonotoneOrderTranspose.program_queryFree _ _ _))
lemma left_queryFree : leftProgram.QueryFree := rename_queryFree _ _ (MonotoneOrderTranspose.program_queryFree _ _ _)
end HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
