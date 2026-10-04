import HiddenCircuits.Circuit.Runtime.SourceScanPrefixes
import HiddenCircuits.Circuit.Runtime.EdgeEndpoints
import HiddenCircuits.Circuit.Runtime.RestoringEdgeEmitterCorrectness
import HiddenCircuits.Complexity.GraphVerifier.MatrixLookup

/-! A fixed physical layout for the actual graph edge-to-gate scan. -/
namespace HiddenCircuits.Circuit.Runtime.SourceScan
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

structure Values where
  wires : ℕ
  payload : BitString
  output : BitString
  swaps : ℕ
  lo : ℕ := 0
  distance : ℕ := 0
  flag : BitString := []

def frame (v : Values) : GridRuntime.Frame 27 := fun q =>
  if q.val=0 then List.replicate v.wires true else if q.val=1 then v.payload else
  if q.val=2 then v.output else if q.val=3 then List.replicate v.swaps true else
  if q.val=4 then List.replicate v.lo true else if q.val=5 then List.replicate v.distance true else
  if q.val=6 then v.flag else []

def store (k i j : ℕ) (inner outer : BitString) (v : Values) : Store 35 :=
  GridRuntime.store k k i j inner outer (frame v)

def lookupEmbedding : Fin 9 ↪ Fin 36 where
  toFun q := if q.val=0 then 9 else if q.val=1 then 2 else if q.val=2 then 4 else
    if q.val=3 then 10 else if q.val=4 then 15 else ⟨q.val+11,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def endpointsEmbedding : Fin 8 ↪ Fin 36 where
  toFun q := if q.val=0 then 2 else if q.val=1 then 4 else if q.val=2 then 13 else
    if q.val=3 then 14 else ⟨q.val+12,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def edgeEmbedding : Fin 8 ↪ Fin 36 where
  toFun q := if q.val=0 then 13 else if q.val=1 then 14 else if q.val=2 then 11 else ⟨q.val+13,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

lemma restrict_lookup (k i j : ℕ) (inner outer : BitString) (v : Values) :
    store k i j inner outer v ∘ lookupEmbedding = GraphVerifier.Runtime.matrixStore
      (List.replicate v.wires true) (List.replicate i true) (List.replicate j true) v.payload v.flag [] [] [] [] := by
  funext q;fin_cases q <;> rfl

lemma restrict_endpoints (k i j : ℕ) (inner outer : BitString) (v : Values) :
    store k i j inner outer v ∘ endpointsEmbedding = EdgeEndpoints.store i j v.lo v.distance 0 0 [] := by
  funext q;fin_cases q <;> rfl

lemma restrict_edge (k i j : ℕ) (inner outer : BitString) (v : Values) :
    store k i j inner outer v ∘ edgeEmbedding = RestoringEdgeEmitter.store v.lo v.distance 0 0 v.output [] [] [] := by
  funext q;fin_cases q <;> rfl

@[simp] lemma update_output (k i j : ℕ) (inner outer out : BitString) (v : Values) :
    Function.update (store k i j inner outer v) (11 : Fin 36) out=store k i j inner outer {v with output:=out} := by
  funext q;fin_cases q <;> rfl
@[simp] lemma update_flag (k i j : ℕ) (inner outer flag : BitString) (v : Values) :
    Function.update (store k i j inner outer v) (15 : Fin 36) flag=store k i j inner outer {v with flag:=flag} := by
  funext q;fin_cases q <;> rfl
@[simp] lemma update_swaps (k i j swaps : ℕ) (inner outer : BitString) (v : Values) :
    Function.update (store k i j inner outer v) (12 : Fin 36) (List.replicate swaps true)=
      store k i j inner outer {v with swaps:=swaps} := by
  funext q;fin_cases q <;> rfl
@[simp] lemma update_lo (k i j lo : ℕ) (inner outer : BitString) (v : Values) :
    Function.update (store k i j inner outer v) (13 : Fin 36) (List.replicate lo true)=
      store k i j inner outer {v with lo:=lo} := by
  funext q;fin_cases q <;> rfl
@[simp] lemma update_distance (k i j distance : ℕ) (inner outer : BitString) (v : Values) :
    Function.update (store k i j inner outer v) (14 : Fin 36) (List.replicate distance true)=
      store k i j inner outer {v with distance:=distance} := by
  funext q;fin_cases q <;> rfl

end HiddenCircuits.Circuit.Runtime.SourceScan
