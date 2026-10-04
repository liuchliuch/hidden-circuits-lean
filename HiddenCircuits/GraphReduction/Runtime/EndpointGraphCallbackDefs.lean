import HiddenCircuits.GraphReduction.Runtime.EndpointGraphDefs

namespace HiddenCircuits.GraphReduction.Runtime.EndpointGraph
open Complexity OracleBlock Approximation MonotoneEndpointEncoding
open CNFCloneEmitter
set_option maxHeartbeats 1200000

def params {n : ℕ} (E : MonotoneEndpoints n) : Store 31 := fun q =>
  if q.val=8 then List.replicate n true else if q.val=9 then encodeBitList (rows E.lo)
  else if q.val=10 then encodeBitList (rows E.hi) else []
def callbackState {n : ℕ} (E : MonotoneEndpoints n) (i j : ℕ) (bit out inner outer : BitString) : Store 31 :=
  MatrixEmitter.store (2*n) i j bit out inner outer (params E)
def value {n : ℕ} (E : MonotoneEndpoints n) (i j : ℕ) : Fin 4 → ℕ :=
  ![endpoint E.lo i,endpoint E.hi i,endpoint E.lo j,endpoint E.hi j]
def flags {n : ℕ} (E : MonotoneEndpoints n) (i j : ℕ) : Fin 6 → Bool :=
  ![decide (i<n),decide (j<n),decide (j-n<endpoint E.lo i),decide (j-n<endpoint E.hi i),
    decide (i-n<endpoint E.lo j),decide (i-n<endpoint E.hi j)]
def stage {n : ℕ} (E : MonotoneEndpoints n) (i j m : ℕ) (out inner outer : BitString) : Store 31 := fun q =>
  if q.val=11 then if 0<m then List.replicate (i-n) true else []
  else if q.val=12 then if 1<m then List.replicate (j-n) true else []
  else if q.val=13 then if 0<m then [flags E i j 0] else []
  else if q.val=14 then if 1<m then [flags E i j 1] else []
  else if q.val=15 then if 2<m then List.replicate (value E i j 0) true else []
  else if q.val=16 then if 3<m then List.replicate (value E i j 1) true else []
  else if q.val=17 then if 4<m then List.replicate (value E i j 2) true else []
  else if q.val=18 then if 5<m then List.replicate (value E i j 3) true else []
  else if q.val=19 then if 6<m then [flags E i j 2] else []
  else if q.val=20 then if 7<m then [flags E i j 3] else []
  else if q.val=21 then if 8<m then [flags E i j 4] else []
  else if q.val=22 then if 9<m then [flags E i j 5] else []
  else callbackState E i j [] out inner outer q

lemma stage_zero {n : ℕ} (E : MonotoneEndpoints n) (i j : ℕ) (out inner outer : BitString) :
    stage E i j 0 out inner outer=callbackState E i j [] out inner outer := by
  funext q;fin_cases q <;> rfl
lemma endpoint_bound {n : ℕ} (E : MonotoneEndpoints n) (i : ℕ) : endpoint E.lo i ≤ n ∧ endpoint E.hi i ≤ n := by
  by_cases hi:i<n
  · simp only [endpoint,dif_pos hi]
    exact ⟨(E.lo_le_hi _).trans (E.hi_le _),E.hi_le _⟩
  · simp [endpoint,hi]
lemma value_bound {n : ℕ} (E : MonotoneEndpoints n) (i j : ℕ) (r : Fin 4) : value E i j r ≤ n := by
  fin_cases r
  · exact (endpoint_bound E i).1
  · exact (endpoint_bound E i).2
  · exact (endpoint_bound E j).1
  · exact (endpoint_bound E j).2

def splitMap (second : Bool) : Fin 3 ↪ Fin 32 where
  toFun q := ![if second then 12 else 11,26,if second then 14 else 13] q
  inj' := by cases second <;> decide +kernel
noncomputable def splitIndex (second : Bool) : OracleBlock 31 :=
  seq (copyOn (if second then 2 else 1) (if second then 12 else 11) 27 (by cases second <;> decide)
    (by cases second <;> decide) (by cases second <;> decide))
    (seq (copyOn 8 26 27 (by decide) (by decide) (by decide)) (UnarySplit.on (splitMap second)))

def lookupMap (r : Fin 4) : Fin 7 ↪ Fin 32 where
  toFun q := (![if r.val=0 ∨ r.val=2 then 9 else 10,if r.val<2 then 1 else 2,
    ⟨15+r.val,by omega⟩,26,27,28,29] : Fin 7 → Fin 32) q
  inj' := by fin_cases r <;> decide +kernel
noncomputable def lookup (r : Fin 4) : OracleBlock 31 := listLookupOn (lookupMap r)
def compareMap (r : Fin 4) : Fin 6 ↪ Fin 32 where
  toFun q := (![if r.val<2 then 12 else 11,⟨15+r.val,by omega⟩,⟨19+r.val,by omega⟩,26,27,28] : Fin 6 → Fin 32) q
  inj' := by fin_cases r <;> decide +kernel
noncomputable def compare (r : Fin 4) : OracleBlock 31 := readOnlyLTOn (compareMap r)
def gate (bs : List Bool) : Bool :=
  (bs[0]?.getD false && !(bs[1]?.getD false) && !(bs[2]?.getD false) && bs[3]?.getD false) ||
  (bs[1]?.getD false && !(bs[0]?.getD false) && !(bs[4]?.getD false) && bs[5]?.getD false)
noncomputable def decideEdge : OracleBlock 31 := GraphVerifier.Runtime.decision 3 [13,14,19,20,21,22] gate
noncomputable def callback : OracleBlock 31 := seq (splitIndex false) (seq (splitIndex true)
  (seq (lookup 0) (seq (lookup 1) (seq (lookup 2) (seq (lookup 3)
    (seq (compare 0) (seq (compare 1) (seq (compare 2) (seq (compare 3)
      (seq decideEdge (clearList [11,12,15,16,17,18])))))))))))
def dataLength {n : ℕ} (E : MonotoneEndpoints n) : ℕ := (encodeBitList (rows E.lo)).length+(encodeBitList (rows E.hi)).length
def callbackBound (n L : ℕ) : ℕ := 4*lookupBound L (2*n)+300*n+300
end HiddenCircuits.GraphReduction.Runtime.EndpointGraph
