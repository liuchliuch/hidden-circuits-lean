import HiddenCircuits.DH.Runtime.PruningModel
import HiddenCircuits.DH.Runtime.WordArrayInitialize
import HiddenCircuits.Complexity.GraphVerifier.MatrixLookup
import HiddenCircuits.Complexity.GraphVerifier.ReadOnlyLength
import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision

/-! Exact Boolean specifications and finite ports for literal pair testing. -/
namespace HiddenCircuits.DH.Runtime.PairCheck
open Complexity Complexity.OracleBlock

/-- Live marks use singleton Boolean words in the same canonical array format
as the coefficient tables. -/
def liveWords {n : ℕ} (alive : Vector Bool n) : List BitString := alive.toList.map (fun b=>[b])
def liveBits {n : ℕ} (alive : Vector Bool n) : BitString := encodeBitList (liveWords alive)

lemma liveWords_get {n : ℕ} (alive : Vector Bool n) (v : Fin n) :
    (liveWords alive)[v.val]?.getD []=[alive[v.val]] := by
  simp [liveWords,List.getElem?_eq_getElem,v.isLt]

lemma liveBits_length {n : ℕ} (alive : Vector Bool n) : (liveBits alive).length=4*n := by
  simp [liveBits,liveWords,encodeBitList_length,List.map_map,Function.comp_def]
  omega

lemma matrixGraph_bit {n : ℕ} (G : MatrixGraph n) (u v : Fin n) :
    G.bits[v.val+n*u.val]?.toList=[G.edge u v] := by
  have hk : v.val+n*u.val<G.bits.length := by
    rw [MatrixGraph.bits_length]
    have hm := Nat.mul_le_mul_left n (show u.val+1≤n from u.isLt)
    nlinarith [v.isLt]
  rw [List.getElem?_eq_getElem hk]
  change [G.bits[v.val+n*u.val]]=[G.edge u v]
  congr 1
  exact G.get_bits u v hk

/-- A serialization relation for an arbitrary Boolean matrix. No graph-class,
symmetry, or looplessness condition enters the machine's operational theorem. -/
structure MatrixData (n : ℕ) where
  bits : BitString
  edge : Fin n → Fin n → Bool
  lookup : ∀u v, bits[v.val+n*u.val]?.toList=[edge u v]

namespace MatrixData

def ofGraph {n : ℕ} (G : MatrixGraph n) : MatrixData n :=
  ⟨G.bits,G.edge,matrixGraph_bit G⟩

lemma index_bound {n : ℕ} (u v : Fin n) : v.val+n*u.val<n*n := by
  have hm := Nat.mul_le_mul_left n (show u.val+1≤n from u.isLt)
  nlinarith [v.isLt]

/-- Every ordinary full-size payload determines its literal Boolean matrix. -/
def ofPayload (n : ℕ) (payload : BitString) (h : payload.length=n*n) : MatrixData n where
  bits := payload
  edge u v := payload[v.val+n*u.val]'(by rw [h];exact index_bound u v)
  lookup u v := by
    have hk : v.val+n*u.val<payload.length := by rw [h];exact index_bound u v
    simp only [List.getElem?_eq_getElem hk,Option.toList_some]

end MatrixData

lemma matrix_bit {n : ℕ} (G : MatrixData n) (u v : Fin n) :
    G.bits[v.val+n*u.val]?.toList=[G.edge u v] := G.lookup u v

/-- The mode is fixed in the compiled code: true for twins, false for pendant. -/
def cell {n : ℕ} (mode : Bool) (G : MatrixData n) (alive : Vector Bool n) (u v x : Fin n) : Bool :=
  !alive[x.val] || if mode then decide (x=u) || decide (x=v) || (G.edge v x == G.edge u x)
    else !G.edge v x || decide (x=u)

def cellsFrom {n : ℕ} (f : Fin n → Bool) (i : ℕ) : ℕ → Bool
  | 0 => true
  | m+1 => (if hi : i<n then f ⟨i,hi⟩ else false) && cellsFrom f (i+1) m

lemma cellsFrom_range {n : ℕ} (f : Fin n → Bool) (i m : ℕ) :
    cellsFrom f i m=(List.range' i m).all (fun j=>if hj:j<n then f ⟨j,hj⟩ else false) := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih => simp [cellsFrom,List.range'_succ,ih]

lemma cellsFrom_all {n : ℕ} (f : Fin n → Bool) : cellsFrom f 0 n=(List.finRange n).all f := by
  rw [cellsFrom_range,←List.range_eq_range',←List.map_coe_finRange_eq_range,List.all_map]
  apply List.all_congr rfl
  intro x
  simp only [Function.comp_def,dif_pos x.isLt]

def test {n : ℕ} (mode : Bool) (G : MatrixData n) (alive : Vector Bool n) (u v : Fin n) : Bool :=
  alive[u.val] && alive[v.val] && decide (u≠v) && (mode || G.edge v u) &&
    cellsFrom (cell mode G alive u v) 0 n

lemma test_false {n : ℕ} (G : MatrixGraph n) (alive : Vector Bool n) (u v : Fin n) :
    test false (MatrixData.ofGraph G) alive u v=PruningModel.pendantTest G.graph alive u v := by
  simp [test,cellsFrom_all,PruningModel.pendantTest,MatrixData.ofGraph,MatrixGraph.graph,Bool.or_assoc]
  congr 1

lemma test_true {n : ℕ} (G : MatrixGraph n) (alive : Vector Bool n) (u v : Fin n) :
    test true (MatrixData.ofGraph G) alive u v=PruningModel.twinTest G.graph alive u v := by
  simp only [test,cellsFrom_all,cell,Bool.true_or,↓reduceIte,Bool.and_true,PruningModel.twinTest]
  congr 1
  apply List.all_congr rfl
  intro x
  cases he : G.edge v x <;> cases hf : G.edge u x <;> simp [cell,MatrixData.ofGraph,MatrixGraph.graph,he,hf,Bool.or_assoc]

/-- Result words make all three successful action kinds distinguishable from failure. -/
def kindBits : PruningModel.Kind → BitString
  | .pendant => [false]
  | .twin b => [true,b]

def resultBits {n : ℕ} (a : Option (PruningModel.Action n)) : BitString :=
  a.map (fun a=>kindBits a.kind) |>.getD []

end HiddenCircuits.DH.Runtime.PairCheck
