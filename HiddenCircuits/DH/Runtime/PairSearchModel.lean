import HiddenCircuits.DH.Runtime.PairCheckModel

/-! Pure first-success semantics of the literal nested unary search loops. -/
namespace HiddenCircuits.DH.Runtime.PairSearch
open Complexity PairCheck

def tryPair {n : ℕ} (G : MatrixData n) (alive : Vector Bool n) (u v : Fin n) : Option (PruningModel.Action n) :=
  if test false G alive u v then some ⟨u,v,.pendant⟩
  else if test true G alive u v then some ⟨u,v,.twin (G.edge u v)⟩ else none

def step {n : ℕ} (G : MatrixData n) (alive : Vector Bool n) (u v : Fin n)
    (found : Option (PruningModel.Action n)) : Option (PruningModel.Action n) :=
  found.orElse (fun _=>tryPair G alive u v)

/-- Process m consecutive columns starting at j. Bounds are guarded on all inputs. -/
def rowFrom {n : ℕ} (G : MatrixData n) (alive : Vector Bool n) (u : Fin n) (j : ℕ) :
    ℕ → Option (PruningModel.Action n) → Option (PruningModel.Action n)
  | 0,found => found
  | m+1,found => if hj : j<n then rowFrom G alive u (j+1) m (step G alive u ⟨j,hj⟩ found) else found

/-- Process m consecutive rows starting at i, scanning each from column zero. -/
def rowsFrom {n : ℕ} (G : MatrixData n) (alive : Vector Bool n) (i : ℕ) :
    ℕ → Option (PruningModel.Action n) → Option (PruningModel.Action n)
  | 0,found => found
  | m+1,found => if hi : i<n then rowsFrom G alive (i+1) m (rowFrom G alive ⟨i,hi⟩ 0 n found) else found

def find {n : ℕ} (G : MatrixData n) (alive : Vector Bool n) : Option (PruningModel.Action n) :=
  rowsFrom G alive 0 n none

def keptBits {n : ℕ} (found : Option (PruningModel.Action n)) : BitString :=
  found.map (fun a=>List.replicate a.keep.val true) |>.getD []
def removedBits {n : ℕ} (found : Option (PruningModel.Action n)) : BitString :=
  found.map (fun a=>List.replicate a.removed.val true) |>.getD []

lemma kindBits_ne_nil (k : PruningModel.Kind) : kindBits k≠[] := by cases k <;> simp [kindBits]
lemma resultBits_eq_nil {n : ℕ} (a : Option (PruningModel.Action n)) : resultBits a=[] ↔ a=none := by
  cases a with
  | none => simp [resultBits]
  | some a => simp [resultBits,kindBits_ne_nil]

lemma tryPair_ofGraph {n : ℕ} (G : MatrixGraph n) (alive : Vector Bool n) (u v : Fin n) :
    tryPair (MatrixData.ofGraph G) alive u v=PruningModel.tryPair G.graph alive u v := by
  unfold tryPair
  rw [test_false,test_true]
  simp [PruningModel.tryPair,MatrixData.ofGraph,MatrixGraph.graph]

/-- Even an arbitrary Boolean matrix can only select distinct live labels. -/
lemma tryPair_live {n : ℕ} (G : MatrixData n) (alive : Vector Bool n) (u v : Fin n)
    {a : PruningModel.Action n} (ha : tryPair G alive u v=some a) :
    alive[a.keep.val]=true ∧ alive[a.removed.val]=true ∧ a.keep≠a.removed := by
  unfold tryPair at ha
  split at ha
  · cases ha
    have ht := ‹test false G alive u v=true›
    simp only [test,Bool.and_eq_true] at ht
    exact ⟨ht.1.1.1.1,ht.1.1.1.2,of_decide_eq_true ht.1.1.2⟩
  · split at ha
    · cases ha
      have ht := ‹test true G alive u v=true›
      simp only [test,Bool.and_eq_true] at ht
      exact ⟨ht.1.1.1.1,ht.1.1.1.2,of_decide_eq_true ht.1.1.2⟩
    · contradiction

end HiddenCircuits.DH.Runtime.PairSearch
