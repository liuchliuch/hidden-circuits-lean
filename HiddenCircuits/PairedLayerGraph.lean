import HiddenCircuits.LayeredSize
import HiddenCircuits.PairedSampling

/-! Actual simple-unweighted PairEval graphs and their exact transfer and size identities. -/
namespace HiddenCircuits

 theorem CutPair.first_zero_one {p : ℕ} (P : CutPair p) (i j : Fin (2*p)) :
    P.first i j=0 ∨ P.first i j=1 := by
  cases P <;> simp only [CutPair.first,addedCut,deletedCut,upper] <;> split_ifs <;> simp
 theorem CutPair.second_zero_one {p : ℕ} (P : CutPair p) (i j : Fin (2*p)) :
    P.second i j=0 ∨ P.second i j=1 := by
  cases P <;> simp only [CutPair.second,Matrix.transpose_apply,addedCut,deletedCut,upper] <;> split_ifs <;> simp

/-- The first and second cut edges, as literal Boolean biadjacency matrices. -/
def CutPair.firstCut {p : ℕ} (P : CutPair p) : UnweightedCut p :=
  fun i j => decide (P.first i j=1)
def CutPair.secondCut {p : ℕ} (P : CutPair p) : UnweightedCut p :=
  fun i j => decide (P.second i j=1)

@[simp] theorem CutPair.cutMatrix_first {p : ℕ} (P : CutPair p) : cutMatrix P.firstCut=P.first := by
  ext i j
  rcases P.first_zero_one i j with h | h <;> simp [cutMatrix,firstCut,h]
@[simp] theorem CutPair.cutMatrix_second {p : ℕ} (P : CutPair p) : cutMatrix P.secondCut=P.second := by
  ext i j
  rcases P.second_zero_one i j with h | h <;> simp [cutMatrix,secondCut,h]

/-- Literal consecutive cuts of the paired layer graph. -/
def pairCuts {p : ℕ} (w : List (CutPair p)) : List (UnweightedCut p) :=
  w.flatMap (fun P => [P.firstCut,P.secondCut])

@[simp] theorem pairCuts_length {p : ℕ} (w : List (CutPair p)) : (pairCuts w).length=2*w.length := by
  induction w with
  | nil => rfl
  | cons P w ih =>
    change ([P.firstCut,P.secondCut] ++ pairCuts w).length=2*(w.length+1)
    rw [List.length_append,ih]
    simp only [List.length_cons,List.length_nil]
    omega

 theorem pairCuts_transfer {p : ℕ} (w : List (CutPair p)) :
    transferProduct (pairCuts w) = pairWordMatrix w := by
  induction w with
  | nil => rfl
  | cons P w ih =>
    change layerTransfer (cutMatrix P.firstCut) *
      (layerTransfer (cutMatrix P.secondCut) * transferProduct (pairCuts w)) =
      CutPair.matrix P * pairWordMatrix w
    rw [CutPair.cutMatrix_first,CutPair.cutMatrix_second,ih]
    exact (Matrix.mul_assoc ..).symm

/-- PairEval is literally an ordinary perfect-matching count of the retained layered graph. -/
theorem pairWordMatrix_eq_matchingCount {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p) :
    pairWordMatrix w S T = (Layered.matchingCount (pairCuts w) S T : ℚ) := by
  rw [Layered.matchingCount_eq_transferProduct,pairCuts_transfer]

/-- The retained graph for h positive cut pairs has exactly 4ph vertices. -/
theorem pairCuts_vertex_count {p : ℕ} (w : List (CutPair p)) (hw : w≠[])
    (S T : State (2*p) p) :
    Fintype.card (Layered.Retained (pairCuts w) S T) = 4*p*w.length := by
  have hc : pairCuts w≠[] := by
    intro he
    have hl := pairCuts_length w
    rw [he] at hl
    have hz : w.length=0 := by simp only [List.length_nil] at hl; omega
    exact hw (by simpa using hz)
  rw [Layered.retained_card _ hc,pairCuts_length]
  ring

/-- The actual sampled oracle graph has the stated polynomial number of retained vertices. -/
theorem sampleWord_vertex_count {p : ℕ} (w : List (Letter (2*p))) (hw : w≠[]) (t : ℕ)
    (S T : State (2*p) p) :
    Fintype.card (Layered.Retained (pairCuts (sampleWord w t)) S T) = 4*p*w.length*(t+1) := by
  have hs : sampleWord w t≠[] := by
    intro he
    have hl := sampleWord_length w t
    rw [he] at hl
    have hwpos : 0<w.length := List.length_pos_iff.mpr hw
    simp only [List.length_nil] at hl
    nlinarith
  rw [pairCuts_vertex_count _ hs,sampleWord_length]
  ring

end HiddenCircuits
