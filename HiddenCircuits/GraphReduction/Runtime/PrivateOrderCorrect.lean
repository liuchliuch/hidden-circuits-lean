import HiddenCircuits.GraphReduction.Runtime.PrivateOrderLocal

/-! Fresh reconstruction: the local tests compare the exact two endpoint orders,
including empty boundary blocks and retained vertices. -/
namespace HiddenCircuits.GraphReduction.Runtime.PrivateOrder
open PrivateProbe

def upperPairAt {p h : ℕ} (pairs : Fin h → CutPair p) (j : Fin (h+1)) : CutPair p :=
  if hj:j.val<h then pairs ⟨j.val,hj⟩ else .background
def lowerPairAt {p h : ℕ} (pairs : Fin h → CutPair p) (j : Fin (h+1)) : CutPair p :=
  if hj:0<j.val then pairs ⟨j.val-1,by have := j.isLt;omega⟩ else .background
lemma upperPair_mode {p h : ℕ} (pairs : Fin h → CutPair p) (j : Fin (h+1)) :
    (upperPairAt pairs j).upperMode=upperModeAt pairs j := by
  unfold upperPairAt upperModeAt
  split_ifs <;> rfl
lemma lowerPair_mode {p h : ℕ} (pairs : Fin h → CutPair p) (j : Fin (h+1)) :
    (lowerPairAt pairs j).lowerMode=lowerModeAt pairs j := by
  unfold lowerPairAt lowerModeAt
  split_ifs <;> rfl

def normalize (x : VertexRecord) : VertexRecord := {x with layer:=0}
lemma normalize_upper {p h s : ℕ} (pairs : Fin h → CutPair p) (v : PrivateProbe.Vertex (2*p) h s) :
    normalize (rawRecord pairs v)=localRecord (upperPairAt pairs (PrivateProbe.topBlock v)) (PrivateProbe.content v) := by
  rcases v with (⟨j,u⟩|⟨r,u⟩)|(⟨j|r,q⟩) <;>
    simp [normalize,rawRecord,localRecord,upperPairAt,PrivateProbe.topBlock,PrivateProbe.content]
lemma normalize_lower {p h s : ℕ} (pairs : Fin h → CutPair p) (v : PrivateProbe.Vertex (2*p) h s) :
    normalize (rawRecord pairs v)=localRecord (lowerPairAt pairs (PrivateProbe.bottomBlock v)) (PrivateProbe.content v) := by
  rcases v with (⟨j,u⟩|⟨r,u⟩)|(⟨j|r,q⟩) <;>
    simp [normalize,rawRecord,localRecord,lowerPairAt,PrivateProbe.bottomBlock,PrivateProbe.content]

lemma upperLocal_raw {p h s : ℕ} (pairs : Fin h → CutPair p) (x y : PrivateProbe.Vertex (2*p) h s)
    (he : PrivateProbe.topBlock x=PrivateProbe.topBlock y) :
    upperLocalLT (rawRecord pairs x) (rawRecord pairs y)=
      decide ((PrivateProbe.upperPosition pairs x).2.val<(PrivateProbe.upperPosition pairs y).2.val) := by
  change upperLocalLT (normalize (rawRecord pairs x)) (normalize (rawRecord pairs y))=_
  rw [normalize_upper,normalize_upper,he,upperLocal_correct,upperPair_mode]
  simp only [PrivateProbe.upperPosition,he]
lemma lowerLocal_raw {p h s : ℕ} (pairs : Fin h → CutPair p) (x y : PrivateProbe.Vertex (2*p) h s)
    (he : PrivateProbe.bottomBlock x=PrivateProbe.bottomBlock y) :
    lowerLocalLT (rawRecord pairs x) (rawRecord pairs y)=
      decide ((PrivateProbe.lowerPosition pairs x).2.val<(PrivateProbe.lowerPosition pairs y).2.val) := by
  change lowerLocalLT (normalize (rawRecord pairs x)) (normalize (rawRecord pairs y))=_
  rw [normalize_lower,normalize_lower,he,lowerLocal_correct,lowerPair_mode]
  simp only [PrivateProbe.lowerPosition,he]

lemma upper_raw {p h s : ℕ} (pairs : Fin h → CutPair p) (x y : PrivateProbe.Vertex (2*p) h s) :
    upperRecordLT (rawRecord pairs x) (rawRecord pairs y)=
      decide (digitRank (PrivateProbe.upperPosition pairs x)<digitRank (PrivateProbe.upperPosition pairs y)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [upperRecordLT,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,upperLayer_eq,digitRank_lt_iff]
  apply or_congr Iff.rfl
  apply and_congr_right
  intro he
  rw [upperLocal_raw pairs x y (Fin.ext he),decide_eq_true_eq]
lemma lower_raw {p h s : ℕ} (pairs : Fin h → CutPair p) (x y : PrivateProbe.Vertex (2*p) h s) :
    lowerRecordLT (rawRecord pairs x) (rawRecord pairs y)=
      decide (digitRank (PrivateProbe.lowerPosition pairs x)<digitRank (PrivateProbe.lowerPosition pairs y)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [lowerRecordLT,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,lowerLayer_eq,digitRank_lt_iff]
  apply or_congr Iff.rfl
  apply and_congr_right
  intro he
  rw [lowerLocal_raw pairs x y (Fin.ext he),decide_eq_true_eq]

theorem upperRecordLT_correct {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x y : PrivateQueryVertex p h s S T) :
    upperRecordLT (privateVertexRecord pairs x) (privateVertexRecord pairs y)=
      decide ((PrivateProbe.retainedDiagram pairs S T s).upper x<(PrivateProbe.retainedDiagram pairs S T s).upper y) := by
  have hh := upper_raw pairs (PrivateProbe.retainedEmbedding S T s x) (PrivateProbe.retainedEmbedding S T s y)
  rw [rawRecord_retained,rawRecord_retained] at hh
  exact hh
 theorem lowerRecordLT_correct {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x y : PrivateQueryVertex p h s S T) :
    lowerRecordLT (privateVertexRecord pairs x) (privateVertexRecord pairs y)=
      decide ((PrivateProbe.retainedDiagram pairs S T s).lower x<(PrivateProbe.retainedDiagram pairs S T s).lower y) := by
  have hh := lower_raw pairs (PrivateProbe.retainedEmbedding S T s x) (PrivateProbe.retainedEmbedding S T s y)
  rw [rawRecord_retained,rawRecord_retained] at hh
  exact hh
end HiddenCircuits.GraphReduction.Runtime.PrivateOrder
