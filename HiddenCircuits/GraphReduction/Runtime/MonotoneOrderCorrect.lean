import HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointDefs

/-! The structural comparator agrees with the actual retained monotone diagram,
including probes and both empty boundary blocks. -/
namespace HiddenCircuits.GraphReduction.Runtime.MonotoneOrder
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

 def rawRecord {p h s : ℕ} (pairs : Fin h → CutPair p) : MonotoneVertex (2*p) h s → VertexRecord
  | .inl (.inl x) => ⟨false,false,x.1.val,x.2.val,backgroundCode⟩
  | .inl (.inr x) => ⟨false,true,x.1.val,x.2.val,backgroundCode⟩
  | .inr (.inl y) => ⟨true,false,y.1.val,y.2.val,cutCode (pairs y.1)⟩
  | .inr (.inr y) => ⟨true,true,y.1.val,y.2.val,backgroundCode⟩
 def localRecord {p s : ℕ} (P : CutPair p) : BlockContent (2*p) s → VertexRecord
  | .inl (.inl u) => ⟨false,false,0,u.val,backgroundCode⟩
  | .inl (.inr u) => ⟨true,false,0,u.val,cutCode P⟩
  | .inr (.inl q) => ⟨true,true,0,q.val,backgroundCode⟩
  | .inr (.inr q) => ⟨false,true,0,q.val,backgroundCode⟩

lemma upperLocal_correct {p s : ℕ} (P : CutPair p) (x y : BlockContent (2*p) s) :
    upperLocalLT (localRecord P x) (localRecord P y)=
      decide ((upperBlock P.upperMode s x).val<(upperBlock P.upperMode s y).val) := by
  rcases x with (u|u)|(q|q) <;> rcases y with (v|v)|(r|r)
  all_goals simp only [localRecord,upperLocalLT,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,
    Bool.not_false,Bool.not_true,Bool.and_false,Bool.false_and,Bool.true_and,Bool.and_true,beq_self_eq_true,
    (show (false==true)=false from rfl),(show (true==false)=false from rfl),cutBit_first,
    upperBlock_even,upperBlock_odd,upperBlock_P,upperBlock_Q,
    InterleaveMode.evenOffset_lt_iff,InterleaveMode.oddOffset_lt_iff,
    InterleaveMode.odd_lt_even_matrix,InterleaveMode.even_lt_odd_matrix,CutPair.upperMode_matrix]
  all_goals try have hu := P.upperMode.evenOffset_lt u
  all_goals try have hu' := P.upperMode.oddOffset_lt u
  all_goals try have hv := P.upperMode.evenOffset_lt v
  all_goals try have hv' := P.upperMode.oddOffset_lt v
  all_goals try have hq := q.isLt
  all_goals try have hr := r.isLt
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp only [Bool.false_eq_true,Bool.not_eq_true,decide_eq_true_eq,decide_eq_false_iff_not,iff_false,iff_true]
  all_goals try simp_all
  all_goals omega

lemma lowerLocal_correct {p s : ℕ} (P : CutPair p) (x y : BlockContent (2*p) s) :
    lowerLocalLT (localRecord P x) (localRecord P y)=
      decide ((lowerBlock P.lowerMode s x).val<(lowerBlock P.lowerMode s y).val) := by
  rcases x with (u|u)|(q|q) <;> rcases y with (v|v)|(r|r)
  all_goals simp only [localRecord,lowerLocalLT,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,
    Bool.not_false,Bool.not_true,Bool.and_false,Bool.false_and,Bool.true_and,Bool.and_true,beq_self_eq_true,
    (show (false==true)=false from rfl),(show (true==false)=false from rfl),cutBit_second,
    lowerBlock_even,lowerBlock_odd,lowerBlock_P,lowerBlock_Q,Nat.add_lt_add_iff_left,
    InterleaveMode.evenOffset_lt_iff,InterleaveMode.oddOffset_lt_iff,
    InterleaveMode.odd_lt_even_matrix,InterleaveMode.even_lt_odd_matrix,CutPair.lowerMode_matrix,Matrix.transpose_apply]
  all_goals try have hu := P.lowerMode.evenOffset_lt u
  all_goals try have hu' := P.lowerMode.oddOffset_lt u
  all_goals try have hv := P.lowerMode.evenOffset_lt v
  all_goals try have hv' := P.lowerMode.oddOffset_lt v
  all_goals try have hq := q.isLt
  all_goals try have hr := r.isLt
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp only [Bool.false_eq_true,Bool.not_eq_true,decide_eq_true_eq,decide_eq_false_iff_not,iff_false,iff_true]
  all_goals try simp_all
  all_goals omega

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
lemma normalize_upper {p h s : ℕ} (pairs : Fin h → CutPair p) (v : MonotoneVertex (2*p) h s) :
    normalize (rawRecord pairs v)=localRecord (upperPairAt pairs (topBlock v)) (endpointContent v) := by
  rcases v with (⟨j,u⟩|⟨r,u⟩)|(⟨j,q⟩|⟨r,q⟩) <;>
    simp [normalize,rawRecord,localRecord,upperPairAt,topBlock,endpointContent]
lemma normalize_lower {p h s : ℕ} (pairs : Fin h → CutPair p) (v : MonotoneVertex (2*p) h s) :
    normalize (rawRecord pairs v)=localRecord (lowerPairAt pairs (bottomBlock v)) (endpointContent v) := by
  rcases v with (⟨j,u⟩|⟨r,u⟩)|(⟨j,q⟩|⟨r,q⟩) <;>
    simp [normalize,rawRecord,localRecord,lowerPairAt,bottomBlock,endpointContent]
lemma upperLayer_eq {p h s : ℕ} (pairs : Fin h → CutPair p) (v : MonotoneVertex (2*p) h s) :
    (rawRecord pairs v).layer=(topBlock v).val := by
  rcases v with (x|x)|(x|x) <;> rfl
lemma lowerLayer_eq {p h s : ℕ} (pairs : Fin h → CutPair p) (v : MonotoneVertex (2*p) h s) :
    lowerLayer (rawRecord pairs v)=(bottomBlock v).val := by
  rcases v with (x|x)|(x|x) <;> simp [lowerLayer,rawRecord,bottomBlock]
lemma upperLocal_raw {p h s : ℕ} (pairs : Fin h → CutPair p) (x y : MonotoneVertex (2*p) h s)
    (he : topBlock x=topBlock y) :
    upperLocalLT (rawRecord pairs x) (rawRecord pairs y)=
      decide ((upperPosition pairs x).2.val<(upperPosition pairs y).2.val) := by
  change upperLocalLT (normalize (rawRecord pairs x)) (normalize (rawRecord pairs y))=_
  rw [normalize_upper,normalize_upper,he,upperLocal_correct,upperPair_mode]
  simp only [upperPosition,he]
lemma lowerLocal_raw {p h s : ℕ} (pairs : Fin h → CutPair p) (x y : MonotoneVertex (2*p) h s)
    (he : bottomBlock x=bottomBlock y) :
    lowerLocalLT (rawRecord pairs x) (rawRecord pairs y)=
      decide ((lowerPosition pairs x).2.val<(lowerPosition pairs y).2.val) := by
  change lowerLocalLT (normalize (rawRecord pairs x)) (normalize (rawRecord pairs y))=_
  rw [normalize_lower,normalize_lower,he,lowerLocal_correct,lowerPair_mode]
  simp only [lowerPosition,he]
lemma upper_raw {p h s : ℕ} (pairs : Fin h → CutPair p) (x y : MonotoneVertex (2*p) h s) :
    upperRecordLT (rawRecord pairs x) (rawRecord pairs y)=
      decide (digitRank (upperPosition pairs x)<digitRank (upperPosition pairs y)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [upperRecordLT,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,upperLayer_eq,digitRank_lt_iff]
  apply or_congr Iff.rfl
  apply and_congr_right
  intro he
  rw [upperLocal_raw pairs x y (Fin.ext he),decide_eq_true_eq]
lemma lower_raw {p h s : ℕ} (pairs : Fin h → CutPair p) (x y : MonotoneVertex (2*p) h s) :
    lowerRecordLT (rawRecord pairs x) (rawRecord pairs y)=
      decide (digitRank (lowerPosition pairs x)<digitRank (lowerPosition pairs y)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [lowerRecordLT,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,lowerLayer_eq,digitRank_lt_iff]
  apply or_congr Iff.rfl
  apply and_congr_right
  intro he
  rw [lowerLocal_raw pairs x y (Fin.ext he),decide_eq_true_eq]
lemma rawRecord_retained {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (v : QueryVertex p h s S T) :
    rawRecord pairs (retainedVertexEmbedding S T s v)=vertexRecord pairs v := by
  rcases v with (x|x)|(x|x) <;> rfl
 theorem upperRecordLT_correct {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x y : QueryVertex p h s S T) :
    upperRecordLT (vertexRecord pairs x) (vertexRecord pairs y)=
      decide ((retainedMonotoneDiagram pairs S T s).upper x<(retainedMonotoneDiagram pairs S T s).upper y) := by
  have hh := upper_raw pairs (retainedVertexEmbedding S T s x) (retainedVertexEmbedding S T s y)
  rw [rawRecord_retained,rawRecord_retained] at hh
  exact hh
 theorem lowerRecordLT_correct {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x y : QueryVertex p h s S T) :
    lowerRecordLT (vertexRecord pairs x) (vertexRecord pairs y)=
      decide ((retainedMonotoneDiagram pairs S T s).lower x<(retainedMonotoneDiagram pairs S T s).lower y) := by
  have hh := lower_raw pairs (retainedVertexEmbedding S T s x) (retainedVertexEmbedding S T s y)
  rw [rawRecord_retained,rawRecord_retained] at hh
  exact hh
end HiddenCircuits.GraphReduction.Runtime.MonotoneOrder
