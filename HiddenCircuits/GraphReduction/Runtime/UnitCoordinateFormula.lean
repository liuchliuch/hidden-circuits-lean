import HiddenCircuits.GraphReduction.Runtime.UnitOffsetCounts

/-! The emitted coordinate is an affine signed baseline followed by
two genuine signed descriptor sums. All coordinate order and equality choices
are structural; there is no supplied representation certificate. -/
namespace HiddenCircuits.GraphReduction.Runtime
open UnitInterval

def correctionTrack (second : Bool) (width : ℕ) (x : VertexRecord) : ℕ :=
  if UnitBaseline.mode x=.risePlus ∨ UnitBaseline.mode x=.riseMinus then x.track+1 else
  if UnitBaseline.mode x=.ordinary ∧ second=true ∧ x.track+1<width then x.track+1 else x.track

def unitCorrectionValue (second : Bool) (width : ℕ) (x y : VertexRecord) : ℤ :=
  if y.side && !y.probe && decide (y.layer<x.layer) && decide (y.track=0) then
    cutScore y.cut (correctionTrack second width x) else 0

def unitCoordinate (width height : ℕ) (records : List VertexRecord) (x : VertexRecord) : ℤ :=
  if x.probe then (2*(x.layer:ℤ)+1)*commonLength width height else
    (2*(x.layer:ℤ)+(if x.side then 1 else 0))*commonLength width height+
      offsetBase (scale height) x+
      (records.map (unitCorrectionValue false width x)).sum+
      (records.map (unitCorrectionValue true width x)).sum

lemma unitCorrectionValue_cases (second : Bool) (width : ℕ) (x y : VertexRecord) :
    unitCorrectionValue second width x y=0 ∨ unitCorrectionValue second width x y=1 ∨
      unitCorrectionValue second width x y=-1 := by
  unfold unitCorrectionValue
  split_ifs
  · exact cutScore_cases _ _
  · simp

lemma correction_sum (second : Bool) {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p)
    (s : ℕ) (x : VertexRecord) (hp:0<2*p) :
    ((unitRecords (fun i=>w.get i) S T s).map (unitCorrectionValue second (2*p) x)).sum=
      prefixScore (w.take x.layer) (correctionTrack second (2*p) x) :=
  descriptorScore_unitRecords w S T s x.layer (correctionTrack second (2*p) x) hp

lemma middleProfile_offset_score {p : ℕ} (height layer : ℕ) (w : List (CutPair p))
    (P : CutPair p) (v : Fin (2*p)) :
    offsetBase (scale height) ⟨true,false,layer,v.val,cutCode P⟩+
      prefixScore w (correctionTrack false (2*p) ⟨true,false,layer,v.val,cutCode P⟩)+
      prefixScore w (correctionTrack true (2*p) ⟨true,false,layer,v.val,cutCode P⟩)=
    middleProfile (scale height) (runOutput (initialProfile (2*p) (scale height)) w) P v := by
  cases P with
  | background =>
    simp [middleProfile,ordinaryMiddle_score,offsetBase,UnitBaseline.offset,UnitBaseline.mode,
      cutCode,correctionTrack]
  | leftRise i =>
    by_cases hv:v.val=i.val
    · simp [middleProfile,hv,offsetBase,UnitBaseline.offset,UnitBaseline.mode,cutCode,correctionTrack,
        initial_runOutput_score,nextTrack];ring
    · simp [middleProfile,hv,ordinaryMiddle_score,offsetBase,UnitBaseline.offset,UnitBaseline.mode,
        cutCode,correctionTrack]
  | leftDrop i =>
    by_cases hv:v.val=i.val
    · simp [middleProfile,hv,offsetBase,UnitBaseline.offset,UnitBaseline.mode,cutCode,correctionTrack,
        initial_runOutput_score,firstTrack];ring
    · simp [middleProfile,hv,ordinaryMiddle_score,offsetBase,UnitBaseline.offset,UnitBaseline.mode,
        cutCode,correctionTrack]
  | rightRise i =>
    by_cases hv:v.val=i.val
    · simp [middleProfile,hv,offsetBase,UnitBaseline.offset,UnitBaseline.mode,cutCode,correctionTrack,
        initial_runOutput_score,nextTrack];ring
    · simp [middleProfile,hv,ordinaryMiddle_score,offsetBase,UnitBaseline.offset,UnitBaseline.mode,
        cutCode,correctionTrack]
  | rightDrop i =>
    by_cases hv:v.val=i.val
    · simp [middleProfile,hv,offsetBase,UnitBaseline.offset,UnitBaseline.mode,cutCode,correctionTrack,
        initial_runOutput_score,firstTrack];ring
    · simp [middleProfile,hv,ordinaryMiddle_score,offsetBase,UnitBaseline.offset,UnitBaseline.mode,
        cutCode,correctionTrack]

 theorem unitCoordinate_correct {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p)
    (s : ℕ) (v : UnitQueryVertex p w.length s S T) :
    unitCoordinate (2*p) w.length (unitRecords (fun i=>w.get i) S T s)
      (unitVertexRecord (fun i=>w.get i) v)=unitQueryLeftInteger w v := by
  rcases v with (v|v)|v
  · have hp : 0<2*p := by have := v.val.2.isLt;omega
    simp only [unitCoordinate,unitVertexRecord,Bool.false_eq_true,ite_false,add_zero]
    rw [correction_sum _ _ _ _ _ _ hp,correction_sum _ _ _ _ _ _ hp]
    change _=2*(v.val.1.val:ℤ)*commonLength (2*p) w.length+unitOriginalOffset w (.inl v)
    rw [unitOriginalOffset,layerProfile_even _ _ _ _ (by have := v.val.1.isLt;omega),initial_runOutput_score]
    simp [offsetBase,UnitBaseline.mode,UnitBaseline.offset,correctionTrack];ring
  · have hp : 0<2*p := by have := v.2.isLt;omega
    simp only [unitCoordinate,unitVertexRecord,Bool.false_eq_true,ite_false,ite_true]
    rw [correction_sum _ _ _ _ _ _ hp,correction_sum _ _ _ _ _ _ hp]
    change _=(2*(v.1.val:ℤ)+1)*commonLength (2*p) w.length+unitOriginalOffset w (.inr v)
    rw [unitOriginalOffset,layerProfile_odd _ _ _ _ v.1.isLt]
    have he:=middleProfile_offset_score w.length v.1.val (w.take v.1.val) (w.get v.1) v.2
    simpa only [add_assoc] using congrArg (fun z=>(2*(v.1.val:ℤ)+1)*commonLength (2*p) w.length+z) he
  · rfl
end HiddenCircuits.GraphReduction.Runtime
