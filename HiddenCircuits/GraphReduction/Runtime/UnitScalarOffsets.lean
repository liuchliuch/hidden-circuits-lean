import HiddenCircuits.GraphReduction.Runtime.UnitBaselineCode
import HiddenCircuits.GraphReduction.UnitIntervalLayerProfiles

/-! Express the paper's recursive profiles as signed prefix sums.
The signs of right-rise and left-drop are negative. Integer division in an
ordinary midpoint is exact because every profile displacement is even. -/
namespace HiddenCircuits.GraphReduction.Runtime
open UnitInterval

def cutScore (c : CutCode) (track : ℕ) : ℤ :=
  if (c.leftRise && decide (track=c.index+1)) || (c.rightDrop && decide (track=c.index)) then 1 else
  if (c.rightRise && decide (track=c.index+1)) || (c.leftDrop && decide (track=c.index)) then -1 else 0

lemma cutScore_cases (c : CutCode) (track : ℕ) :
    cutScore c track=0 ∨ cutScore c track=1 ∨ cutScore c track=-1 := by
  unfold cutScore;split_ifs <;> simp
lemma cutScore_abs (c : CutCode) (track : ℕ) : |cutScore c track|≤1 := by
  rcases cutScore_cases c track with h|h|h <;> rw [h] <;> norm_num

def prefixScore {p : ℕ} (w : List (CutPair p)) (track : ℕ) : ℤ :=
  (w.map (fun P=>cutScore (cutCode P) track)).sum

lemma outputProfile_score {p : ℕ} (a : Profile (2*p)) (P : CutPair p) (v : Fin (2*p)) :
    outputProfile a P v=a v+2*cutScore (cutCode P) v.val := by
  cases P <;> simp [outputProfile,cutScore,cutCode] <;> split_ifs <;> omega

lemma runOutput_score {p : ℕ} (a : Profile (2*p)) (w : List (CutPair p)) (v : Fin (2*p)) :
    runOutput a w v=a v+2*prefixScore w v.val := by
  induction w generalizing a with
  | nil => simp [runOutput,prefixScore]
  | cons P w ih =>
    rw [runOutput,ih,outputProfile_score]
    simp only [prefixScore,List.map_cons,List.sum_cons]
    ring

lemma initial_runOutput_score {p : ℕ} (height : ℕ) (w : List (CutPair p)) (v : Fin (2*p)) :
    runOutput (initialProfile (2*p) (scale height)) w v=
      (v.val+1)*scale height+2*prefixScore w v.val := by
  rw [runOutput_score];rfl

lemma midpoint_score (height track : ℕ) (a b : ℤ) :
    (((track:ℤ)+1)*scale height+2*a+(((track:ℤ)+2)*scale height+2*b))/2=
      ((track:ℤ)+1)*scale height+scale height/2+a+b := by
  have hδ : scale height=2*(500*((height:ℤ)+1)) := by unfold scale;ring
  rw [hδ]
  have he : ((track:ℤ)+1)*(2*(500*((height:ℤ)+1)))+2*a+
      (((track:ℤ)+2)*(2*(500*((height:ℤ)+1)))+2*b)=
      2*(((track:ℤ)+1)*(2*(500*((height:ℤ)+1)))+500*((height:ℤ)+1)+a+b) := by ring
  rw [he]
  simp

lemma ordinaryMiddle_score {p : ℕ} (height : ℕ) (w : List (CutPair p)) (v : Fin (2*p)) :
    ordinaryMiddle (scale height) (runOutput (initialProfile (2*p) (scale height)) w) v=
      (v.val+1)*scale height+scale height/2+prefixScore w v.val+
        prefixScore w (if v.val+1<2*p then v.val+1 else v.val) := by
  unfold ordinaryMiddle
  split_ifs with hv
  · rw [initial_runOutput_score,initial_runOutput_score]
    convert midpoint_score height v.val (prefixScore w v.val) (prefixScore w (v.val+1)) using 1 <;>
      push_cast <;> ring
  · rw [initial_runOutput_score];ring
end HiddenCircuits.GraphReduction.Runtime
