import HiddenCircuits.Complexity.EvalValidation.PairAtom
import HiddenCircuits.Complexity.EncodingSoundness

namespace HiddenCircuits.Complexity.EvalValidation.WordAtom
open GraphVerifier
set_option maxHeartbeats 800000
def valid (xs width : BitString) : Bool :=
  (parse xs).ok && Index.valid (parse xs).right width && decide ((parse xs).left.length=2)

lemma kind_isSome (xs : BitString) : (decodeKind xs).isSome=decide (xs.length=2) := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs =>
      cases xs <;> cases a <;> cases b <;> rfl
lemma valid_decode (p : ℕ) (xs width : BitString) (hw : width.length=2*p) :
    valid xs width=(decodeLetter (2*p) xs).isSome := by
  unfold valid decodeLetter
  rw [parse_spec]
  cases hok:(parse xs).ok
  · simp [hok]
  · simp only [hok,if_true,Bool.true_and]
    cases hk:decodeKind (parse xs).left with
    | none =>
      have h:=kind_isSome (parse xs).left
      rw [hk] at h
      simp only [Option.isSome_none] at h
      simp [←h]
    | some k =>
      have h:=kind_isSome (parse xs).left
      rw [hk] at h
      simp only [Option.isSome_some] at h
      simp only [←h,Bool.and_true]
      have he:=PairAtom.index_isSome p (parse xs).right width hw
      rw [←he]
      unfold decodePairIndex
      split_ifs <;> rfl

end HiddenCircuits.Complexity.EvalValidation.WordAtom
