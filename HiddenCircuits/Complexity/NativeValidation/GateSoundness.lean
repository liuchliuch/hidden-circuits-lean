import HiddenCircuits.Complexity.NativeValidation.Gate
import HiddenCircuits.Complexity.EncodingSoundness

namespace HiddenCircuits.Complexity.NativeValidation.Gate
open EvalValidation GraphVerifier Circuit Circuit.Runtime
set_option maxHeartbeats 1000000
lemma evaluate_pair (deltaMode : Bool) (ks tag is width : BitString) :
    evaluate deltaMode ks.length tag (pairBits ks is) width=leafValue deltaMode (tag++ks) is width := by
  induction ks generalizing tag with
  | nil=>simp [pairBits,evaluate]
  | cons b ks ih=>simp only [List.length_cons,pairBits,evaluate,ih,List.append_assoc,List.singleton_append]
lemma evaluate_witness (deltaMode : Bool) (n : ℕ) (tag xs width : BitString)
    (h:evaluate deltaMode n tag xs width=true) :
    ∃ks is,ks.length=n ∧ xs=pairBits ks is ∧ leafValue deltaMode (tag++ks) is width=true := by
  induction n generalizing tag xs with
  | zero=>
    cases xs with
    | nil=>simp [evaluate] at h
    | cons b xs=>
      cases b
      · exact ⟨[],xs,rfl,rfl,by simpa only [List.append_nil] using h⟩
      · simp [evaluate] at h
  | succ n ih=>
    cases xs with
    | nil=>simp [evaluate] at h
    | cons a xs=>
      cases a
      · simp [evaluate] at h
      · cases xs with
        | nil=>simp [evaluate] at h
        | cons b xs=>
          obtain ⟨ks,is,hl,hx,hv⟩:=ih (tag++[b]) xs h
          refine ⟨b::ks,is,by simp [hl],?_,?_⟩
          · simp only [pairBits,hx]
          · simpa only [List.append_assoc,List.singleton_append] using hv
lemma tag_length {tag : BitString} {t : GateTag} (h:decodeTag tag=some t) : tag.length=4 := by
  cases tag with
  | nil=>simp [decodeTag] at h
  | cons a tag=>
    cases tag with
    | nil=>cases a <;> simp [decodeTag] at h
    | cons b tag=>
      cases tag with
      | nil=>cases a <;> cases b <;> simp [decodeTag] at h
      | cons c tag=>
        cases tag with
        | nil=>cases a <;> cases b <;> cases c <;> simp [decodeTag] at h
        | cons d tag=>
          cases tag with
          | nil=>rfl
          | cons e tag=>cases a <;> cases b <;> cases c <;> cases d <;> simp [decodeTag] at h
lemma leaf_tag_length (deltaMode : Bool) (tag xs width : BitString) (h:leafValue deltaMode tag xs width=true) : tag.length=4 := by
  unfold leafValue at h
  cases ht:decodeTag tag with
  | none=>simp [ht] at h
  | some t=>exact tag_length ht
lemma valid_parse (deltaMode : Bool) (xs width : BitString) :
    valid deltaMode xs width=((parse xs).ok && leafValue deltaMode (parse xs).left (parse xs).right width) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    obtain ⟨ks,is,hl,rfl,hv⟩:=evaluate_witness deltaMode 4 [] xs width h
    simpa [parse_pair] using hv
  · intro h
    have hh:(parse xs).ok=true ∧ leafValue deltaMode (parse xs).left (parse xs).right width=true := by simpa only [Bool.and_eq_true] using h
    obtain ⟨hok,hv⟩:=hh
    have hu:unpairBits xs=some ((parse xs).left,(parse xs).right):=by rw [parse_spec,hok];rfl
    have he:=pairBits_of_unpair xs _ _ hu
    have hl:=leaf_tag_length deltaMode (parse xs).left (parse xs).right width hv
    have hh:=evaluate_pair deltaMode (parse xs).left [] (parse xs).right width
    rw [hl,he] at hh
    simpa only [valid,List.nil_append] using hh.trans hv

def decoded (deltaMode : Bool) (n : ℕ) (xs : BitString) : Bool :=
  match decodeGate n xs with
  | none=>false
  | some g=>if deltaMode then (decodeDeltaGate g).isSome else true
lemma gateFromTag_delta (n : ℕ) (t : GateTag) (b : ℕ) (h:b+t.width≤n) :
    (decodeDeltaGate (gateFromTag n t b h)).isSome= !decide (t=.controlledSign) := by cases t <;> rfl
lemma unary_all (xs : BitString) : xs.all id=true ↔ xs=List.replicate xs.length true := by
  exact GraphVerifier.header_all_true xs
lemma valid_decode (deltaMode : Bool) (n : ℕ) (xs width : BitString) (hw:width.length=n) :
    valid deltaMode xs width=decoded deltaMode n xs := by
  rw [valid_parse]
  unfold leafValue decoded decodeGate
  rw [parse_spec]
  cases hok:(parse xs).ok
  · simp [hok]
  · simp only [hok,if_true,Bool.true_and]
    cases ht:decodeTag (parse xs).left with
    | none=>rfl
    | some t=>
      simp only []
      by_cases hb:(parse xs).right.length+t.width≤n
      · simp only [dif_pos hb]
        by_cases hu:(parse xs).right=List.replicate (parse xs).right.length true
        · have ha:(parse xs).right.all id=true:=(unary_all _).mpr hu
          simp only [if_pos hu,gateFromTag_delta,ha,hw,hb,decide_true,Bool.true_and,Bool.and_true]
          cases deltaMode <;> simp
        · have ha:(parse xs).right.all id=false:=Bool.eq_false_iff.mpr (fun h=>hu ((unary_all _).mp h))
          simp only [if_neg hu,ha,Bool.false_and]
          split_ifs <;> first | contradiction | rfl
      · simp only [dif_neg hb,hw,hb,decide_false,Bool.and_false]
        split_ifs <;> first | contradiction | rfl
end HiddenCircuits.Complexity.NativeValidation.Gate
