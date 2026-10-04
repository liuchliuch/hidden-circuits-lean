import HiddenCircuits.Complexity.GraphVerifier.PayloadSemantics
import HiddenCircuits.Complexity.GraphVerifier.UnpairProgram

/-! A flat-bit presentation of the exact canonical independent-set verifier. -/
namespace HiddenCircuits.Complexity.GraphVerifier

 theorem header_all_true (xs : BitString) : xs.all id=true ↔ xs=List.replicate xs.length true := by
  simp only [List.all_eq_true,List.eq_replicate_length,id_eq]

/-- Every test is a flat list check or bounded double loop over actual input bits. -/
def flatVerifyPair (x w : BitString) : Bool :=
  let r := parse x
  r.ok && r.left.all id && decide (w.length=x.length) &&
    decide (ValidPayload r.left.length r.right) &&
    decide (ValidSelectedPairs r.left.length r.right w) && (w.drop r.left.length).all (fun b => !b)

theorem verifyPair_eq_flat (x w : BitString) : verifyPair x w=flatVerifyPair x w := by
  unfold verifyPair GraphInput.decode flatVerifyPair
  rw [parse_spec]
  cases hok : (parse x).ok with
  | false => simp [hok]
  | true =>
    simp only [hok,if_true,Option.map_some,Bool.true_and]
    by_cases hh : (parse x).left=List.replicate (parse x).left.length true
    · have ha : (parse x).left.all id=true := (header_all_true _).mpr hh
      rw [if_pos hh]
      cases hg : MatrixGraph.ofBits (parse x).left.length (parse x).right with
      | none =>
        have hp : ¬ValidPayload (parse x).left.length (parse x).right := by
          intro hp
          rw [ofBits_valid _ _ hp] at hg
          cases hg
        simp [ha,hg,hp]
      | some G =>
        have hp := ofBits_some_edges _ _ G hg
        have hx : unpairBits x=some ((parse x).left,(parse x).right) := by rw [parse_spec,hok]; rfl
        have hl := unpairBits_length hx
        simp only [hg,Option.map_some,ha,Bool.true_and]
        by_cases hw : w.length=x.length
        · have hn : (parse x).left.length ≤ w.length := by omega
          rw [dif_pos hw,dif_pos hn]
          have hs := selectedPairs_iff (parse x).right w G hp.2 hn
          have hz := zeroPadded_iff_drop w (parse x).left.length
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq,Bool.and_eq_true,hw,decide_true,Bool.true_and,hp.1,
            PaddedIndependent]
          exact and_congr hs.symm hz
        · simp [hw]
    · have ha : (parse x).left.all id=false := by
        apply Bool.eq_false_iff.mpr
        intro h
        exact hh ((header_all_true _).mp h)
      simp [hh,ha]

/-- Malformed pairing and malformed graph inputs are handled by the same flat routine. -/
def flatVerifier (xs : BitString) : Bool :=
  (parse xs).ok && flatVerifyPair (parse xs).left (parse xs).right

theorem verifier_eq_flat (xs : BitString) : verifier xs=flatVerifier xs := by
  unfold verifier flatVerifier
  rw [parse_spec]
  cases h : (parse xs).ok <;> simp [h,verifyPair_eq_flat]

end HiddenCircuits.Complexity.GraphVerifier
