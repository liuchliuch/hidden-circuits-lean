import HiddenCircuits.Complexity.GraphVerifier.MatchingRuntimeSemantics
import HiddenCircuits.Complexity.GraphVerifier.GuardSemantics

/-! Exact squared-witness guard and flat matching verifier semantics. -/
namespace HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
open Runtime

 def guardValue (xs : BitString) : Bool :=
  let x := (parse xs).left
  let w := (parse xs).right
  let h := (parse x).left
  let p := (parse x).right
  (parse xs).ok && (parse x).ok && h.all id && decide (w.length=x.length*x.length) &&
    decide (p.length=h.length*h.length) && (w.drop (h.length*h.length)).all (fun b => !b)

 theorem guard_implies_lengths (xs : BitString) (hg : guardValue xs=true) :
    (parse (parse xs).left).right.length=(parse (parse xs).left).left.length*(parse (parse xs).left).left.length ∧
      (parse (parse xs).left).left.length*(parse (parse xs).left).left.length ≤ (parse xs).right.length := by
  simp only [guardValue,Bool.and_eq_true,decide_eq_true_eq] at hg
  have hlen : (parse xs).right.length=(parse xs).left.length*(parse xs).left.length := by tauto
  have hn := (parse_lengths (parse xs).left).1
  exact ⟨by tauto,hlen ▸ Nat.mul_le_mul hn hn⟩

 theorem matching_edges_iff {n : ℕ} (p w : BitString) (G : MatrixGraph n)
    (he : ∀ i j, G.edge i j=flatEdge n p i j) :
    (scanPairs n p w=true ∧ RowsOne n w) ↔ G.ValidPerfect (fun i => bitAt w i.val) := by
  rw [scanPairs_iff]
  constructor
  · rintro ⟨⟨_,_,hs,hi⟩,hr⟩
    refine ⟨hr,hs,?_⟩
    intro i j hj
    rw [he]
    exact hi i j hj
  · rintro ⟨hr,hs,hi⟩
    refine ⟨⟨?_,?_,hs,?_⟩,hr⟩
    · intro i j;rw [←he,←he,G.symm]
    · intro i;rw [←he,G.loopless]
    · intro i j hj;rw [←he];exact hi i j hj

 def flatVerifyPair (x w : BitString) : Bool :=
  let r := parse x
  r.ok && r.left.all id && decide (w.length=x.length*x.length) &&
    decide (r.right.length=r.left.length*r.left.length) &&
    (w.drop (r.left.length*r.left.length)).all (fun b => !b) &&
    scanPairs r.left.length r.right w && decide (RowsOne r.left.length w)

 theorem verifyPair_eq_flat (x w : BitString) : Matching.verifyPair x w=flatVerifyPair x w := by
  unfold Matching.verifyPair GraphInput.decode flatVerifyPair
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
          intro hp;rw [ofBits_valid _ _ hp] at hg;cases hg
        apply Bool.eq_iff_iff.mpr
        simp only [hg,ha,Bool.true_and,Bool.false_eq_true,Bool.and_eq_true,decide_eq_true_eq]
        constructor
        · intro h;cases h
        · intro h
          have hs := (scanPairs_iff _ _ _).mp h.1.2
          exact False.elim (hp ⟨h.1.1.1.2,hs.1,hs.2.1⟩)
      | some G =>
        have hp := ofBits_some_edges _ _ G hg
        simp only [hg,Option.map_some,ha,Bool.true_and]
        by_cases hw : w.length=x.length*x.length
        · have hn : (parse x).left.length*(parse x).left.length ≤ w.length := by
            rw [hw];exact Nat.mul_le_mul (parse_lengths x).1 (parse_lengths x).1
          rw [dif_pos hw,dif_pos hn]
          have hs := matching_edges_iff (parse x).right w G (fun i j => congrFun (congrFun hp.2 i) j)
          have hz := zeroPadded_iff_drop w ((parse x).left.length*(parse x).left.length)
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq,Bool.and_eq_true,hw,decide_true,Bool.true_and,hp.1.1,
            Matching.PaddedPerfect]
          have hf : restrictCertificate hn (fun i => w.get i)=(fun i => bitAt w i.val) := by
            funext i
            exact (bitAt_get w i.val (lt_of_lt_of_le i.isLt hn)).symm
          rw [hf,←hs,hz]
          tauto
        · simp [hw]
    · have ha : (parse x).left.all id=false := by
        apply Bool.eq_false_iff.mpr
        intro h;exact hh ((header_all_true _).mp h)
      simp [hh,ha]

 theorem verifier_eq_guard_scan (xs : BitString) : Matching.verifier xs=
    (guardValue xs && scanPairs (parse (parse xs).left).left.length
      (parse (parse xs).left).right (parse xs).right &&
      decide (RowsOne (parse (parse xs).left).left.length (parse xs).right)) := by
  unfold Matching.verifier
  rw [parse_spec]
  cases h : (parse xs).ok <;> simp [h,verifyPair_eq_flat,flatVerifyPair,guardValue,Bool.and_assoc]

end HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
