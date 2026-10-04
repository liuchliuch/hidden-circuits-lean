import HiddenCircuits.Complexity.GraphVerifier.MatchingCertificates

/-! A unique padded matching witness with an arbitrary sufficient certificate budget. -/
namespace HiddenCircuits.Complexity.GraphVerifier.PaddedMatching
open Matching

def verifyPair (x w : BitString) : Bool :=
  match GraphInput.decode x with
  | none => false
  | some G => if hn : G.1*G.1≤w.length then decide (PaddedPerfect G.2 hn (fun i=>w.get i)) else false

def verifier (s : BitString) : Bool :=
  match unpairBits s with | none => false | some (x,w) => verifyPair x w

theorem verifier_on_rejected (x : BitString) {m : ℕ} (w : Fin m → Bool)
    (hg : GraphInput.decode x=none) : verifier (pairBits x (List.ofFn w))=false := by
  simp [verifier,verifyPair,hg]

theorem verifier_on_decoded (x : BitString) {m : ℕ} (w : Fin m → Bool) (G : GraphInput)
    (hg : GraphInput.decode x=some G) (hm : G.1*G.1≤m) :
    verifier (pairBits x (List.ofFn w))=decide (PaddedPerfect G.2 hm w) := by
  simp [verifier,verifyPair,hg,hm,PaddedPerfect,restrictCertificate,
    ZeroPadded,MatrixGraph.ValidPerfect,MatrixGraph.matchingBit]
  apply and_congr
  · rfl
  · constructor
    · intro ht i hi;exact ht ⟨i.val,by simpa using i.isLt⟩ hi
    · intro ht i hi;exact ht ⟨i.val,by simpa using i.isLt⟩ hi

theorem certificateCount_eq (x : BitString) (m : ℕ)
    (hm : ∀G,GraphInput.decode x=some G → G.1*G.1≤m) :
    certificateCount verifier x m=GraphInput.perfectMatchingProblem x := by
  classical
  unfold certificateCount GraphInput.perfectMatchingProblem
  cases hg : GraphInput.decode x with
  | none =>
    have hf (w : Fin m → Bool) : verifier (pairBits x (List.ofFn w))=false := verifier_on_rejected x w hg
    simp [hf]
  | some G =>
    have hv (w : Fin m → Bool) : verifier (pairBits x (List.ofFn w))=true ↔ PaddedPerfect G.2 (hm G hg) w := by
      rw [verifier_on_decoded x w G hg (hm G hg)];simp
    rw [Fintype.card_congr (Equiv.subtypeEquivRight hv),
      ←Fintype.card_congr (paddedPerfectEquiv G.2 (hm G hg)),←G.2.perfectMatchingCount_eq_certificates]

end HiddenCircuits.Complexity.GraphVerifier.PaddedMatching
