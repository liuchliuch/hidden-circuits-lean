import HiddenCircuits.Complexity.EncodingSoundness

/-! Canonical fixed-polynomial-length independent-set certificates. Unused
certificate positions are forced false, so padding has exactly one extension. -/
namespace HiddenCircuits.Complexity.GraphVerifier

variable {n L : ℕ}

def padCertificate (h : n ≤ L) (w : Fin n → Bool) : Fin L → Bool :=
  fun i => if hi : i.val < n then w ⟨i.val,hi⟩ else false

def restrictCertificate (h : n ≤ L) (w : Fin L → Bool) : Fin n → Bool :=
  fun i => w (i.castLE h)

def ZeroPadded (w : Fin L → Bool) (n : ℕ) : Prop := ∀ i, n ≤ i.val → w i = false

instance (w : Fin L → Bool) (n : ℕ) : Decidable (ZeroPadded w n) :=
  inferInstanceAs (Decidable (∀ i : Fin L, n ≤ i.val → w i = false))

@[simp] theorem restrict_padCertificate (h : n ≤ L) (w : Fin n → Bool) :
    restrictCertificate h (padCertificate h w) = w := by
  funext i;simp [restrictCertificate,padCertificate,i.isLt]

theorem padCertificate_zeroPadded (h : n ≤ L) (w : Fin n → Bool) : ZeroPadded (padCertificate h w) n := by
  intro i hi;simp [padCertificate,show ¬i.val<n by omega]

theorem pad_restrictCertificate (h : n ≤ L) (w : Fin L → Bool) (hw : ZeroPadded w n) :
    padCertificate h (restrictCertificate h w) = w := by
  funext i
  by_cases hi : i.val < n
  · simp only [padCertificate,dif_pos hi,restrictCertificate]
    congr 1
  · simp [padCertificate,hi,hw i (by omega)]

def PaddedIndependent (G : MatrixGraph n) (h : n ≤ L) (w : Fin L → Bool) : Prop :=
  G.ValidIndependent (restrictCertificate h w) ∧ ZeroPadded w n

instance (G : MatrixGraph n) (h : n ≤ L) (w : Fin L → Bool) : Decidable (PaddedIndependent G h w) :=
  inferInstanceAs (Decidable (G.ValidIndependent (restrictCertificate h w) ∧ ZeroPadded w n))

/-- Exactly one longer certificate represents each independent set. -/
def paddedIndependentEquiv (G : MatrixGraph n) (h : n ≤ L) :
    G.IndependentCertificate ≃ {w : Fin L → Bool // PaddedIndependent G h w} where
  toFun w := ⟨padCertificate h w.val,by
    exact ⟨by simpa using w.property,padCertificate_zeroPadded h w.val⟩⟩
  invFun w := ⟨restrictCertificate h w.val,w.property.1⟩
  left_inv w := Subtype.ext (restrict_padCertificate h w.val)
  right_inv w := Subtype.ext (pad_restrictCertificate h w.val w.property.2)

def verifyPair (x w : BitString) : Bool :=
  match GraphInput.decode x with
  | none => false
  | some G =>
    if hw : w.length = x.length then
      if hn : G.1 ≤ w.length then
        decide (PaddedIndependent G.2 hn (fun i => w.get i))
      else false
    else false

def verifier (s : BitString) : Bool :=
  match unpairBits s with
  | none => false
  | some (x,w) => verifyPair x w

theorem verifier_on_rejected (x : BitString) (w : Fin x.length → Bool)
    (hg : GraphInput.decode x = none) : verifier (pairBits x (List.ofFn w)) = false := by
  simp [verifier,verifyPair,hg]

theorem verifier_on_decoded (x : BitString) (w : Fin x.length → Bool) (G : GraphInput)
    (hg : GraphInput.decode x = some G) : verifier (pairBits x (List.ofFn w)) =
      decide (PaddedIndependent G.2 (GraphInput.decode_vertices_bound hg) w) := by
  simp [verifier,verifyPair,hg,GraphInput.decode_vertices_bound hg,
    PaddedIndependent,restrictCertificate,ZeroPadded,MatrixGraph.ValidIndependent]
  apply congrArg₂ Bool.and
  · rfl
  · congr 1
    apply propext
    constructor
    · intro h i hi
      exact h ⟨i.val,by simpa using i.isLt⟩ hi
    · intro h i hi
      exact h ⟨i.val,by simpa using i.isLt⟩ hi

/-- The actual fixed witness length is the input bit length, including malformed
strings. Valid graphs count each independent set once; invalid graphs count zero. -/
theorem certificateCount_eq (x : BitString) :
    certificateCount verifier x x.length = GraphInput.independentSetProblem x := by
  classical
  unfold certificateCount GraphInput.independentSetProblem
  cases hg : GraphInput.decode x with
  | none =>
    have hf : ∀ w : Fin x.length → Bool, verifier (pairBits x (List.ofFn w)) = false := by
      intro w;exact verifier_on_rejected x w hg
    simp [hf]
  | some G =>
    let h := GraphInput.decode_vertices_bound hg
    have hv (w : Fin x.length → Bool) :
        verifier (pairBits x (List.ofFn w)) = true ↔ PaddedIndependent G.2 h w := by
      rw [verifier_on_decoded x w G hg];simp [h]
    let e : {w : Fin x.length → Bool // verifier (pairBits x (List.ofFn w)) = true} ≃
        {w : Fin x.length → Bool // PaddedIndependent G.2 h w} :=
      Equiv.subtypeEquivRight hv
    rw [Fintype.card_congr e,← Fintype.card_congr (paddedIndependentEquiv G.2 h),
      ← G.2.independentCount_eq_certificates]

end HiddenCircuits.Complexity.GraphVerifier
