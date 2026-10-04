import HiddenCircuits.Complexity.GraphVerifier.Certificates
import HiddenCircuits.PerfectPartners

/-! Unique row-major perfect-matching certificates for actual graph subgraphs. -/
namespace HiddenCircuits.Complexity
namespace MatrixGraph
variable {n : ℕ}

def matchingBit (w : Fin (n*n) → Bool) (i j : Fin n) : Bool := w (finProdFinEquiv (i,j))

def ValidPerfect (G : MatrixGraph n) (w : Fin (n*n) → Bool) : Prop :=
  (∀ i, ∃! j, matchingBit w i j=true) ∧
  (∀ i j, matchingBit w i j=matchingBit w j i) ∧
  (∀ i j, matchingBit w i j=true → G.edge i j=true)

instance (G : MatrixGraph n) (w : Fin (n*n) → Bool) : Decidable (G.ValidPerfect w) := by
  unfold ValidPerfect ExistsUnique
  infer_instance

abbrev PerfectCertificate (G : MatrixGraph n) := {w : Fin (n*n) → Bool // G.ValidPerfect w}

noncomputable def PerfectCertificate.partner {G : MatrixGraph n} (w : G.PerfectCertificate) (i : Fin n) : Fin n :=
  (w.property.1 i).exists.choose

theorem PerfectCertificate.partner_bit {G : MatrixGraph n} (w : G.PerfectCertificate) (i : Fin n) :
    matchingBit w.val i (w.partner i)=true := (w.property.1 i).exists.choose_spec

theorem PerfectCertificate.partner_eq_iff {G : MatrixGraph n} (w : G.PerfectCertificate) (i j : Fin n) :
    w.partner i=j ↔ matchingBit w.val i j=true := by
  constructor
  · rintro rfl;exact w.partner_bit i
  · intro h;exact ExistsUnique.unique (w.property.1 i) (w.partner_bit i) h

noncomputable def PerfectCertificate.toPartner {G : MatrixGraph n} (w : G.PerfectCertificate) : PerfectPartner G.graph :=
  ⟨w.partner,by
    constructor
    · intro i
      apply (w.partner_eq_iff _ _).mpr
      rw [←w.property.2.1]
      exact w.partner_bit i
    · intro i
      exact w.property.2.2 i (w.partner i) (w.partner_bit i)⟩

noncomputable def certificateOfPartner (G : MatrixGraph n) (p : PerfectPartner G.graph) : G.PerfectCertificate := by
  classical
  refine ⟨fun q => decide (p.val (finProdFinEquiv.symm q).1=(finProdFinEquiv.symm q).2),?_,?_,?_⟩
  · intro i
    refine ⟨p.val i,by simp [matchingBit],?_⟩
    intro j hj
    exact (show p.val i=j by simpa [matchingBit] using hj).symm
  · intro i j
    simp only [matchingBit,Equiv.symm_apply_apply]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro rfl;exact p.property.1 i
    · rintro h
      rw [←h,p.property.1]
  · intro i j hj
    have hh : p.val i=j := by simpa [matchingBit] using hj
    rw [←hh]
    exact p.property.2 i

theorem certificateOfPartner_bit (G : MatrixGraph n) (p : PerfectPartner G.graph) (i j : Fin n) :
    matchingBit (certificateOfPartner G p).val i j=decide (p.val i=j) := by
  change decide (p.val (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1=
    (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2)=_
  rw [Equiv.symm_apply_apply]

noncomputable def perfectCertificateEquiv (G : MatrixGraph n) : G.PerfectCertificate ≃ PerfectPartner G.graph where
  toFun := PerfectCertificate.toPartner
  invFun := certificateOfPartner G
  left_inv w := by
    apply Subtype.ext
    funext q
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective q
    change matchingBit (certificateOfPartner G w.toPartner).val i j=matchingBit w.val i j
    rw [certificateOfPartner_bit]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact w.partner_eq_iff i j
  right_inv p := by
    apply Subtype.ext
    funext i
    apply ((certificateOfPartner G p).partner_eq_iff i (p.val i)).mpr
    rw [certificateOfPartner_bit]
    simp

theorem perfectMatchingCount_eq_certificates (G : MatrixGraph n) :
    HiddenCircuits.perfectMatchingCount G.graph=Fintype.card G.PerfectCertificate := by
  rw [perfectMatchingCount_eq_partners]
  exact (Fintype.card_congr (perfectCertificateEquiv G)).symm

end MatrixGraph

namespace GraphInput
noncomputable def perfectMatchingProblem (x : BitString) : ℕ :=
  match decode x with | none => 0 | some G => HiddenCircuits.perfectMatchingCount G.2.graph
end GraphInput

namespace GraphVerifier.Matching
open GraphVerifier
variable {n L : ℕ}

def PaddedPerfect (G : MatrixGraph n) (h : n*n≤L) (w : Fin L → Bool) : Prop :=
  G.ValidPerfect (restrictCertificate h w) ∧ ZeroPadded w (n*n)
instance (G : MatrixGraph n) (h : n*n≤L) (w : Fin L → Bool) : Decidable (PaddedPerfect G h w) :=
  inferInstanceAs (Decidable (G.ValidPerfect (restrictCertificate h w) ∧ ZeroPadded w (n*n)))

def paddedPerfectEquiv (G : MatrixGraph n) (h : n*n≤L) :
    G.PerfectCertificate ≃ {w : Fin L → Bool // PaddedPerfect G h w} where
  toFun w := ⟨padCertificate h w.val,⟨by simpa using w.property,padCertificate_zeroPadded h w.val⟩⟩
  invFun w := ⟨restrictCertificate h w.val,w.property.1⟩
  left_inv w := Subtype.ext (restrict_padCertificate h w.val)
  right_inv w := Subtype.ext (pad_restrictCertificate h w.val w.property.2)

def verifyPair (x w : BitString) : Bool :=
  match GraphInput.decode x with
  | none => false
  | some G =>
    if hw : w.length=x.length*x.length then
      if hn : G.1*G.1≤w.length then decide (PaddedPerfect G.2 hn (fun i => w.get i)) else false
    else false

def verifier (s : BitString) : Bool :=
  match unpairBits s with | none => false | some (x,w) => verifyPair x w

theorem decode_square_bound {x : BitString} {G : GraphInput} (hg : GraphInput.decode x=some G) :
    G.1*G.1≤x.length*x.length := Nat.mul_self_le_mul_self (GraphInput.decode_vertices_bound hg)

theorem verifier_on_rejected (x : BitString) (w : Fin (x.length*x.length) → Bool)
    (hg : GraphInput.decode x=none) : verifier (pairBits x (List.ofFn w))=false := by
  simp [verifier,verifyPair,hg]

theorem verifier_on_decoded (x : BitString) (w : Fin (x.length*x.length) → Bool) (G : GraphInput)
    (hg : GraphInput.decode x=some G) : verifier (pairBits x (List.ofFn w))=
      decide (PaddedPerfect G.2 (decode_square_bound hg) w) := by
  simp [verifier,verifyPair,hg,decode_square_bound hg,PaddedPerfect,restrictCertificate,
    ZeroPadded,MatrixGraph.ValidPerfect,MatrixGraph.matchingBit]
  apply and_congr
  · rfl
  · constructor
    · intro ht i hi
      exact ht ⟨i.val,by simpa using i.isLt⟩ hi
    · intro ht i hi
      exact ht ⟨i.val,by simpa using i.isLt⟩ hi

 theorem certificateCount_eq (x : BitString) :
    certificateCount verifier x (x.length*x.length)=GraphInput.perfectMatchingProblem x := by
  classical
  unfold certificateCount GraphInput.perfectMatchingProblem
  cases hg : GraphInput.decode x with
  | none =>
    have hf (w : Fin (x.length*x.length) → Bool) : verifier (pairBits x (List.ofFn w))=false :=
      verifier_on_rejected x w hg
    simp [hf]
  | some G =>
    let h := decode_square_bound hg
    have hv (w : Fin (x.length*x.length) → Bool) :
        verifier (pairBits x (List.ofFn w))=true ↔ PaddedPerfect G.2 h w := by
      rw [verifier_on_decoded x w G hg];simp [h]
    let e := Equiv.subtypeEquivRight hv
    rw [Fintype.card_congr e,←Fintype.card_congr (paddedPerfectEquiv G.2 h),
      ←G.2.perfectMatchingCount_eq_certificates]

end GraphVerifier.Matching
end HiddenCircuits.Complexity
