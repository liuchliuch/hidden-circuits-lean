import HiddenCircuits.LayeredBoundary
import HiddenCircuits.DH.PartialPairs

/-! Exact first-cut decomposition of matchings in the actual layered graph. -/
namespace HiddenCircuits.Layered
open HiddenCircuits.DH

/-- Restrict an optional vertex to the first layer's actual track label. -/
def decodeAcross {p l : ℕ} (o : Option (Vertices p l)) : Option (Fin (2*p)) :=
  o.bind (firstDecode p l)

 theorem decodeAcross_some {p l : ℕ} (o : Option (Vertices p l)) (x : Fin (2*p)) :
    decodeAcross o = some x ↔ o = some (first p l x) := by
  cases o <;> simp [decodeAcross,firstDecode_some]

 theorem encode_decodeAcross {p l : ℕ} (o : Option (Vertices p l))
    (h : ∀ v, o = some v → ∃ y, first p l y = v) :
    (decodeAcross o).map (first p l) = o := by
  cases ho : o with
  | none => rfl
  | some v =>
    obtain ⟨y,rfl⟩ := h v ho
    simp only [decodeAcross,Option.bind_some,firstDecode_first,Option.map_some]

/-- Independent tail matching and literal cross-track partial bijection. -/
structure CutData {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p)) where
  tail : EncodedMatching (graph w)
  pairs : PartialPairs (Fin (2*p)) (Fin (2*p))
  valid : ∀ x y, pairs.left x = some y → tail.val (first p w.length y) = none ∧ R x y = true

namespace CutData
variable {p : ℕ} {R : UnweightedCut p} {w : List (UnweightedCut p)}

@[ext] theorem ext {d e : CutData R w} (ht : d.tail=e.tail) (hp : d.pairs=e.pairs) : d=e := by
  cases d
  cases e
  simp_all

/-- Assemble the actual arbitrary-join decomposition from track-level crossing data. -/
def toJoinData (d : CutData R w) :
    JoinData (⊥ : SimpleGraph (Fin (2*p))) (graph w)
      (fun x v => ∃ y, first p w.length y = v ∧ R x y = true) where
  left := emptyMatching _
  right := d.tail
  acrossLeft x := (d.pairs.left x).map (first p w.length)
  acrossRight v := (firstDecode p w.length v).bind d.pairs.right
  across_symm x v := by
    simp only [Option.map_eq_some_iff,Option.bind_eq_some_iff]
    constructor
    · rintro ⟨y,hy,hv⟩
      exact ⟨y,(firstDecode_some p w.length v y).mpr hv.symm,(d.pairs.symm x y).mp hy⟩
    · rintro ⟨y,hy,hx⟩
      exact ⟨y,(d.pairs.symm x y).mpr hx,((firstDecode_some p w.length v y).mp hy).symm⟩
  across_valid x v h := by
    obtain ⟨y,hy,rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl,(d.valid x y hy).1,y,rfl,(d.valid x y hy).2⟩

/-- The union of the chosen cut edges and tail edges is a genuine graph matching. -/
def matching (d : CutData R w) : EncodedMatching (graph (R::w)) := d.toJoinData.matching

end CutData

/-- Read off the tail matching and the concrete crossing pairs of any layered matching. -/
def cutDataFromJoin {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p))
    (d : JoinData (⊥ : SimpleGraph (Fin (2*p))) (graph w)
      (fun x v => ∃ y, first p w.length y = v ∧ R x y = true)) : CutData R w where
  tail := d.right
  pairs := {
    left := fun x => decodeAcross (d.acrossLeft x)
    right := fun y => d.acrossRight (first p w.length y)
    symm := by
      intro x y
      rw [decodeAcross_some]
      exact d.across_symm x (first p w.length y) }
  valid := by
    intro x y h
    have hh := d.across_valid x (first p w.length y) ((decodeAcross_some _ _).mp h)
    obtain ⟨z,hz,hr⟩ := hh.2.2
    have he : z=y := first_injective p w.length hz
    subst z
    exact ⟨hh.2.1,hr⟩

 theorem CutData.toJoin_fromJoin {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p))
    (d : JoinData (⊥ : SimpleGraph (Fin (2*p))) (graph w)
      (fun x v => ∃ y, first p w.length y = v ∧ R x y = true)) :
    (cutDataFromJoin R w d).toJoinData = d := by
  apply JoinData.ext
  · apply Subtype.ext
    funext x
    exact (matching_bot_none d.left x).symm
  · rfl
  · funext x
    exact encode_decodeAcross (d.acrossLeft x) (fun v hv => by
      obtain ⟨y,hy,_⟩ := (d.across_valid x v hv).2.2
      exact ⟨y,hy⟩)
  · funext v
    change (firstDecode p w.length v).bind (fun y => d.acrossRight (first p w.length y)) = d.acrossRight v
    cases hv : firstDecode p w.length v with
    | some y =>
      have he := (firstDecode_some p w.length v y).mp hv
      simp only [Option.bind_some]
      rw [he]
    | none =>
      change none = d.acrossRight v
      cases hr : d.acrossRight v with
      | none => rfl
      | some x =>
        obtain ⟨y,hy,_⟩ := (d.across_valid x v ((d.across_symm x v).mpr hr)).2.2
        have hd := (firstDecode_some p w.length v y).mpr hy.symm
        rw [hv] at hd
        contradiction

 theorem CutData.fromJoin_toJoin {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p))
    (d : CutData R w) : cutDataFromJoin R w d.toJoinData = d := by
  apply CutData.ext
  · rfl
  · apply PartialPairs.ext_left
    funext x
    change decodeAcross ((d.pairs.left x).map (first p w.length)) = d.pairs.left x
    cases h : d.pairs.left x <;> simp [decodeAcross,firstDecode_first]

/-- Exact matching decomposition at the first cut. It records actual graph edges,
not a transfer-count equation or a certificate of one. -/
def cutMatchingEquiv {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p)) :
    EncodedMatching (graph (R::w)) ≃ CutData R w :=
  joinMatchingEquiv.trans {
    toFun := cutDataFromJoin R w
    invFun := CutData.toJoinData
    left_inv := CutData.toJoin_fromJoin R w
    right_inv := CutData.fromJoin_toJoin R w }

noncomputable instance {p : ℕ} (R : UnweightedCut p) (w : List (UnweightedCut p)) :
    Fintype (CutData R w) := Fintype.ofEquiv (EncodedMatching (graph (R::w))) (cutMatchingEquiv R w)

end HiddenCircuits.Layered
