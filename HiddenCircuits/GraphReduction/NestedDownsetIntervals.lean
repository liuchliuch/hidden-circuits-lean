import HiddenCircuits.GraphReduction.IntervalOrder

/-! The finite interval-order construction from linearly nested strict downsets. -/
namespace HiddenCircuits.GraphReduction.Interval
variable {V : Type*} [Fintype V] (R : V → V → Prop) [DecidableRel R]

def downset (v : V) : Finset V := Finset.univ.filter (fun x => R x v)
def downCount (v : V) : ℕ := (downset R v).card

def downRight (v : V) : ℕ := Finset.univ.sup (fun w => if R v w then 0 else downCount R w)

def NestedDownsets : Prop :=
  ∀ x y, (∀ v, R v x → R v y) ∨ (∀ v, R v y → R v x)

lemma downRight_lt_iff (hn : NestedDownsets R) (x y : V) :
    downRight R x < downCount R y ↔ R x y := by
  constructor
  · intro hc
    by_contra hxy
    have hb := Finset.le_sup (f:=fun w => if R x w then 0 else downCount R w)
      (show y ∈ Finset.univ from Finset.mem_univ y)
    simp only [hxy,ite_false] at hb
    exact (Nat.not_lt_of_ge hb) hc
  · intro hxy
    have hy : 0 < downCount R y := Finset.card_pos.mpr ⟨x,by simp [downset,hxy]⟩
    apply (Finset.sup_lt_iff hy).mpr
    intro z _
    split_ifs with hxz
    · exact hy
    · have hsub : downset R z ⊂ downset R y := by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · rcases hn z y with h | h
          · intro v hv
            simp only [downset,Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
            exact h v hv
          · exact False.elim (hxz (h x hxy))
        · intro he
          have hx : x ∈ downset R y := by simp [downset,hxy]
          rw [←he] at hx
          exact hxz (by simpa only [downset,Finset.mem_filter,Finset.mem_univ,true_and] using hx)
      exact Finset.card_lt_card hsub

/-- Closed integer intervals represent the incomparability graph of any finite
irreflexive relation whose strict downsets are linearly nested. -/
def ofNestedDownsets (G : SimpleGraph V) (hirr : ∀ v, ¬R v v)
    (hn : NestedDownsets R)
    (hG : ∀ x y, G.Adj x y ↔ x ≠ y ∧ ¬R x y ∧ ¬R y x) : NatRepresentation G where
  left := downCount R
  right := downRight R
  ordered v := by
    have h := (downRight_lt_iff R hn v v).not
    exact Nat.le_of_not_gt (h.mpr (hirr v))
  adjacency x y := by
    rw [hG]
    rw [←downRight_lt_iff R hn x y,←downRight_lt_iff R hn y x]
    simp only [Nat.not_lt]
    exact and_congr_right (fun _ => and_comm)

end HiddenCircuits.GraphReduction.Interval
