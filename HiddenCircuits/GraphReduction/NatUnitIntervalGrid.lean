import HiddenCircuits.GraphReduction.FiniteOrderRank

/-! Integer-only bounded unit-grid compression. The source coordinate U/D uses
one positive common denominator. Quotient/remainder scans and finite comparison
ranks preserve U(v)≤U(w)+D, without rational arithmetic or normalization. -/
namespace HiddenCircuits.GraphReduction.NatUnitIntervalGrid
open FiniteOrderRank
variable {V : Type*} [Fintype V]

def quotientParts (D : ℕ) (u : V → ℕ) : Finset ℕ :=
  Finset.univ.image (fun v => u v/D) ∪ Finset.univ.image (fun v => u v/D+1)
def remainderParts (D : ℕ) (u : V → ℕ) : Finset ℕ := Finset.univ.image (fun v => u v%D)
def denominator : ℕ := max 1 (Fintype.card V)
def numerator (D : ℕ) (u : V → ℕ) (v : V) : ℕ :=
  denominator (V:=V)*rank (quotientParts D u) (u v/D) + rank (remainderParts D u) (u v%D)

lemma quotient_mem (D : ℕ) (u : V → ℕ) (v : V) : u v/D ∈ quotientParts D u := by simp [quotientParts]
lemma successor_mem (D : ℕ) (u : V → ℕ) (v : V) : u v/D+1 ∈ quotientParts D u := by simp [quotientParts]
lemma remainder_mem (D : ℕ) (u : V → ℕ) (v : V) : u v%D ∈ remainderParts D u := by simp [remainderParts]
lemma denominator_pos : 0 < denominator (V:=V) := by simp [denominator]
lemma card_le_denominator : Fintype.card V ≤ denominator (V:=V) := le_max_right _ _

private lemma rank_succ {s : Finset ℕ} {a : ℕ} (ha : a ∈ s) : rank s (a+1) = rank s a+1 := by
  have he : s.filter (· < a+1) = insert a (s.filter (· < a)) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_insert]
    constructor
    · rintro ⟨hx,hxa⟩
      by_cases he : x=a
      · exact Or.inl he
      · exact Or.inr ⟨hx,by omega⟩
    · rintro (rfl|⟨hx,hxa⟩)
      · exact ⟨ha,by omega⟩
      · exact ⟨hx,by omega⟩
  unfold rank
  rw [he,Finset.card_insert_of_notMem]
  simp

lemma quotientParts_card (D : ℕ) (u : V → ℕ) : (quotientParts D u).card ≤ 2*Fintype.card V := by
  unfold quotientParts
  have h1 := Finset.card_image_le (s:=Finset.univ) (f:=fun v => u v/D)
  have h2 := Finset.card_image_le (s:=Finset.univ) (f:=fun v => u v/D+1)
  have h3 := Finset.card_union_le (Finset.univ.image (fun v => u v/D)) (Finset.univ.image (fun v => u v/D+1))
  simp only [Finset.card_univ] at h1 h2
  omega
lemma remainder_rank_lt (D : ℕ) (u : V → ℕ) (v : V) :
    rank (remainderParts D u) (u v%D) < denominator (V:=V) := by
  have hc : (remainderParts D u).card ≤ Fintype.card V := by
    simpa [remainderParts] using Finset.card_image_le (s:=Finset.univ) (f:=fun v => u v%D)
  exact (lt_card (remainder_mem D u v)).trans_le (hc.trans card_le_denominator)

/-- Both output endpoints are quadratically bounded for every source array. -/
theorem endpoint_bound (D : ℕ) (u : V → ℕ) (v : V) :
    numerator D u v + denominator (V:=V) < 2*Fintype.card V*denominator (V:=V) := by
  have hi := lt_card (successor_mem D u v)
  rw [rank_succ (quotient_mem D u v)] at hi
  have hc := quotientParts_card D u
  have hr := remainder_rank_lt D u v
  unfold numerator
  nlinarith

/-- Exact threshold comparison, using only natural division and remainder. -/
theorem comparison (D : ℕ) (hD : 0 < D) (u : V → ℕ) (v w : V) :
    numerator D u v ≤ numerator D u w+denominator (V:=V) ↔ u v ≤ u w+D := by
  have hv := remainder_rank_lt D u v
  have hw := remainder_rank_lt D u w
  have hp := denominator_pos (V:=V)
  have hvD := Nat.mod_lt (u v) hD
  have hwD := Nat.mod_lt (u w) hD
  have hev := Nat.mod_add_div (u v) D
  have hew := Nat.mod_add_div (u w) D
  rcases le_or_gt (u v/D) (u w/D) with h | h
  · have hg := mono (quotientParts D u) h
    have hm := Nat.mul_le_mul_left D h
    constructor
    · intro _; omega
    · intro _; unfold numerator; nlinarith
  · by_cases he : u v/D = u w/D+1
    · have hg : rank (quotientParts D u) (u v/D) = rank (quotientParts D u) (u w/D)+1 := by
        rw [he,rank_succ (quotient_mem D u w)]
      have hc := le_iff (s:=remainderParts D u) (a:=u v%D) (remainder_mem D u w)
      unfold numerator
      rw [hg]
      constructor
      · intro hn
        have hr : rank (remainderParts D u) (u v%D) ≤ rank (remainderParts D u) (u w%D) := by nlinarith
        have := hc.mp hr
        nlinarith
      · intro hn
        have hr : u v%D ≤ u w%D := by nlinarith
        have := hc.mpr hr
        nlinarith
    · have hh : u w/D+1 < u v/D := by omega
      have hg := strict (successor_mem D u w) hh
      rw [rank_succ (quotient_mem D u w)] at hg
      have hm := Nat.mul_le_mul_left D (show u w/D+2 ≤ u v/D by omega)
      constructor
      · intro hn; unfold numerator at hn; nlinarith
      · intro hn
        have hm' : D*(u w/D)+2*D ≤ D*(u v/D) := by nlinarith [hm]
        omega

end HiddenCircuits.GraphReduction.NatUnitIntervalGrid
