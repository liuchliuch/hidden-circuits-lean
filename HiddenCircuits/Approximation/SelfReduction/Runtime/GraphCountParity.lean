import HiddenCircuits.PerfectPartners

/-! The physical odd-order
rejection is exact on every graph, independently of the quasimonotone promise. -/
namespace HiddenCircuits.Approximation.SelfReduction.GraphCount

 theorem perfectMatchingCount_zero_of_odd {n : ℕ} (G : SimpleGraph (Fin n))
    (hn : n%2 ≠ 0) : perfectMatchingCount G=0 := by
  classical
  rw [perfectMatchingCount_eq_partners]
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun P => ?_⟩
  have he := P.toMatching.property.even_card
  simp only [Fintype.card_fin] at he
  exact hn (Nat.even_iff.mp he)

 theorem half_vertices (n : ℕ) (hn : n%2=0) : 2*(n/2)=n := by omega

 theorem half_vertices_le (n N : ℕ) (h : n ≤ N) : n/2 ≤ N :=
  (Nat.div_le_self n 2).trans h

end HiddenCircuits.Approximation.SelfReduction.GraphCount
