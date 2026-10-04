import HiddenCircuits.Approximation.SelfReduction.HeavyBranch

/-! A computable densest-cluster estimator. A strict majority of ε-accurate
observations guarantees a selected observation within 3ε of the target. -/
namespace HiddenCircuits.Approximation.SelfReduction

 def cluster (n : ℕ) (z : Fin (n+1) → ℚ) (ε : ℚ) (i : Fin (n+1)) : Finset (Fin (n+1)) :=
  Finset.univ.filter (fun j => |z j-z i| ≤ 2*ε)

 def robustEstimate (n : ℕ) (z : Fin (n+1) → ℚ) (ε : ℚ) : ℚ :=
  z (chooseMax n (fun i => (cluster n z ε i).card))

 theorem robustEstimate_accurate (n : ℕ) (z : Fin (n+1) → ℚ) (p ε : ℚ)
    (hmajor : n+1<2*(Finset.univ.filter (fun i => |z i-p| ≤ ε)).card) :
    |robustEstimate n z ε-p| ≤ 3*ε := by
  classical
  let G := Finset.univ.filter (fun i => |z i-p| ≤ ε)
  let j := chooseMax n (fun i => (cluster n z ε i).card)
  have hgpos : 0<G.card := by dsimp [G]; omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hgpos
  have hip : |z i-p| ≤ ε := (Finset.mem_filter.mp hi).2
  have hsub : G ⊆ cluster n z ε i := by
    intro a ha
    have hap : |z a-p| ≤ ε := (Finset.mem_filter.mp ha).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    calc
      |z a-z i|=|(z a-p)+(p-z i)| := by congr 1; ring
      _ ≤ |z a-p|+|p-z i| := abs_add_le _ _
      _ ≤ 2*ε := by rw [abs_sub_comm p]; linarith
  have hj : G.card ≤ (cluster n z ε j).card :=
    (Finset.card_le_card hsub).trans (chooseMax_spec n (fun i => (cluster n z ε i).card) i)
  have hc : (Finset.univ : Finset (Fin (n+1))).card<G.card+(cluster n z ε j).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    dsimp [G] at hj ⊢
    omega
  obtain ⟨a,ha⟩ := Finset.inter_nonempty_of_card_lt_card_add_card
    (Finset.subset_univ G) (Finset.subset_univ (cluster n z ε j)) hc
  obtain ⟨hag,hac⟩ := Finset.mem_inter.mp ha
  have hap : |z a-p| ≤ ε := (Finset.mem_filter.mp hag).2
  have haj : |z a-z j| ≤ 2*ε := (Finset.mem_filter.mp hac).2
  change |z j-p| ≤ 3*ε
  calc
    |z j-p|=|(z j-z a)+(z a-p)| := by congr 1; ring
    _ ≤ |z j-z a|+|z a-p| := abs_add_le _ _
    _ ≤ 3*ε := by rw [abs_sub_comm (z j)]; linarith

end HiddenCircuits.Approximation.SelfReduction
