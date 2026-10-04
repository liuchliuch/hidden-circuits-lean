import HiddenCircuits.DH.Pruning

/-! Actual twin transpositions preserve adjacency and distances from every other root. -/
namespace HiddenCircuits.DH
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {u v : V}

noncomputable def TwinPair.swapIso (h : TwinPair G u v) : G ≃g G := by
  classical
  refine { toEquiv := Equiv.swap u v, map_rel_iff' := ?_ }
  intro x y
  by_cases hxu : x=u
  · subst x
    by_cases hyu : y=u
    · subst y; simp
    · by_cases hyv : y=v
      · subst y; simp [h.distinct,G.adj_comm]
      · rw [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne hyu hyv]
        exact h.external y hyu hyv
  · by_cases hxv : x=v
    · subst x
      by_cases hyu : y=u
      · subst y; simp [h.distinct,G.adj_comm]
      · by_cases hyv : y=v
        · subst y; simp
        · rw [Equiv.swap_apply_right,Equiv.swap_apply_of_ne_of_ne hyu hyv]
          exact (h.external y hyu hyv).symm
    · rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]
      by_cases hyu : y=u
      · subst y
        rw [Equiv.swap_apply_left]
        simpa only [G.adj_comm] using h.external x hxu hxv
      · by_cases hyv : y=v
        · subst y
          rw [Equiv.swap_apply_right]
          simpa only [G.adj_comm] using (h.external x hxu hxv).symm
        · rw [Equiv.swap_apply_of_ne_of_ne hyu hyv]

@[simp] lemma TwinPair.swapIso_left (h : TwinPair G u v) : h.swapIso u=v := by
  classical
  exact Equiv.swap_apply_left u v

@[simp] lemma TwinPair.swapIso_right (h : TwinPair G u v) : h.swapIso v=u := by
  classical
  exact Equiv.swap_apply_right u v

lemma TwinPair.swapIso_other (h : TwinPair G u v) (x : V) (hxu : x≠u) (hxv : x≠v) :
    h.swapIso x=x := by
  classical
  exact Equiv.swap_apply_of_ne_of_ne hxu hxv

/-- Twins can lie in different BFS layers only when the root is one of them. -/
theorem TwinPair.dist_eq_of_root_other (h : TwinPair G u v) (r : V) (hru : r≠u) (hrv : r≠v) :
    G.dist r u = G.dist r v := by
  have hd := iso_dist_eq h.swapIso r u
  rw [h.swapIso_other r hru hrv,h.swapIso_left] at hd
  exact hd.symm

end HiddenCircuits.DH
