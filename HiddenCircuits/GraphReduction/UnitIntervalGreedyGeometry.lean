import HiddenCircuits.GraphReduction.UnitIntervalGreedyRun

/-! Geometric invariants of the executable greedy component scan. Coordinates
are proof witnesses only; the selector inspects integer graph counts. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalGreedy
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure Fits (r : RealUnitInterval.Representation G) (ls : List V) (R : Finset V) : Prop where
  sorted : ls.Pairwise (fun v w => r.left v ≤ r.left w)
  beforeRemaining : ∀ v ∈ ls, ∀ w ∈ R, r.left v ≤ r.left w

lemma fits_step (r : RealUnitInterval.Representation G) (ls : List V) (R : Finset V)
    (hf : Fits r ls R) (hdis : ∀ v ∈ ls, v ∉ R)
    (hcover : ∀ v, v ∈ ls ∨ v ∈ R) {y : V}
    (hy : choose G ls.toFinset R = some y) (hpos : score G ls.toFinset y ≠ 0) :
    ∃ r' : RealUnitInterval.Representation G, Fits r' (ls++[y]) (R.erase y) := by
  classical
  have hp := choose_spec G ls.toFinset R hy
  obtain ⟨x,hx,hmin⟩ := R.exists_min_image r.left ⟨y,hp.1⟩
  have hsub := neighbors_mono_left r ls.toFinset (hmin y hp.1)
    (fun v hv => hf.beforeRemaining v (List.mem_toFinset.mp hv) x hx)
  have hxp : 0 < score G ls.toFinset x := by
    have := Finset.card_le_card hsub
    change score G ls.toFinset y ≤ score G ls.toFinset x at this
    omega
  have ht := preferred_twin r ls.toFinset R
    (fun v => (hcover v).imp List.mem_toFinset.mpr id) hx
    (fun v hv w hw => hf.beforeRemaining v (List.mem_toFinset.mp hv) w hw) hmin hp hxp
  let r' := swapRepresentation r ht
  have hsame : ∀ v ∈ ls, r'.left v = r.left v := by
    intro v hv
    have hvx : v ≠ x := fun he => hdis v hv (he.symm ▸ hx)
    have hvy : v ≠ y := fun he => hdis v hv (he.symm ▸ hp.1)
    exact congrArg r.left (Equiv.swap_apply_of_ne_of_ne hvx hvy)
  have hnew : r'.left y = r.left x := by simp [r',swapRepresentation]
  have hswap : ∀ v ∈ R, Equiv.swap x y v ∈ R := by
    intro v hv
    by_cases hvx : v=x
    · subst v; simpa using hp.1
    · by_cases hvy : v=y
      · subst v; simpa using hx
      · rwa [Equiv.swap_apply_of_ne_of_ne hvx hvy]
  refine ⟨r',⟨?_,?_⟩⟩
  · apply List.pairwise_append.mpr
    refine ⟨?_,by simp,?_⟩
    · exact hf.sorted.imp_of_mem (fun {v w} hv hw h => by rw [hsame v hv,hsame w hw]; exact h)
    · intro v hv w hw
      have hwy : w=y := by simpa using hw
      subst w
      rw [hsame v hv,hnew]
      exact hf.beforeRemaining v hv x hx
  · intro v hv w hw
    have hwr : w ∈ R := Finset.mem_of_mem_erase hw
    rcases List.mem_append.mp hv with hv|hv
    · rw [hsame v hv]
      exact hf.beforeRemaining v hv (Equiv.swap x y w) (hswap w hwr)
    · have hvy : v=y := by simpa using hv
      subst v
      rw [hnew]
      exact hmin (Equiv.swap x y w) (hswap w hwr)

/-- Every bounded execution from a valid geometric prefix retains a real model
in which the emitted sequence is sorted. Twin swaps never change its graph. -/
theorem run_fits (fuel : ℕ) (ls : List V) (R : Finset V)
    (r : RealUnitInterval.Representation G) (hfit : Fits r ls R)
    (hdis : ∀ v ∈ ls, v ∉ R) (hcover : ∀ v, v ∈ ls ∨ v ∈ R) :
    ∃ r' : RealUnitInterval.Representation G, Fits r' (run G fuel ls R).1 (run G fuel ls R).2 := by
  induction fuel generalizing ls R r with
  | zero => exact ⟨r,hfit⟩
  | succ fuel ih =>
    simp only [run]
    split
    · exact ⟨r,hfit⟩
    · rename_i y hy
      split
      · exact ⟨r,hfit⟩
      · rename_i hpos
        obtain ⟨r',hfit'⟩ := fits_step r ls R hfit hdis hcover hy hpos
        have hyr := (choose_spec G ls.toFinset R hy).1
        apply ih (ls++[y]) (R.erase y) r' hfit'
        · intro v hv hvr
          rcases List.mem_append.mp hv with hv|hv
          · exact hdis v hv (Finset.mem_of_mem_erase hvr)
          · have hvy : v=y := by simpa using hv
            subst v; exact (Finset.mem_erase.mp hvr).1 rfl
        · intro v
          by_cases he : v=y
          · subst v; exact Or.inl (by simp)
          · rcases hcover v with hv|hv
            · exact Or.inl (List.mem_append_left _ hv)
            · exact Or.inr (Finset.mem_erase.mpr ⟨he,hv⟩)

/-- A genuinely leftmost start, which exists in every nonempty represented
residual graph, always yields a sorted component sequence. -/
theorem component_sorted (r : RealUnitInterval.Representation G) (root : V)
    (hroot : ∀ v, r.left root ≤ r.left v) :
    ∃ r' : RealUnitInterval.Representation G,
      (component G root).Pairwise (fun v w => r'.left v ≤ r'.left w) := by
  have hf : Fits r [root] (Finset.univ.erase root) := by
    refine ⟨by simp,?_⟩
    intro v hv w _
    have he : v=root := by simpa using hv
    subst v
    exact hroot w
  have hd : ∀ v ∈ [root], v ∉ Finset.univ.erase root := by simp
  have hc : ∀ v, v ∈ [root] ∨ v ∈ Finset.univ.erase root := by intro v; simp; tauto
  obtain ⟨r',hfit⟩ := run_fits (Fintype.card V) [root] (Finset.univ.erase root) r hf hd hc
  exact ⟨r',hfit.sorted⟩

end HiddenCircuits.GraphReduction.UnitIntervalGreedy
