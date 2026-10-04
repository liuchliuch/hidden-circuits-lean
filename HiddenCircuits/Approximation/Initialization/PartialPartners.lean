import HiddenCircuits.Approximation.SwitchChain
import HiddenCircuits.PerfectPartners

/-! An actual permutation accumulator for
partial perfect matchings. Retained vertices are fixed; all other vertices
already have graph-adjacent involutive partners. -/
namespace HiddenCircuits.Approximation.Initialization.PartialPartners

variable {n : ℕ} {G : SimpleGraph (Fin n)}

structure Valid (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    (π : Equiv.Perm (Fin n)) : Prop where
  fixed : ∀ v ∈ U, π v = v
  involutive : Function.Involutive π
  adjacent : ∀ v, v ∉ U → G.Adj v (π v)

theorem initial (G : SimpleGraph (Fin n)) :
    Valid G Finset.univ (Equiv.refl (Fin n)) :=
  ⟨by simp, by intro v; rfl, by simp⟩

theorem add_pair {U : Finset (Fin n)} {π : Equiv.Perm (Fin n)}
    (hπ : Valid G U π) (u v : Fin n) (hu : u ∈ U) (hv : v ∈ U)
    (he : G.Adj u v) :
    Valid G ((U.erase u).erase v) (MonotoneEndpoints.transpose π u v) := by
  classical
  have hpu := hπ.fixed u hu
  have hpv := hπ.fixed v hv
  have huv : u ≠ v := he.ne
  constructor
  · intro w hw
    rcases Finset.mem_erase.mp hw with ⟨hwv, hw⟩
    rcases Finset.mem_erase.mp hw with ⟨hwu, hw⟩
    simpa [MonotoneEndpoints.transpose_apply, Equiv.swap_apply_of_ne_of_ne hwu hwv]
      using hπ.fixed w hw
  · intro w
    by_cases hwu : w = u
    · subst w
      simp [MonotoneEndpoints.transpose_apply, hpu, hpv]
    by_cases hwv : w = v
    · subst w
      simp [MonotoneEndpoints.transpose_apply, hpu, hpv]
    have hπu : π w ≠ u := by
      intro hh
      exact hwu (π.injective (hh.trans hpu.symm))
    have hπv : π w ≠ v := by
      intro hh
      exact hwv (π.injective (hh.trans hpv.symm))
    simpa [MonotoneEndpoints.transpose_apply,
      Equiv.swap_apply_of_ne_of_ne hwu hwv,
      Equiv.swap_apply_of_ne_of_ne hπu hπv] using hπ.involutive w
  · intro w hw
    by_cases hwu : w = u
    · subst w
      simpa [MonotoneEndpoints.transpose_apply, hpv] using he
    by_cases hwv : w = v
    · subst w
      simpa [MonotoneEndpoints.transpose_apply, hpu] using he.symm
    have hwU : w ∉ U := by
      intro hh
      exact hw (Finset.mem_erase.mpr ⟨hwv, Finset.mem_erase.mpr ⟨hwu, hh⟩⟩)
    simpa [MonotoneEndpoints.transpose_apply, Equiv.swap_apply_of_ne_of_ne hwu hwv]
      using hπ.adjacent w hwU

def finish {π : Equiv.Perm (Fin n)} (hπ : Valid G ∅ π) : PerfectPartner G :=
  ⟨π, hπ.involutive, fun v => hπ.adjacent v (by simp)⟩

@[simp] theorem finish_val {π : Equiv.Perm (Fin n)} (hπ : Valid G ∅ π) :
    (finish hπ).val = π := rfl

end HiddenCircuits.Approximation.Initialization.PartialPartners
