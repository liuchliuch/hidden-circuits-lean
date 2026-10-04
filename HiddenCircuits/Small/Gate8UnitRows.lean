import HiddenCircuits.Small.Gate8Upper
import HiddenCircuits.Small.Gate8IntSparse
namespace HiddenCircuits.Small

/-- A cut whose selected row thresholds are another actual state reuses the
already certified upper-compound row. This covers the unit rows exactly. -/
theorem gate8_unit_row (r : Fin 70 → List (Fin 70 × ℤ)) (f : Fin 8 → Fin 8)
    (a b : Fin 70) (hr : r a = [(b,1)])
    (hs : ∀ j, f (gate8Tracks a j) = gate8Tracks b j) :
    ∀ t, sparseIntProduct r Gate8FNat a t = (gate8FastCompound f a t : ℤ) := by
  intro t
  simp only [sparseIntProduct, hr, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, one_mul, add_zero]
  rw [← gate8_upper_nat]
  apply congrArg (fun x : ℕ => (x : ℤ))
  apply congrArg gate8FastPermanent
  funext j
  rw [hs j]
  rfl

end HiddenCircuits.Small
