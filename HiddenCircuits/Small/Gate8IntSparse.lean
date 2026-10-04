import HiddenCircuits.Small.Gate8Threshold
namespace HiddenCircuits.Small

def sparseIntProduct {n m p : ℕ} (a : Fin n → List (Fin m × ℤ))
    (B : Matrix (Fin m) (Fin p) ℕ) : Matrix (Fin n) (Fin p) ℤ :=
  fun i j => ((a i).map (fun x => x.2 * (B x.1 j : ℤ))).sum

theorem sparseProduct_intCast {n m p : ℕ} (a : Fin n → List (Fin m × ℤ))
    (B : Matrix (Fin m) (Fin p) ℕ) :
    sparseProduct (fun i => (a i).map (fun x => (x.1,(x.2 : ℚ))))
      (fun i j => (B i j : ℚ)) = fun i j => (sparseIntProduct a B i j : ℚ) := by
  ext i j
  simp [sparseProduct, sparseIntProduct, List.map_map, Function.comp_def]

theorem sparseProduct_intCast_eq {n m p : ℕ} (a : Fin n → List (Fin m × ℤ))
    (B : Matrix (Fin m) (Fin p) ℕ) (C : Matrix (Fin n) (Fin p) ℕ)
    (h : sparseIntProduct a B = fun i j => (C i j : ℤ)) :
    sparseProduct (fun i => (a i).map (fun x => (x.1,(x.2 : ℚ))))
      (fun i j => (B i j : ℚ)) = fun i j => (C i j : ℚ) := by
  rw [sparseProduct_intCast, h]
  simp only [Int.cast_natCast]

end HiddenCircuits.Small
