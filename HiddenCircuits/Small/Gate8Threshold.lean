import HiddenCircuits.Small.Gate8Ferrers
namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option trace.profiler true
set_option trace.profiler.threshold 500
def gate8Threshold : Fin 70 → Fin 8 → Fin 5 := ![![0, 1, 2, 3, 4, 4, 4, 4], ![0, 1, 2, 3, 3, 4, 4, 4], ![0, 1, 2, 3, 3, 3, 4, 4], ![0, 1, 2, 3, 3, 3, 3, 4], ![0, 1, 2, 3, 3, 3, 3, 3], ![0, 1, 2, 2, 3, 4, 4, 4], ![0, 1, 2, 2, 3, 3, 4, 4], ![0, 1, 2, 2, 3, 3, 3, 4], ![0, 1, 2, 2, 3, 3, 3, 3], ![0, 1, 2, 2, 2, 3, 4, 4], ![0, 1, 2, 2, 2, 3, 3, 4], ![0, 1, 2, 2, 2, 3, 3, 3], ![0, 1, 2, 2, 2, 2, 3, 4], ![0, 1, 2, 2, 2, 2, 3, 3], ![0, 1, 2, 2, 2, 2, 2, 3], ![0, 1, 1, 2, 3, 4, 4, 4], ![0, 1, 1, 2, 3, 3, 4, 4], ![0, 1, 1, 2, 3, 3, 3, 4], ![0, 1, 1, 2, 3, 3, 3, 3], ![0, 1, 1, 2, 2, 3, 4, 4], ![0, 1, 1, 2, 2, 3, 3, 4], ![0, 1, 1, 2, 2, 3, 3, 3], ![0, 1, 1, 2, 2, 2, 3, 4], ![0, 1, 1, 2, 2, 2, 3, 3], ![0, 1, 1, 2, 2, 2, 2, 3], ![0, 1, 1, 1, 2, 3, 4, 4], ![0, 1, 1, 1, 2, 3, 3, 4], ![0, 1, 1, 1, 2, 3, 3, 3], ![0, 1, 1, 1, 2, 2, 3, 4], ![0, 1, 1, 1, 2, 2, 3, 3], ![0, 1, 1, 1, 2, 2, 2, 3], ![0, 1, 1, 1, 1, 2, 3, 4], ![0, 1, 1, 1, 1, 2, 3, 3], ![0, 1, 1, 1, 1, 2, 2, 3], ![0, 1, 1, 1, 1, 1, 2, 3], ![0, 0, 1, 2, 3, 4, 4, 4], ![0, 0, 1, 2, 3, 3, 4, 4], ![0, 0, 1, 2, 3, 3, 3, 4], ![0, 0, 1, 2, 3, 3, 3, 3], ![0, 0, 1, 2, 2, 3, 4, 4], ![0, 0, 1, 2, 2, 3, 3, 4], ![0, 0, 1, 2, 2, 3, 3, 3], ![0, 0, 1, 2, 2, 2, 3, 4], ![0, 0, 1, 2, 2, 2, 3, 3], ![0, 0, 1, 2, 2, 2, 2, 3], ![0, 0, 1, 1, 2, 3, 4, 4], ![0, 0, 1, 1, 2, 3, 3, 4], ![0, 0, 1, 1, 2, 3, 3, 3], ![0, 0, 1, 1, 2, 2, 3, 4], ![0, 0, 1, 1, 2, 2, 3, 3], ![0, 0, 1, 1, 2, 2, 2, 3], ![0, 0, 1, 1, 1, 2, 3, 4], ![0, 0, 1, 1, 1, 2, 3, 3], ![0, 0, 1, 1, 1, 2, 2, 3], ![0, 0, 1, 1, 1, 1, 2, 3], ![0, 0, 0, 1, 2, 3, 4, 4], ![0, 0, 0, 1, 2, 3, 3, 4], ![0, 0, 0, 1, 2, 3, 3, 3], ![0, 0, 0, 1, 2, 2, 3, 4], ![0, 0, 0, 1, 2, 2, 3, 3], ![0, 0, 0, 1, 2, 2, 2, 3], ![0, 0, 0, 1, 1, 2, 3, 4], ![0, 0, 0, 1, 1, 2, 3, 3], ![0, 0, 0, 1, 1, 2, 2, 3], ![0, 0, 0, 1, 1, 1, 2, 3], ![0, 0, 0, 0, 1, 2, 3, 4], ![0, 0, 0, 0, 1, 2, 3, 3], ![0, 0, 0, 0, 1, 2, 2, 3], ![0, 0, 0, 0, 1, 1, 2, 3], ![0, 0, 0, 0, 0, 1, 2, 3]]
theorem gate8Threshold_spec : ∀ t b j,
    (if b ≤ gate8Tracks t j then 1 else 0 : ℕ) =
      if (gate8Threshold t b).val ≤ j.val then 1 else 0 := by decide +kernel

def gate8FerrersCut (f : Fin 8 → Fin 8) : Matrix (Fin 8) (Fin 8) ℕ :=
  fun a b => if f a ≤ b then 1 else 0

def gate8FastCompound (f : Fin 8 → Fin 8) : Matrix (Fin 70) (Fin 70) ℕ :=
  fun s t => gate8FastPermanent (fun i => gate8Threshold t (f (gate8Tracks s i)))

theorem gate8_fast_compound (f : Fin 8 → Fin 8) :
    gate8NatCompound (gate8FerrersCut f) = gate8FastCompound f := by
  ext s t
  change (∑ σ : Fin 24, ∏ j : Fin 4,
    if f (gate8Tracks s (gate8PermMaps σ j)) ≤ gate8Tracks t j then 1 else 0) = _
  calc
    _ = gate8SuffixPermanent (fun i => gate8Threshold t (f (gate8Tracks s i))) := by
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.prod_congr rfl
      intro j _
      exact gate8Threshold_spec t _ j
    _ = _ := gate8Ferrers _

def gate8AddedBound (i : Fin 7) (a : Fin 8) : Fin 8 :=
  if a.val = i.val + 1 then i.castSucc else a

def gate8DeletedBound (i : Fin 7) (a : Fin 8) : Fin 8 :=
  if a.val = i.val then i.succ else a

theorem gate8AddedNat_ferrers : ∀ i, gate8AddedNat i = gate8FerrersCut (gate8AddedBound i) := by
  decide +kernel

theorem gate8DeletedNat_ferrers : ∀ i, gate8DeletedNat i = gate8FerrersCut (gate8DeletedBound i) := by
  decide +kernel

end HiddenCircuits.Small
