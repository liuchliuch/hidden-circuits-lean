import HiddenCircuits.Approximation.SamplerRuntime.EndpointFiber

/-! Exact scalar boundary update for the typed endpoint deletion. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.EndpointFiber
open GraphReduction

/-- Delete column j from a half-open prefix ending at boundary t. -/
def dropBoundary (j t : ℕ) : ℕ := t-(if j<t then 1 else 0)

lemma succAbove_lt_iff {n : ℕ} (j : Fin (n+1)) (k : Fin n) (t : ℕ) :
    (j.succAbove k).val<t ↔ k.val<dropBoundary j.val t := by
  by_cases hk : k.castSucc<j
  · rw [Fin.succAbove_of_castSucc_lt j k hk]
    change k.val<t ↔ k.val<dropBoundary j.val t
    have hh : k.val<j.val := hk
    unfold dropBoundary
    split_ifs <;> omega
  · rw [Fin.succAbove_of_le_castSucc j k (le_of_not_gt hk)]
    change k.val+1<t ↔ k.val<dropBoundary j.val t
    have hh : j.val≤k.val := le_of_not_gt hk
    unfold dropBoundary
    split_ifs <;> omega

lemma endpointCount_succAbove {n : ℕ} (j : Fin (n+1)) (t : ℕ) (ht : t≤n+1) :
    endpointCount (fun k : Fin n => (j.succAbove k).val) t=dropBoundary j.val t := by
  let c := endpointCount (fun k : Fin n => (j.succAbove k).val) t
  have hc : c≤n := by
    simpa only [Fintype.card_fin] using endpointCount_upper (fun k : Fin n => (j.succAbove k).val) t
  have hb : dropBoundary j.val t≤n := by
    have hj := j.isLt
    unfold dropBoundary
    split_ifs <;> omega
  have he (k : Fin n) : k.val<c ↔ k.val<dropBoundary j.val t :=
    (endpointCount_index (fun k : Fin n => (j.succAbove k).val)
      (fun a b h => Fin.strictMono_succAbove j h) k t).symm.trans (succAbove_lt_iff j k t)
  apply Nat.le_antisymm
  · by_contra hh
    have hlt : dropBoundary j.val t<c := Nat.lt_of_not_ge hh
    let k : Fin n := ⟨dropBoundary j.val t,lt_of_lt_of_le hlt hc⟩
    have hk := he k
    dsimp [k] at hk
    omega
  · by_contra hh
    have hlt : c<dropBoundary j.val t := Nat.lt_of_not_ge hh
    let k : Fin n := ⟨c,lt_of_lt_of_le hlt hb⟩
    have hk := he k
    dsimp [k] at hk
    omega

/-- Remove the first row and decrement each remaining lower boundary precisely
when the deleted column lies below that boundary. -/
theorem deleteFirst_lo {n : ℕ} (E : MonotoneEndpoints (n+1)) (j : Fin (n+1)) (i : Fin n) :
    (deleteFirst E j).lo i=dropBoundary j.val (E.lo i.succ) :=
  endpointCount_succAbove j _ ((E.lo_le_hi i.succ).trans (E.hi_le i.succ))

/-- The same strict comparison updates the half-open upper boundary. -/
theorem deleteFirst_hi {n : ℕ} (E : MonotoneEndpoints (n+1)) (j : Fin (n+1)) (i : Fin n) :
    (deleteFirst E j).hi i=dropBoundary j.val (E.hi i.succ) :=
  endpointCount_succAbove j _ (E.hi_le i.succ)

end HiddenCircuits.Approximation.SamplerRuntime.EndpointFiber
