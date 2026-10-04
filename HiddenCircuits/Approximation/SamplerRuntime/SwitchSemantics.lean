import HiddenCircuits.Approximation.SamplerRuntime.Switch
import HiddenCircuits.Approximation.SamplerRuntime.RuntimeBounds
import HiddenCircuits.GraphReduction.MonotoneEndpointEncoding
import HiddenCircuits.Approximation.SwitchChain

/-! Identification of the literal array program with the admissible-permutation switch. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Switch
open Complexity Complexity.OracleBlock GraphReduction.MonotoneEndpointEncoding Approximation

variable {n : ℕ}
def rowWords (π : Equiv.Perm (Fin n)) : List BitString := rows (fun i => (π i).val)

lemma rows_encoded_length (f : Fin n → ℕ) (hf : ∀i,f i≤n) :
    (encodeBitList (rows f)).length≤2*n*n+2*n := by
  have hh := rows_size f hf
  simp only [encodeBitList_length,rows_length]
  nlinarith

@[simp] lemma rows_get (f : Fin n → ℕ) (i : Fin n) :
    (rows f)[i.val]?.getD []=List.replicate (f i) true := by simp [rows,i.isLt]
@[simp] lemma rowWords_get (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (rowWords π)[i.val]?.getD []=List.replicate (π i).val true := rows_get _ _

lemma exchange_rowWords (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    ArraySwap.exchange (rowWords π) i.val j.val=rowWords (MonotoneEndpoints.transpose π i j) := by
  simp only [ArraySwap.exchange,rowWords_get]
  apply List.ext_getElem
  · simp [rowWords,rows]
  · intro k hk hk'
    have hk0 : k<n := by simpa [rowWords,rows] using hk
    let x : Fin n := ⟨k,hk0⟩
    by_cases hki : k=i.val
    · have hx : x=i := Fin.ext hki
      subst k
      simp [rowWords,rows,List.getElem_set,MonotoneEndpoints.transpose]
      intro hji
      have he : j=i := Fin.ext hji
      rw [he]
    · by_cases hkj : k=j.val
      · have hx : x=j := Fin.ext hkj
        subst k
        simp [rowWords,rows,List.getElem_set,MonotoneEndpoints.transpose,hx,Fin.ext_iff]
      · have hxi : x≠i := by intro h;exact hki (congrArg Fin.val h)
        have hxj : x≠j := by intro h;exact hkj (congrArg Fin.val h)
        simp [rowWords,rows,List.getElem_set,MonotoneEndpoints.transpose,Equiv.swap_apply_def,hki,hkj,Ne.symm hki,Ne.symm hkj,hxi,hxj,x]

lemma transpose_admissible_iff (E : MonotoneEndpoints n) (π : E.Permutations) (i j : Fin n) :
    E.Admissible (MonotoneEndpoints.transpose π.val i j) ↔
      (E.lo i≤(π.val j).val ∧ (π.val j).val<E.hi i) ∧
      (E.lo j≤(π.val i).val ∧ (π.val i).val<E.hi j) := by
  constructor
  · intro h
    exact ⟨by simpa [MonotoneEndpoints.transpose] using h i,
      by simpa [MonotoneEndpoints.transpose] using h j⟩
  · rintro ⟨hi,hj⟩ k
    by_cases hki : k=i
    · subst k;simpa [MonotoneEndpoints.transpose] using hi
    · by_cases hkj : k=j
      · subst k;simpa [MonotoneEndpoints.transpose] using hj
      · simpa [MonotoneEndpoints.transpose,Equiv.swap_apply_def,hki,hkj] using π.property k

lemma accepts_iff (E : MonotoneEndpoints n) (π : E.Permutations) (i j : Fin n) :
    accepts (rows E.lo) (rows E.hi) (rowWords π.val) i.val j.val=true ↔
      E.Admissible (MonotoneEndpoints.transpose π.val i j) := by
  rw [transpose_admissible_iff]
  simp [accepts,RowCheck.check,IntervalCheck.check]

lemma result_switch (E : MonotoneEndpoints n) (π : E.Permutations) (i j : Fin n) :
    result (rows E.lo) (rows E.hi) (rowWords π.val) i.val j.val=rowWords (E.switch i j π).val := by
  by_cases h : E.Admissible (MonotoneEndpoints.transpose π.val i j)
  · have ha := (accepts_iff E π i j).mpr h
    simp [result,ha,MonotoneEndpoints.switch,restrictedMove,h,exchange_rowWords]
  · have ha : accepts (rows E.lo) (rows E.hi) (rowWords π.val) i.val j.val=false :=
      Bool.eq_false_iff.mpr (fun hh => h ((accepts_iff E π i j).mp hh))
    simp [result,ha,MonotoneEndpoints.switch,restrictedMove,h]

/-- Exact operational correspondence; no unit-cost permutation operation is used. -/
theorem program_switch (g : BitString → ℕ) (E : MonotoneEndpoints n) (π : E.Permutations) (i j : Fin n) :
    ∃t,program.Executes g (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi))
      (encodeBitList (rowWords π.val)) i.val j.val [] [] [] [])
      (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi))
        (encodeBitList (rowWords (E.switch i j π).val)) i.val j.val [] [] [] []) t ∧
      t≤bound (rows E.lo) (rows E.hi) (rowWords π.val) i.val j.val := by
  simpa only [result_switch] using program_executes g (rows E.lo) (rows E.hi) (rowWords π.val) i.val j.val

end HiddenCircuits.Approximation.SamplerRuntime.Switch

namespace HiddenCircuits.Approximation.SamplerRuntime.Switch
open Complexity GraphReduction.MonotoneEndpointEncoding

/-- A coarse polynomial in the vertex count bounds every literal switch scan. -/
lemma bound_polynomial {n : ℕ} (E : MonotoneEndpoints n) (π : E.Permutations) (i j : Fin n) :
    bound (rows E.lo) (rows E.hi) (rowWords π.val) i.val j.val≤1000000*(n+1)^4 := by
  have hl := rows_encoded_length E.lo (fun i => (E.lo_le_hi i).trans (E.hi_le i))
  have hh := rows_encoded_length E.hi E.hi_le
  have hd := rows_encoded_length (fun i => (π.val i).val) (fun i => (π.val i).isLt.le)
  have hi := i.isLt
  have hj := j.isLt
  have hs := HiddenCircuits.Approximation.SamplerRuntime.switch_bound (rows E.lo) (rows E.hi) (rowWords π.val) i.val j.val
  have hbase : (encodeBitList (rows E.lo)).length+(encodeBitList (rows E.hi)).length+
      (encodeBitList (rowWords π.val)).length+i.val+j.val+1≤10*(n+1)^2 := by
    change (encodeBitList (rowWords π.val)).length≤2*n*n+2*n at hd
    nlinarith
  have hp := Nat.pow_le_pow_left hbase 2
  nlinarith
end HiddenCircuits.Approximation.SamplerRuntime.Switch
