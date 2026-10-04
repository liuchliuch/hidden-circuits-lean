import HiddenCircuits.Complexity.GraphVerifier.MatchingRowsRuntime

namespace HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
open OracleBlock

 theorem count_ofFn_one_iff {n : ℕ} (f : Fin n → Bool) :
    (List.ofFn f).count true=1 ↔ ∃! j, f j=true := by
  have hc : (Finset.univ.filter (fun j => f j=true)).card=(List.ofFn f).count true := by
    simpa using Fin.card_filter_univ_eq_vector_get_eq_count true (List.Vector.ofFn f)
  rw [←hc,Finset.card_eq_one]
  constructor
  · rintro ⟨j,hj⟩
    have hf : f j=true := by
      have hm : j∈Finset.univ.filter (fun j => f j=true) := by rw [hj];simp
      simpa using hm
    refine ⟨j,hf,?_⟩
    intro k hk
    have hm : k∈Finset.univ.filter (fun j => f j=true) := by simp [hk]
    simpa [hj] using hm
  · rintro ⟨j,hj,hu⟩
    refine ⟨j,?_⟩
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact ⟨fun hk => hu k hk,fun hk => hk ▸ hj⟩

 theorem take_drop_ofFn (data : BitString) (s n : ℕ) (hlen : s+n≤data.length) :
    (data.drop s).take n=List.ofFn (fun j : Fin n => bitAt data (s+j.val)) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_ofFn]
    omega
  · intro k hk hk'
    have hk0 : k<n := by simpa using hk'
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    rw [bitAt_get data _ (by omega)]
    rfl

 theorem rowFlag_iff (n : ℕ) (data : BitString) (i : Fin n) (hlen : n*n≤data.length) :
    rowFlag n data i.val=true ↔ ∃! j : Fin n, flatEdge n data i j=true := by
  unfold rowFlag
  rw [decide_eq_true_eq,take_drop_ofFn data (n*i.val) n (by
    have hh := Nat.mul_le_mul_left n (show i.val+1≤n by omega)
    nlinarith),count_ofFn_one_iff]
  change (∃! j : Fin n,bitAt data (n*i.val+j.val)=true) ↔
    ∃! j : Fin n,bitAt data (j.val+n*i.val)=true
  simp only [Nat.add_comm]

 theorem allRowsValue_iff (n : ℕ) (data : BitString) (a : Bool) (hlen : n*n≤data.length) :
    allRowsValue n data 0 n a=(a && decide (RowsOne n data)) := by
  rw [allRowsValue_all,←List.range_eq_range']
  apply congrArg (fun b => a && b)
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true,List.mem_range,decide_eq_true_eq]
  constructor
  · intro h i
    exact (rowFlag_iff n data i hlen).mp (h i.val i.isLt)
  · intro h i hi
    exact (rowFlag_iff n data ⟨i,hi⟩ hlen).mpr (h ⟨i,hi⟩)

/-- Exact matching-row semantics of the actual six-stack repeated scanner. -/
theorem oneRows_correct (g : BitString → ℕ) (n : ℕ) (data : BitString) (a : Bool)
    (hlen : n*n≤data.length) :
    oneRowsBlock.Executes g (oneRowsStore n [] data [a] [])
      (oneRowsStore n [] (data.drop (n*n)) [a && decide (RowsOne n data)] []) (7*n*n+14*n+5) := by
  simpa [allRowsValue_iff n data a hlen] using oneRows_executes g n data a hlen

end HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
