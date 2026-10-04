import HiddenCircuits.DH.Runtime.FinalProduct
import HiddenCircuits.DH.Runtime.StorageBounds

/-! Source-state invariants discharge every literal final-product bit and time bound. -/
namespace HiddenCircuits.DH.Runtime.FinalProduct
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 800000

def numericRows {n : ℕ} (s : NumericStateModel.State n) : Rows :=
  (List.finRange n).map (fun v=>(s.alive[v.val],s.rows[v.val]))
lemma vector_values {α : Type*} {n : ℕ} (v : Vector α n) :
    (List.finRange n).map (fun i=>v[i.val])=v.toList := by
  rw [←List.ofFn_eq_map]
  simpa only [Vector.toList_ofFn] using congrArg Vector.toList (Vector.ofFn_getElem (xs:=v))
lemma numericRows_length {n : ℕ} (s : NumericStateModel.State n) : (numericRows s).length=n := by
  simp [numericRows]
lemma numericRows_live {n : ℕ} (s : NumericStateModel.State n) : live (numericRows s)=PairCheck.liveBits s.alive := by
  simp only [live,numericRows,List.map_map,Function.comp_def,PairCheck.liveBits,PairCheck.liveWords]
  rw [←vector_values s.alive,List.map_map]
  rfl
lemma numericRows_table {n : ℕ} (s : NumericStateModel.State n) : table (numericRows s)=NumericEncoding.tableBits s := by
  simp only [table,numericRows,List.map_map,Function.comp_def,NumericEncoding.tableBits,NumericEncoding.tableWords]
  rw [←vector_values s.rows,List.map_map]
  rfl
lemma numericRows_product {n : ℕ} (s : NumericStateModel.State n) : product (numericRows s)=NumericStateModel.result s := by
  simp only [product,numericRows,List.map_map,Function.comp_def,factor,NumericStateModel.result]
lemma numericRows_nonempty {n : ℕ} (s : NumericStateModel.State n) (hs : NumericStateModel.Safe s) :
    ∀x∈numericRows s,x.2≠[] := by
  intro x hx
  obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hx
  have hl:=hs.row_lengths v
  intro he
  change s.rows[v.val]=[] at he
  rw [he] at hl
  simp at hl
lemma numericRows_bound {n : ℕ} (s : NumericStateModel.State n) (hs : NumericStateModel.Safe s) :
    ∀x∈numericRows s,(NumericEncoding.rowBits x.2).length≤NumericEncoding.rowBound n := by
  intro x hx
  obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hx
  exact NumericEncoding.safe_row_bound hs v
lemma numericRows_factor_bound {n : ℕ} (s : NumericStateModel.State n) (hs : NumericStateModel.Safe s) :
    ∀z∈factors (numericRows s),z.natAbs≤2^((n+1)^2) := by
  intro z hz
  obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hz
  obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hx
  simp only [factor,Int.natAbs_natCast]
  split_ifs
  · exact hs.coefficient_bound v 0
  · exact Nat.one_le_pow _ _ (by decide)
lemma numericRows_bitBound {n : ℕ} (s : NumericStateModel.State n) (hs : NumericStateModel.Safe s) :
    ProductBitBound (((n+1)^2)*n+2) 1 (factors (numericRows s)) := by
  have h:=productBitBound_of_abs 0 ((n+1)^2) 1 (factors (numericRows s))
    (by simp) (numericRows_factor_bound s hs)
  simpa only [factors,List.length_map,numericRows_length,zero_add] using h

noncomputable def bitPolynomial : Polynomial ℕ := (X+1)^2*X+2
noncomputable def rowPolynomial : Polynomial ℕ := 2*(X+1)*((X+1)^2+3)
noncomputable def numericTime : Polynomial ℕ :=
  X*(operationTime.comp (bitPolynomial+rowPolynomial)+12*rowPolynomial+52)+6*bitPolynomial+22

lemma numeric_executes (g : BitString→ℕ) {n : ℕ} (s : NumericStateModel.State n) (hs : NumericStateModel.Safe s) :
    ∃c,program.Executes g (initial (PairCheck.liveBits s.alive) (NumericEncoding.tableBits s))
      (output (NumericStateModel.result s)) c ∧ c≤numericTime.eval n := by
  obtain ⟨c,hc,hb⟩:=program_executes g (numericRows s) (((n+1)^2)*n+2) (NumericEncoding.rowBound n)
    (numericRows_nonempty s hs) (numericRows_bound s hs) (numericRows_bitBound s hs)
  refine ⟨c,?_,?_⟩
  · simpa only [numericRows_live,numericRows_table,numericRows_product] using hc
  · rw [numericRows_length] at hb
    convert hb using 1
    simp only [numericTime,bitPolynomial,rowPolynomial,eval_add,eval_mul,eval_comp,eval_X,eval_pow,
      eval_ofNat,eval_one,bodyBound,NumericEncoding.rowBound]
    ring

lemma on_executes {k : ℕ} (φ : Fin 14 ↪ Fin (k+1)) (g : BitString→ℕ) {n : ℕ}
    (s : NumericStateModel.State n) (hs : NumericStateModel.Safe s) (before after : Store k)
    (hbefore : before∘φ=initial (PairCheck.liveBits s.alive) (NumericEncoding.tableBits s))
    (hafter : after∘φ=output (NumericStateModel.result s))
    (hframe : ∀j,(∀i,φ i≠j)→after j=before j) :
    ∃c,(on φ).Executes g before after c ∧ c≤numericTime.eval n := by
  obtain ⟨c,hc,hb⟩:=numeric_executes g s hs
  exact ⟨c,rename_executes_to _ φ g hc hbefore hafter hframe,hb⟩
end HiddenCircuits.DH.Runtime.FinalProduct
