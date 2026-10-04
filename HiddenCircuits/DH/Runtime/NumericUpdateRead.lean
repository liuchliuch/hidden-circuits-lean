import HiddenCircuits.DH.Runtime.NumericUpdateBounds

/-! The four actual indexed reads for a pruning action. -/
namespace HiddenCircuits.DH.Runtime.NumericUpdate
open Complexity Complexity.OracleBlock NumericStateModel NumericEncoding PruningModel
set_option maxHeartbeats 2000000

def data {n : ℕ} (s : NumericStateModel.State n) (a : Action n)
    (left right aa bb row sum mark : BitString) : Store 45:=
  state n a.keep.val a.removed.val (PairCheck.liveBits s.alive) (sizeBits s) (tableBits s) left right aa bb row sum mark
def loaded {n : ℕ} (s : NumericStateModel.State n) (a : Action n) : Store 45:=
  data s a (rowBits s.rows[a.keep.val]) (rowBits s.rows[a.removed.val])
    (List.replicate s.sizes[a.keep.val] true) (List.replicate s.sizes[a.removed.val] true) [] [] []
def merged {n : ℕ} (s : NumericStateModel.State n) (a : Action n) : Store 45:=
  data s a (rowBits s.rows[a.keep.val]) (rowBits s.rows[a.removed.val])
    (List.replicate s.sizes[a.keep.val] true) (List.replicate s.sizes[a.removed.val] true)
    (rowBits (CoefficientModel.mergeRow n a.kind s.sizes[a.keep.val] s.sizes[a.removed.val] s.rows[a.keep.val] s.rows[a.removed.val])) [] []

lemma reads_executes (g : BitString→ ℕ) {n : ℕ} (s : NumericStateModel.State n) (h : Safe s) (a : Action n) :
    ∃t,reads.Executes g (store n a.keep.val a.removed.val (PairCheck.liveBits s.alive) (sizeBits s) (tableBits s))
      (loaded s a) t ∧t≤ 2000*(basePolynomial.eval n)^2 := by
  let s0:=store n a.keep.val a.removed.val (PairCheck.liveBits s.alive) (sizeBits s) (tableBits s)
  let s1:=data s a (rowBits s.rows[a.keep.val]) [] [] [] [] [] []
  let s2:=data s a (rowBits s.rows[a.keep.val]) (rowBits s.rows[a.removed.val]) [] [] [] [] []
  let s3:=data s a (rowBits s.rows[a.keep.val]) (rowBits s.rows[a.removed.val]) (List.replicate s.sizes[a.keep.val] true) [] [] [] []
  let s4:=data s a (rowBits s.rows[a.keep.val]) (rowBits s.rows[a.removed.val]) (List.replicate s.sizes[a.keep.val] true) (List.replicate s.sizes[a.removed.val] true) [] [] []
  obtain ⟨c1,hc1,hb1⟩:=WordArray.readOn_executes leftMap g s0 (tableWords s) a.keep.val
    (by funext q;fin_cases q <;> rfl)
  rw [tableWords_get s a.keep] at hc1
  have h1:(WordArray.readOn leftMap).Executes g s0 s1 c1:=by
    convert hc1 using 1;funext q;fin_cases q <;> rfl
  obtain ⟨c2,hc2,hb2⟩:=WordArray.readOn_executes rightMap g s1 (tableWords s) a.removed.val
    (by funext q;fin_cases q <;> rfl)
  rw [tableWords_get s a.removed] at hc2
  have h2:(WordArray.readOn rightMap).Executes g s1 s2 c2:=by
    convert hc2 using 1;funext q;fin_cases q <;> rfl
  obtain ⟨c3,hc3,hb3⟩:=WordArray.readOn_executes sizeLeftMap g s2 (sizeWords s) a.keep.val
    (by funext q;fin_cases q <;> rfl)
  rw [sizeWords_get s a.keep] at hc3
  have h3:(WordArray.readOn sizeLeftMap).Executes g s2 s3 c3:=by
    convert hc3 using 1;funext q;fin_cases q <;> rfl
  obtain ⟨c4,hc4,hb4⟩:=WordArray.readOn_executes sizeRightMap g s3 (sizeWords s) a.removed.val
    (by funext q;fin_cases q <;> rfl)
  rw [sizeWords_get s a.removed] at hc4
  have h4:(WordArray.readOn sizeRightMap).Executes g s3 s4 c4:=by
    convert hc4 using 1;funext q;fin_cases q <;> rfl
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  obtain ⟨hn,hL,hS,hT,hR⟩:=base_bounds s h
  have hu:a.keep.val≤ basePolynomial.eval n:=by have:=a.keep.isLt;omega
  have hv:a.removed.val≤ basePolynomial.eval n:=by have:=a.removed.isLt;omega
  have hD:1≤ basePolynomial.eval n:=by omega
  have b1:=hb1.trans (lookup_bound _ _ _ hT hu hD)
  have b2:=hb2.trans (lookup_bound _ _ _ hT hv hD)
  have b3:=hb3.trans (lookup_bound _ _ _ hS hu hD)
  have b4:=hb4.trans (lookup_bound _ _ _ hS hv hD)
  nlinarith

lemma loaded_bound {n : ℕ} (s : NumericStateModel.State n) (h : Safe s) (a : Action n) :
    ∀q,(loaded s a q).length≤ basePolynomial.eval n := by
  obtain ⟨hn,hL,hS,hT,hR⟩:=base_bounds s h
  have hu:=a.keep.isLt
  have hv:=a.removed.isLt
  have hA:=h.size_bound a.keep
  have hB:=h.size_bound a.removed
  intro q
  fin_cases q <;> simp [loaded,data,state]
  all_goals first | exact hL | exact hS | exact hT | exact hR a.keep | exact hR a.removed | omega

lemma merge_executes (g : BitString→ ℕ) {n : ℕ} (s : NumericStateModel.State n) (h : Safe s) (a : Action n) :
    ∃t,(CoefficientRowRuntime.on rowMap a.kind).Executes g (loaded s a) (merged s a) t ∧
      t≤ CoefficientRowRuntime.time.eval (3*basePolynomial.eval n) := by
  obtain ⟨c,hc,hcb⟩:=CoefficientRowRuntime.on_executes rowMap g (loaded s a) n a.kind
    s.sizes[a.keep.val] s.sizes[a.removed.val] s.rows[a.keep.val] s.rows[a.removed.val]
    (h.size_bound a.keep) (h.size_bound a.removed) (h.row_lengths a.keep) (h.row_lengths a.removed)
    (by funext q;fin_cases q <;> rfl)
  rw [runtime_row s h a] at hc
  refine ⟨c,?_,?_⟩
  · convert hc using 1;funext q;fin_cases q <;> rfl
  · apply hcb.trans
    apply polynomial_nat_eval_mono
    obtain ⟨hn,_,_,_,hR⟩:=base_bounds s h
    have hL:=hR a.keep
    have hR':=hR a.removed
    change n+(rowBits s.rows[a.keep.val]).length+(rowBits s.rows[a.removed.val]).length+1≤ 3*basePolynomial.eval n
    omega
end HiddenCircuits.DH.Runtime.NumericUpdate
