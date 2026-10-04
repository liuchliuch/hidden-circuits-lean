import HiddenCircuits.DH.Runtime.NumericUpdateRead

/-! Unary size addition and the three actual array
writes. The newly computed row bound is derived from its real execution. -/
namespace HiddenCircuits.DH.Runtime.NumericUpdate
open Complexity Complexity.OracleBlock NumericStateModel NumericEncoding PruningModel
set_option maxHeartbeats 2000000

def mergedRow {n : ℕ} (s : NumericStateModel.State n) (a : Action n) : BitString:=
  rowBits (CoefficientModel.mergeRow n a.kind s.sizes[a.keep.val] s.sizes[a.removed.val] s.rows[a.keep.val] s.rows[a.removed.val])
def prepared {n : ℕ} (s : NumericStateModel.State n) (a : Action n) : Store 45:=
  data s a (rowBits s.rows[a.keep.val]) (rowBits s.rows[a.removed.val])
    (List.replicate s.sizes[a.keep.val] true) (List.replicate s.sizes[a.removed.val] true)
    (mergedRow s a) (List.replicate (s.sizes[a.keep.val]+s.sizes[a.removed.val]) true) [false]
def finished {n : ℕ} (s : NumericStateModel.State n) (a : Action n) : Store 45:=
  state n a.keep.val a.removed.val (PairCheck.liveBits (update s a).alive) (sizeBits (update s a)) (tableBits (update s a))
    (rowBits s.rows[a.keep.val]) (rowBits s.rows[a.removed.val])
    (List.replicate s.sizes[a.keep.val] true) (List.replicate s.sizes[a.removed.val] true)
    (mergedRow s a) (List.replicate (s.sizes[a.keep.val]+s.sizes[a.removed.val]) true) [false]

lemma prepare_executes (g : BitString→ ℕ) {n : ℕ} (s : NumericStateModel.State n) (a : Action n) :
    (seq sumSizes (push 12 false)).Executes g (merged s a) (prepared s a)
      (5*s.sizes[a.keep.val]+5*s.sizes[a.removed.val]+9) := by
  let A:=s.sizes[a.keep.val]
  let B:=s.sizes[a.removed.val]
  let s1:=Function.update (merged s a) 11 (List.replicate A true)
  let s2:=Function.update (merged s a) 11 (List.replicate (A+B) true)
  have h1:(copyOn (8:Fin 46) 11 13 (by decide) (by decide) (by decide)).Executes g (merged s a) s1 (5*A+2):=by
    convert copyOn_executes g (8:Fin 46) 11 13 (by decide) (by decide) (by decide) (merged s a) rfl using 1
    · funext q;fin_cases q <;> simp [s1,merged,data,state,A]
    · simp [merged,data,state,A]
  have h2:(copyOn (9:Fin 46) 11 13 (by decide) (by decide) (by decide)).Executes g s1 s2 (5*B+2):=by
    convert copyOn_executes g (9:Fin 46) 11 13 (by decide) (by decide) (by decide) s1 rfl using 1
    · funext q;fin_cases q <;> simp [s1,s2,merged,data,state,A,B,←List.replicate_add,Nat.add_comm]
    · simp [s1,merged,data,state,B]
  have h3:(push (12:Fin 46) false).Executes g s2 (prepared s a) 1:=by
    convert push_executes g (12:Fin 46) false s2 using 1
    funext q;fin_cases q <;> rfl
  convert seq_executes _ _ g (seq_executes _ _ g h1 h2) h3 using 1 <;> omega

lemma writes_executes (g : BitString→ ℕ) {n : ℕ} (s : NumericStateModel.State n) (h : Safe s) (a : Action n)
    (hrow:(mergedRow s a).length≤ envelope.eval n) :
    ∃t,writes.Executes g (prepared s a) (finished s a) t ∧t≤ 8000*(envelope.eval n)^2 := by
  let s1:=state n a.keep.val a.removed.val (PairCheck.liveBits s.alive) (sizeBits s) (tableBits (update s a))
    (rowBits s.rows[a.keep.val]) (rowBits s.rows[a.removed.val])
    (List.replicate s.sizes[a.keep.val] true) (List.replicate s.sizes[a.removed.val] true)
    (mergedRow s a) (List.replicate (s.sizes[a.keep.val]+s.sizes[a.removed.val]) true) [false]
  let s2:=state n a.keep.val a.removed.val (PairCheck.liveBits s.alive) (sizeBits (update s a)) (tableBits (update s a))
    (rowBits s.rows[a.keep.val]) (rowBits s.rows[a.removed.val])
    (List.replicate s.sizes[a.keep.val] true) (List.replicate s.sizes[a.removed.val] true)
    (mergedRow s a) (List.replicate (s.sizes[a.keep.val]+s.sizes[a.removed.val]) true) [false]
  obtain ⟨c1,hc1,hb1⟩:=WordArray.updateOn_executes tableMap g (prepared s a) (tableWords s) a.keep.val (mergedRow s a)
    (by funext q;fin_cases q <;> rfl)
  have ht1:(WordArray.updateOn tableMap).Executes g (prepared s a) s1 c1:=by
    convert hc1 using 1
    funext q;fin_cases q <;> simp [s1,prepared,data,state,tableMap,update_table,mergedRow]
  obtain ⟨c2,hc2,hb2⟩:=WordArray.updateOn_executes sizesMap g s1 (sizeWords s) a.keep.val
    (List.replicate (s.sizes[a.keep.val]+s.sizes[a.removed.val]) true) (by funext q;fin_cases q <;> rfl)
  have ht2:(WordArray.updateOn sizesMap).Executes g s1 s2 c2:=by
    convert hc2 using 1
    funext q;fin_cases q <;> simp [s1,s2,state,sizesMap,update_sizes]
  obtain ⟨c3,hc3,hb3⟩:=WordArray.updateOn_executes liveMap g s2 (PairCheck.liveWords s.alive) a.removed.val [false]
    (by funext q;fin_cases q <;> rfl)
  have ht3:(WordArray.updateOn liveMap).Executes g s2 (finished s a) c3:=by
    convert hc3 using 1
    funext q;fin_cases q <;> simp [s2,finished,state,liveMap,update_live]
  refine ⟨_,seq_executes _ _ g ht1 (seq_executes _ _ g ht2 ht3),?_⟩
  obtain ⟨hn,hL,hS,hT,hR⟩:=base_bounds s h
  have hE:=envelope_base n
  have hE1:1≤ envelope.eval n:=by omega
  have hu:a.keep.val≤ envelope.eval n:=by have:=a.keep.isLt;omega
  have hv:a.removed.val≤ envelope.eval n:=by have:=a.removed.isLt;omega
  have hA:=h.size_bound a.keep
  have hB:=h.size_bound a.removed
  have hb1':c1≤ 2500*(envelope.eval n)^2:=hb1.trans (update_bound _ _ _ _ (hT.trans (by omega)) hu (by omega) hE1)
  have hb2':c2≤ 2500*(envelope.eval n)^2:=hb2.trans (update_bound _ _ _ _ (hS.trans (by omega)) hu
    (by simp only [List.length_replicate];omega) hE1)
  have hb3':c3≤ 2500*(envelope.eval n)^2:=hb3.trans (update_bound _ _ _ _ (hL.trans (by omega)) hv (by simp;omega) hE1)
  nlinarith
end HiddenCircuits.DH.Runtime.NumericUpdate
