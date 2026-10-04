import HiddenCircuits.Circuit.Runtime.SourceCircuitSetup

/-! Initialize the real source-grid clocks, handling zero wires by a literal
empty-header branch and restoring the positive wire-count master. -/
namespace HiddenCircuits.Circuit.Runtime.SourceCircuitEmitter
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock Polynomial

noncomputable def positiveScan : OracleBlock 35 := seq (push 9 true)
  (seq (copyOn 9 0 16 (by decide) (by decide) (by decide))
    (seq (GraphVerifier.Runtime.popDrop 0) (seq (copyOn 0 1 16 (by decide) (by decide) (by decide)) SourceScan.loop)))
noncomputable def scan : OracleBlock 35 := branchPop 9 skip skip positiveScan
noncomputable def scanTime : Polynomial ℕ := SourceScan.loopTime+10*X+22

lemma positiveScan_executes (g : BitString → ℕ) {k : ℕ} (G : MatrixGraph (k+1)) (out : BitString) (swaps : ℕ) :
    ∃ c, positiveScan.Executes g (store 0 0 k G.bits out swaps)
      (store k k (k+1) G.bits ((SourceScan.gateStream (restoringEdges (sourceEdges G)).gates).reverse++out)
        (swaps+2*restoringSwapPairs (sourceEdges G))) c ∧
      c≤SourceScan.loopTime.eval (k+1)+10*k+19 := by
  have h₀ : (push (9 : Fin 36) true).Executes g (store 0 0 k G.bits out swaps)
      (store 0 0 (k+1) G.bits out swaps) 1 := by
    convert push_executes g (9 : Fin 36) true (store 0 0 k G.bits out swaps) using 1
    funext q;fin_cases q <;> simp [store,List.replicate_succ]
  have h₁ : (copyOn (9 : Fin 36) 0 16 (by decide) (by decide) (by decide)).Executes g
      (store 0 0 (k+1) G.bits out swaps) (store (k+1) 0 (k+1) G.bits out swaps) (5*(k+1)+2) := by
    convert copyOn_executes g (9 : Fin 36) 0 16 (by decide) (by decide) (by decide)
      (store 0 0 (k+1) G.bits out swaps) rfl using 1
    · funext q;fin_cases q <;> simp [store]
    · simp [store]
  have h₂ : (GraphVerifier.Runtime.popDrop (0 : Fin 36)).Executes g
      (store (k+1) 0 (k+1) G.bits out swaps) (store k 0 (k+1) G.bits out swaps) 1 := by
    convert GraphVerifier.Runtime.popDrop_executes (0 : Fin 36) g (store (k+1) 0 (k+1) G.bits out swaps) using 1
    funext q;fin_cases q <;> simp [store,List.replicate_succ]
  have h₃ : (copyOn (0 : Fin 36) 1 16 (by decide) (by decide) (by decide)).Executes g
      (store k 0 (k+1) G.bits out swaps) (store k k (k+1) G.bits out swaps) (5*k+2) := by
    convert copyOn_executes g (0 : Fin 36) 1 16 (by decide) (by decide) (by decide)
      (store k 0 (k+1) G.bits out swaps) rfl using 1
    · funext q;fin_cases q <;> simp [store]
    · simp [store]
  obtain ⟨c,hc,hcb⟩ := SourceScan.loop_executes g G out swaps
  have h₄ : SourceScan.loop.Executes g (store k k (k+1) G.bits out swaps)
      (store k k (k+1) G.bits ((SourceScan.gateStream (restoringEdges (sourceEdges G)).gates).reverse++out)
        (swaps+2*restoringSwapPairs (sourceEdges G))) c := by
    convert hc using 1 <;> funext q <;> fin_cases q <;> rfl
  refine ⟨_,seq_executes _ _ g h₀ (seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄))),?_⟩
  omega

theorem scan_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixGraph n) (out : BitString) (swaps : ℕ) :
    ∃ c, scan.Executes g (store 0 0 n G.bits out swaps)
      (store (n-1) (n-1) n G.bits ((SourceScan.gateStream (restoringEdges (sourceEdges G)).gates).reverse++out)
        (swaps+2*restoringSwapPairs (sourceEdges G))) c ∧ c≤scanTime.eval n := by
  cases n with
  | zero =>
    have h := branchPop_empty (9 : Fin 36) skip skip positiveScan g
      (s := store 0 0 0 G.bits out swaps) rfl (skip_executes g _)
    refine ⟨3,?_,?_⟩
    · simpa [sourceEdges,orderedEdges,restoringEdges,ConstraintProgram.identity,SourceScan.gateStream,restoringSwapPairs,encodeBitList] using h
    · simp [scanTime,SourceScan.loopTime]
  | succ k =>
    obtain ⟨c,hc,hcb⟩ := positiveScan_executes g G out swaps
    have hu : Function.update (store 0 0 (k+1) G.bits out swaps) (9 : Fin 36) (List.replicate k true)=
        store 0 0 k G.bits out swaps := by funext q;fin_cases q <;> rfl
    have h := branchPop_true (9 : Fin 36) skip skip positiveScan g
      (s := store 0 0 (k+1) G.bits out swaps) (rest := List.replicate k true) rfl (by rw [hu];exact hc)
    refine ⟨c+2,by simpa using h,?_⟩
    simp only [scanTime,eval_add,eval_mul,eval_X,eval_ofNat]
    omega

lemma positiveScan_queryFree : positiveScan.QueryFree := seq_queryFree _ _ (push_queryFree _ _)
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (GraphVerifier.Runtime.popDrop_queryFree _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) SourceScan.loop_queryFree)))
lemma scan_queryFree : scan.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree positiveScan_queryFree

end HiddenCircuits.Circuit.Runtime.SourceCircuitEmitter
