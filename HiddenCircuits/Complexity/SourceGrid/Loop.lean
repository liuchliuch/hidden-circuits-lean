import HiddenCircuits.Complexity.SourceGrid.Body
import HiddenCircuits.Complexity.GridPrefixStates

/-! The actual nested source-oracle grid loop and exact accumulated numerator. -/
namespace HiddenCircuits.Complexity.SourceGrid
open OracleBlock Polynomial

noncomputable def loop (Q : OracleBlock 29) : OracleBlock 42 := GridRuntime.program (body Q)
noncomputable def loopTime (q : Polynomial ℕ) : Polynomial ℕ :=
  (X+1)^2*(cellTime q+40)+20*X+30

theorem loop_executes (Q : OracleBlock 29) (q : Polynomial ℕ)
    (hQ : ∀ (F : CNFInput) (a b : ℕ), ∃ c,
      Q.Executes GraphInput.independentSetProblem (queryStore (CNFInput.encode F) a b [])
        (queryStore (CNFInput.encode F) a b (F.2.2.encodedCloneQuery a b)) c ∧
      c≤q.eval ((CNFInput.encode F).length+a+b)) (F : CNFInput) :
    ∃ c, (loop Q).Executes GraphInput.independentSetProblem
      (GridRuntime.initialStore F.1 F.2.1 (frame (persistent F 0)))
      (GridRuntime.initialStore F.1 F.2.1 (frame (persistent F
        (gridNumerator F.1 F.2.1 (fun i j => (F.2.2.cloneCount i.val j.val : ℤ)))))) c ∧
      c≤(loopTime q).eval (CNFInput.encode F).length := by
  have hb : ∀ (i : Fin (F.1+1)) (j : Fin (F.2.1+1)) inner outer, ∃ c,
      (body Q).Executes GraphInput.independentSetProblem
        (GridRuntime.store F.1 F.2.1 i.val j.val inner outer (frame (persistent F
          (gridPrefixSum F.1 F.2.1 (fun a b => (F.2.2.cloneCount a.val b.val : ℤ)) i.val j.val))))
        (GridRuntime.store F.1 F.2.1 i.val j.val inner outer (frame (persistent F
          (gridPrefixSum F.1 F.2.1 (fun a b => (F.2.2.cloneCount a.val b.val : ℤ)) i.val j.val+
            gridTerm F.1 F.2.1 i j (F.2.2.cloneCount i.val j.val))))) c ∧
      c≤(cellTime q).eval (CNFInput.encode F).length := by
    intro i j inner outer
    exact body_executes Q q hQ F i j (gridPrefix F.1 F.2.1 i.val j.val)
      (gridPrefix_length F.1 F.2.1 i.val j.val) inner outer
  obtain ⟨c,hc,hcb⟩ := gridProgram_accumulator (body Q) GraphInput.independentSetProblem
    F.1 F.2.1 ((cellTime q).eval (CNFInput.encode F).length)
    (fun i j => (F.2.2.cloneCount i.val j.val : ℤ)) (fun acc => frame (persistent F acc)) hb
  refine ⟨c,hc,hcb.trans ?_⟩
  have hlen := CNFInput.encode_length_lower F
  simpa only [loopTime,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one] using
    GridRuntime.programCost_bound F.1 F.2.1 ((cellTime q).eval (CNFInput.encode F).length)
      (CNFInput.encode F).length (by omega) (by omega)

end HiddenCircuits.Complexity.SourceGrid
