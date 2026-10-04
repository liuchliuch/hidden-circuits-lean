import HiddenCircuits.Complexity.CanonicalSubstitution.Body
import HiddenCircuits.Complexity.GridPrefixStates

/-! Execute the concrete canonical
solver-substituted body across the actual inclusive grid loop. -/
namespace HiddenCircuits.Complexity.CanonicalSubstitution
open OracleBlock Polynomial
variable {k : ℕ}

noncomputable def loop (C : OracleBlock k) : OracleBlock (k+43) := GridRuntime.program (body C)
noncomputable def loopTime (q : Polynomial ℕ) : Polynomial ℕ :=
  (X+1)^2*(cellTime (k := k) q+40)+20*X+30

theorem loop_executes (C : OracleBlock k) (q : Polynomial ℕ) (g : BitString → ℕ)
    (hC : ∀ G : GraphInput, ∃ s : Store k, ∃ c,
      C.Executes g (Function.update (fun _ => []) 0 (GraphInput.encode G)) s c ∧
      s 0=Computability.encodeNat G.2.independentCount ∧ c≤q.eval (GraphInput.encode G).length)
    (F : CNFInput) :
    ∃ c, (loop C).Executes g
      (extend (GridRuntime.initialStore F.1 F.2.1 (SourceGrid.frame (SourceGrid.persistent F 0))))
      (extend (GridRuntime.initialStore F.1 F.2.1 (SourceGrid.frame (SourceGrid.persistent F
        (gridNumerator F.1 F.2.1 (fun i j => (F.2.2.cloneCount i.val j.val : ℤ))))))) c ∧
      c≤(loopTime (k := k) q).eval (CNFInput.encode F).length := by
  have hb : ∀ (i : Fin (F.1+1)) (j : Fin (F.2.1+1)) inner outer, ∃ c,
      (body C).Executes g
        (GridRuntime.store F.1 F.2.1 i.val j.val inner outer (widenFrame (SourceGrid.frame (SourceGrid.persistent F
          (gridPrefixSum F.1 F.2.1 (fun a b => (F.2.2.cloneCount a.val b.val : ℤ)) i.val j.val)))))
        (GridRuntime.store F.1 F.2.1 i.val j.val inner outer (widenFrame (SourceGrid.frame (SourceGrid.persistent F
          (gridPrefixSum F.1 F.2.1 (fun a b => (F.2.2.cloneCount a.val b.val : ℤ)) i.val j.val+
            gridTerm F.1 F.2.1 i j (F.2.2.cloneCount i.val j.val)))))) c ∧
      c≤(cellTime (k := k) q).eval (CNFInput.encode F).length := by
    intro i j inner outer
    have h := body_executes C q g hC F i j (gridPrefix F.1 F.2.1 i.val j.val)
      (gridPrefix_length F.1 F.2.1 i.val j.val) inner outer
    simpa only [SourceGrid.store, extend_grid_store] using h
  obtain ⟨c,hc,hcb⟩ := gridProgram_accumulator (body C) g
    F.1 F.2.1 ((cellTime (k := k) q).eval (CNFInput.encode F).length)
    (fun i j => (F.2.2.cloneCount i.val j.val : ℤ))
    (fun acc => widenFrame (SourceGrid.frame (SourceGrid.persistent F acc))) hb
  refine ⟨c,?_,hcb.trans ?_⟩
  · simpa only [loop, extend_grid_initial] using hc
  · have hlen := CNFInput.encode_length_lower F
    simpa only [loopTime,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one] using
      GridRuntime.programCost_bound F.1 F.2.1 ((cellTime (k := k) q).eval (CNFInput.encode F).length)
        (CNFInput.encode F).length (by omega) (by omega)

end HiddenCircuits.Complexity.CanonicalSubstitution
