import HiddenCircuits.Complexity.CanonicalSubstitution.Loop

/-! Operational canonical graph-oracle substitution. The theorem constructs all
source and solver code and derives #P hardness from an actual canonical graph
solver, without a postulated reduction-transitivity rule. -/
namespace HiddenCircuits.Complexity
namespace CanonicalSubstitution
open OracleBlock Polynomial
variable {k : ℕ}

lemma source_finish_queryFree : SourceGrid.finish.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ FinalCountRuntime.program_queryFree)
      (seq_queryFree _ _ (clear_queryFree _) (moveOn_queryFree _ _ _ _ _ _))))

noncomputable def program (C : OracleBlock k) : OracleBlock (k+43) :=
  seq (liftBase SourceGrid.setup) (seq (loop C) (liftBase SourceGrid.finish))
noncomputable def time (q : Polynomial ℕ) : Polynomial ℕ := SourceGrid.setupTime+loopTime (k := k) q+SourceGrid.finishTime+4

theorem program_executes (C : OracleBlock k) (q : Polynomial ℕ) (g : BitString → ℕ)
    (hC : ∀ G : GraphInput, ∃ s : Store k, ∃ c,
      C.Executes g (Function.update (fun _ => []) 0 (GraphInput.encode G)) s c ∧
      s 0=Computability.encodeNat G.2.independentCount ∧ c≤q.eval (GraphInput.encode G).length)
    (F : CNFInput) :
    ∃ s : Store (k+43), ∃ c, (program C).Executes g (Function.update (fun _ => []) 0 (CNFInput.encode F)) s c ∧
      s 0=Computability.encodeNat F.2.2.satCount ∧ c≤(time (k := k) q).eval (CNFInput.encode F).length := by
  obtain ⟨a,ha,hab⟩ := SourceGrid.setup_executes g F
  have h₀ := liftBase_executes (k := k) SourceGrid.setup g _ _ _ ha
  rw [extend_initial] at h₀
  obtain ⟨b,hb,hbb⟩ := loop_executes C q g hC F
  obtain ⟨s,c,hc,ho,hcb⟩ := SourceGrid.finish_executes F
  have hf : SourceGrid.finish.Executes g
      (GridRuntime.initialStore F.1 F.2.1 (SourceGrid.frame (SourceGrid.persistent F
        (gridNumerator F.1 F.2.1 (fun i j => (F.2.2.cloneCount i.val j.val : ℤ)))))) s c :=
    OracleMachine.Steps.changeOracle source_finish_queryFree g hc
  have h₂ := liftBase_executes (k := k) SourceGrid.finish g _ _ _ hf
  refine ⟨extend s,a+(b+c+2)+2,seq_executes _ _ g h₀ (seq_executes _ _ g hb h₂),?_,?_⟩
  · have h := extend_base (k := k) s 0
    rw [base_zero] at h
    exact h.trans ho
  · simp only [time,eval_add,eval_ofNat]
    omega

end CanonicalSubstitution

/-- An actual canonical graph solver block, with proved target-oracle executions
and polynomial bit time, suffices for #P hardness of that target. All oracle
substitution, canonical-query and work-cleanup obligations are proved above. -/
theorem sharpPHard_of_canonical_independent_block {k : ℕ} (g : BitString → ℕ)
    (C : OracleBlock k) (q : Polynomial ℕ)
    (hC : ∀ G : GraphInput, ∃ s : OracleBlock.Store k, ∃ c,
      C.Executes g (Function.update (fun _ => []) 0 (GraphInput.encode G)) s c ∧
      s 0=Computability.encodeNat G.2.independentCount ∧ c≤q.eval (GraphInput.encode G).length) : SharpPHard g :=
  sharpPHard_of_canonical_sat_block g (CanonicalSubstitution.program C) (CanonicalSubstitution.time (k := k) q)
    (CanonicalSubstitution.program_executes C q g hC)

end HiddenCircuits.Complexity
