import HiddenCircuits.Complexity.CanonicalSubstitution.Stores

/-! Physically clean a canonical graph solver's private work stacks. The
additional time is derived from its actual execution storage bound. -/
namespace HiddenCircuits.Complexity.CanonicalSubstitution
open OracleBlock Polynomial
variable {k : ℕ}

noncomputable def cleanSolver (C : OracleBlock k) : OracleBlock k := seq C (cleanup 0)
noncomputable def cleanSolverTime (q : Polynomial ℕ) : Polynomial ℕ :=
  q+C (k+1)*(X+q+3)+3

theorem cleanSolver_executes (C : OracleBlock k) (q : Polynomial ℕ) (g : BitString → ℕ)
    (hC : ∀ G : GraphInput, ∃ s : Store k, ∃ c,
      C.Executes g (Function.update (fun _ => []) 0 (GraphInput.encode G)) s c ∧
      s 0=Computability.encodeNat G.2.independentCount ∧ c≤q.eval (GraphInput.encode G).length)
    (G : GraphInput) :
    ∃ c, (cleanSolver C).Executes g (Function.update (fun _ => []) 0 (GraphInput.encode G))
      (Function.update (fun _ => []) 0 (Computability.encodeNat G.2.independentCount)) c ∧
      c≤(cleanSolverTime (k := k) q).eval (GraphInput.encode G).length := by
  obtain ⟨s,c,hc,ho,hcb⟩ := hC G
  have hs := hc.stack_bound (C.machine.init_stack_bound (GraphInput.encode G))
  obtain ⟨d,hd,hdb⟩ := cleanup_executes g (0 : Fin (k+1)) s ((GraphInput.encode G).length+c) hs
  rw [ho] at hd
  refine ⟨c+d+2,seq_executes _ _ g hc hd,?_⟩
  have hm := Nat.mul_le_mul_left (k+1) (show (GraphInput.encode G).length+c+3≤
      (GraphInput.encode G).length+q.eval (GraphInput.encode G).length+3 by omega)
  simp only [cleanSolverTime,eval_add,eval_mul,eval_C,eval_X,eval_ofNat]
  omega

end HiddenCircuits.Complexity.CanonicalSubstitution
