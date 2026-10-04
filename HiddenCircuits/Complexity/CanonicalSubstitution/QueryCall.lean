import HiddenCircuits.Complexity.CanonicalSubstitution.CleanSolver

/-! Replace one graph-oracle instruction by actual solver code on disjoint
private work tapes, including copying, cleanup, answer movement and sign. -/
namespace HiddenCircuits.Complexity.CanonicalSubstitution
open OracleBlock BinaryArithmetic
variable {k : ℕ}

noncomputable def call (C : OracleBlock k) : OracleBlock (k+43) :=
  seq (copyOn (baseEmbedding 15) (workEmbedding 0) (baseEmbedding 17)
    (base_ne_work _ _) (baseEmbedding.injective.ne (by decide)) (base_ne_work _ _).symm)
    (seq (rename (cleanSolver C) workEmbedding) (seq (clear (baseEmbedding 15))
      (seq (moveOn (workEmbedding 0) (baseEmbedding 15) (baseEmbedding 17)
        (base_ne_work _ _).symm (base_ne_work _ _).symm (baseEmbedding.injective.ne (by decide)))
        (push (baseEmbedding 15) false))))

theorem call_executes (C : OracleBlock k) (q : Polynomial ℕ) (g : BitString → ℕ)
    (hC : ∀ G : GraphInput, ∃ s : Store k, ∃ c,
      C.Executes g (Function.update (fun _ => []) 0 (GraphInput.encode G)) s c ∧
      s 0=Computability.encodeNat G.2.independentCount ∧ c≤q.eval (GraphInput.encode G).length)
    (s : Store 42) (G : GraphInput) (hx : s 15=GraphInput.encode G) (ht : s 17=[]) :
    ∃ cost, (call C).Executes g (extend s)
      (extend (Function.update s 15 (signedBits (G.2.independentCount : ℤ)))) cost ∧
      cost≤(cleanSolverTime (k := k) q).eval (GraphInput.encode G).length+
        6*(GraphInput.encode G).length+6*(Computability.encodeNat G.2.independentCount).length+17 := by
  let input : Store k := Function.update (fun _ => []) 0 (GraphInput.encode G)
  let output : Store k := Function.update (fun _ => []) 0 (Computability.encodeNat G.2.independentCount)
  have h₀ : (copyOn (baseEmbedding 15) (workEmbedding 0) (baseEmbedding 17)
      (base_ne_work _ _) (baseEmbedding.injective.ne (by decide)) (base_ne_work _ _).symm).Executes g
      (extend s) (combined s input) (5*(GraphInput.encode G).length+2) := by
    simpa only [extend,combined_base,combined_work,hx,List.append_nil,update_work] using
      copyOn_executes g (baseEmbedding 15) (workEmbedding 0) (baseEmbedding 17)
        (base_ne_work _ _) (baseEmbedding.injective.ne (by decide)) (base_ne_work _ _).symm (extend (k := k) s)
        (by simpa only [extend,combined_base] using ht)
  obtain ⟨c,hc,hcb⟩ := cleanSolver_executes C q g hC G
  have h₁ : (rename (cleanSolver C) workEmbedding).Executes g (combined s input) (combined s output) c := by
    apply rename_executes_to _ workEmbedding g hc
    · funext i;exact combined_work _ _ _
    · funext i;exact combined_work _ _ _
    · intro j hj
      rcases port_cases j with ⟨i,rfl⟩ | ⟨i,rfl⟩
      · simp
      · exact False.elim (hj i rfl)
  have h₂ : (clear (baseEmbedding (k := k) 15)).Executes g (combined s output)
      (combined (Function.update s 15 []) output) ((GraphInput.encode G).length+1) := by
    simpa only [combined_base,hx,update_base] using clear_executes g (baseEmbedding (k := k) 15) (combined s output)
  have h₃ : (moveOn (workEmbedding 0) (baseEmbedding 15) (baseEmbedding 17)
      (base_ne_work _ _).symm (base_ne_work _ _).symm (baseEmbedding.injective.ne (by decide))).Executes g
      (combined (Function.update s 15 []) output)
      (extend (Function.update s 15 (Computability.encodeNat G.2.independentCount)))
      (6*(Computability.encodeNat G.2.independentCount).length+5) := by
    have h := moveOn_executes g (workEmbedding 0) (baseEmbedding 15) (baseEmbedding 17)
      (base_ne_work _ _).symm (base_ne_work _ _).symm (baseEmbedding.injective.ne (by decide))
      (combined (Function.update s 15 []) output) (by simp only [combined_base,Function.update_of_ne (by decide : (17 : Fin 43)≠15),ht])
    simpa only [combined_work,combined_base,output,Function.update_self,List.append_nil,
      update_base,update_work,Function.update_idem,Function.update_eq_self,extend] using h
  have h₄ : (push (baseEmbedding (k := k) 15) false).Executes g
      (extend (Function.update s 15 (Computability.encodeNat G.2.independentCount)))
      (extend (Function.update s 15 (signedBits (G.2.independentCount : ℤ)))) 1 := by
    simpa only [extend,combined_base,Function.update_self,update_base,Function.update_idem,SourceGrid.signedBits_nat] using
      push_executes g (baseEmbedding (k := k) 15) false
        (extend (Function.update s 15 (Computability.encodeNat G.2.independentCount)))
  refine ⟨_,seq_executes _ _ g h₀ (seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄))),?_⟩
  omega

end HiddenCircuits.Complexity.CanonicalSubstitution
