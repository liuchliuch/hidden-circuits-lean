import HiddenCircuits.Circuit.Runtime.SourceCircuitFinish

/-! Complete actual finite-bit source graph-to-constraint-circuit compiler.
Its two clean outputs are canonical circuit bytes and the exact unary exponent
of the known scalar normalization. -/
namespace HiddenCircuits.Circuit.Runtime.SourceCircuitEmitter
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock Polynomial

noncomputable def program : OracleBlock 35 := seq core finish
noncomputable def time : Polynomial ℕ := coreTime+2*circuitSize+12*X^3+X^2+3*X+22

theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixGraph n) :
    ∃ c, program.Executes g (Function.update (fun _ => []) 0 (GraphInput.encode ⟨n,G⟩))
      (outputStore (circuitBits n (restoringIndependentProgram G).gates) (2*restoringSwapPairs (sourceEdges G))) c ∧
      c≤time.eval (GraphInput.encode ⟨n,G⟩).length := by
  obtain ⟨c,hc,hcb⟩ := core_executes g G
  have hf := finish_executes g (n-1) (n-1) n G.bits
    (circuitBits n (restoringIndependentProgram G).gates).reverse (2*restoringSwapPairs (sourceEdges G))
  simp only [List.reverse_reverse,List.length_reverse] at hf
  refine ⟨_,seq_executes _ _ g hc hf,?_⟩
  have hn := GraphInput.vertices_le_length (⟨n,G⟩ : GraphInput)
  change n≤(GraphInput.encode ⟨n,G⟩).length at hn
  have hs := circuitSize_bound G
  have hm := polynomial_nat_eval_mono circuitSize hn
  dsimp only at hm
  have hnorm := normalization_bound G
  have h2 := Nat.pow_le_pow_left hn 2
  have h3 := Nat.pow_le_pow_left hn 3
  simp only [time,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,MatrixGraph.bits_length]
  simp only [pow_two] at h2 ⊢
  omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ core_queryFree finish_queryFree

/-- The physically emitted gate sequence computes the actual source count, with
exactly the scalar exponent returned on output1. -/
theorem emitted_circuit_correct {n : ℕ} (G : MatrixGraph n) :
    (1/8 : ℚ)^(2*restoringSwapPairs (sourceEdges G)) *
      constraintCircuitMatrix (restoringIndependentProgram G).gates (zeroBits n) (zeroBits n)=G.independentCount := by
  rw [←restoringIndependentProgram_scalar]
  exact restoringIndependentProgram_correct G

noncomputable def on {k : ℕ} (φ : Fin 36 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 36 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    {n : ℕ} (G : MatrixGraph n)
    (hs : s∘φ=Function.update (fun _ => []) 0 (GraphInput.encode ⟨n,G⟩)) :
    ∃ c, (on φ).Executes g s
      (Function.update (Function.update s (φ 0) (circuitBits n (restoringIndependentProgram G).gates))
        (φ 1) (List.replicate (2*restoringSwapPairs (sourceEdges G)) true)) c ∧
      c≤time.eval (GraphInput.encode ⟨n,G⟩).length := by
  obtain ⟨c,hc,hb⟩ := program_executes g G
  refine ⟨c,?_,hb⟩
  apply rename_executes_to program φ g hc hs
  · funext q
    have hq := congrFun hs q
    change s (φ q)=_ at hq
    simp only [Function.comp_def,Function.update_apply,φ.injective.eq_iff,hq]
    fin_cases q <;> rfl
  · intro q hq
    simp only [Function.update_of_ne (hq 0).symm,Function.update_of_ne (hq 1).symm]
lemma on_queryFree {k : ℕ} (φ : Fin 36 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Circuit.Runtime.SourceCircuitEmitter
