import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidualMathematics

/-! Closed polynomial and canonical even-rank interfaces for actual graph
pair deletion, suitable for composition in the finite counting loop. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidual
open Complexity OracleBlock Initialization Polynomial

noncomputable def timePolynomial : Polynomial ℕ :=
  5*X+55*(X+1)^2+4+X*X*(500*(X+X+X*(2*X+2)+1)^2+18)+40*X+30+
    X+X*(2*X+2)+8+10*X*X+37*X+70

@[simp] lemma timePolynomial_eval (N : ℕ) : timePolynomial.eval N=timeBound N := by
  simp [timePolynomial,timeBound,ResidualGraphProgram.timeBound,InducedGraphEmitter.timeBound]
  <;> ring

/-- Degree-six clock with numerical coefficients, including every byte operation. -/
lemma timeBound_expanded (N : ℕ) :
    timeBound N=2000*N^6+8000*N^5+10000*N^4+4000*N^3+585*N^2+195*N+167 := by
  unfold timeBound ResidualGraphProgram.timeBound InducedGraphEmitter.timeBound
  ring

lemma timeBound_mono {N M : ℕ} (h : N≤M) : timeBound N≤timeBound M := by
  unfold timeBound ResidualGraphProgram.timeBound InducedGraphEmitter.timeBound
  gcongr

theorem program_bounded (g : BitString → ℕ) {N b : ℕ} (G : MatrixGraph (N+1))
    (j : Fin (N+1)) (hb : N+1≤b) :
    ∃ t,program.Executes g (inputStore (GraphInput.encode ⟨N+1,G⟩) (unary j.val))
      (inputStore (output G j) (unary j.val)) t ∧ t≤timePolynomial.eval b := by
  obtain ⟨t,ht,hb'⟩ := program_executes g G j
  exact ⟨t,ht,hb'.trans (by rw [timePolynomial_eval];exact timeBound_mono hb)⟩

/-- Uniform polynomial complexity measured in the actual canonical input bytes. -/
theorem program_inputLengthBound (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph (N+1))
    (j : Fin (N+1)) :
    ∃ t,program.Executes g (inputStore (GraphInput.encode ⟨N+1,G⟩) (unary j.val))
      (inputStore (output G j) (unary j.val)) t ∧
      t≤timePolynomial.eval (GraphInput.encode ⟨N+1,G⟩).length :=
  program_bounded g G j (GraphInput.vertices_le_length ⟨N+1,G⟩)

theorem program_executes_even (g : BitString → ℕ) {d : ℕ} (G : MatrixGraph (2*(d+1)))
    (j : Fin (2*(d+1))) (hj : j≠0) :
    ∃ t,program.Executes g (inputStore (GraphInput.encode ⟨2*(d+1),G⟩) (unary j.val))
      (inputStore (GraphInput.encode ⟨2*d,evenGraph G j hj⟩) (unary j.val)) t ∧
      t≤timeBound (2*(d+1)) := by
  simpa only [output_as_evenGraph G j hj] using program_executes g G j

theorem programOn_executes_even {k d : ℕ} (φ : Fin 19 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (G : MatrixGraph (2*(d+1))) (j : Fin (2*(d+1))) (hj : j≠0)
    (hs : s∘φ=inputStore (GraphInput.encode ⟨2*(d+1),G⟩) (unary j.val)) :
    ∃ t,(programOn φ).Executes g s
      (Function.update s (φ 0) (GraphInput.encode ⟨2*d,evenGraph G j hj⟩)) t ∧
      t≤timeBound (2*(d+1)) := by
  simpa only [output_as_evenGraph G j hj] using programOn_executes φ g s G j hs

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidual
