import HiddenCircuits.Circuit.Runtime.SpectralNodesBounds

/-! The exact lexicographic triangular spectral nodes are emitted by one fixed
finite bit-stack program, with a polynomial bound in the input unary degree. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralNodes
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

def inputStore (g : ℕ) : Store 12 := fun i => if i.val=12 then List.replicate g true else []
def outputStore (g : ℕ) (xs : BitString) : Store 12 :=
  Function.update (inputStore g) 0 xs
noncomputable def prepare : OracleBlock 12 :=
  seq (prepend 10 (signedBits 1)) (seq (copyOn 12 11 9 (by decide) (by decide) (by decide)) (push 11 true))
noncomputable def finish : OracleBlock 12 := seq (clear 10) (reverseOn 7 0 (by decide))
noncomputable def program : OracleBlock 12 := seq prepare (seq outerLoop finish)

theorem prepare_executes (oracle : BitString → ℕ) (g : ℕ) :
    prepare.Executes oracle (inputStore g) (outerState 1 (g+1) g []) (5*g+14) := by
  let s₁ := Function.update (inputStore g) (10:Fin 13) (signedBits 1)
  let s₂ := outerState 1 g g []
  have h₁ : (prepend (10:Fin 13) (signedBits 1)).Executes oracle (inputStore g) s₁ 7 := by
    simpa [s₁,inputStore] using prepend_executes oracle (10:Fin 13) (signedBits 1) (inputStore g)
  have h₂ : (copyOn (12:Fin 13) 11 9 (by decide) (by decide) (by decide)).Executes oracle s₁ s₂ (5*g+2) := by
    convert copyOn_executes oracle (12:Fin 13) 11 9 (by decide) (by decide) (by decide) s₁ rfl using 1
    · funext i;fin_cases i <;> simp [s₁,s₂,inputStore,outerState]
    · simp [s₁,inputStore]
  have h₃ : (push (11:Fin 13) true).Executes oracle s₂ (outerState 1 (g+1) g []) 1 := by
    convert push_executes oracle (11:Fin 13) true s₂ using 1
    funext i;fin_cases i <;> simp [s₂,outerState,List.replicate_succ]
  convert seq_executes _ _ oracle h₁ (seq_executes _ _ oracle h₂ h₃) using 1 <;> omega

theorem finish_executes (oracle : BitString → ℕ) (x g : ℕ) (out : BitString) :
    finish.Executes oracle (outerState x 0 g out) (outputStore g out.reverse)
      ((signedBits (x:ℤ)).length+2*out.length+4) := by
  let s := Function.update (outerState x 0 g out) (10:Fin 13) []
  have h₁ : (clear (10:Fin 13)).Executes oracle (outerState x 0 g out) s ((signedBits (x:ℤ)).length+1) := by
    simpa [s,outerState] using clear_executes oracle (10:Fin 13) (outerState x 0 g out)
  have h₂ : (reverseOn (7:Fin 13) 0 (by decide)).Executes oracle s (outputStore g out.reverse) (2*out.length+1) := by
    convert reverseOn_executes oracle (7:Fin 13) 0 (by decide) s using 1
    · funext i;fin_cases i <;> simp [s,outerState,outputStore,inputStore]
  convert seq_executes _ _ oracle h₁ h₂ using 1 <;> omega

noncomputable def time : Polynomial ℕ :=
  5*X+14+(X+1)*((X+2)*(bodyTime.comp (4*(X+1)+2)+2)+6*(4*(X+1)+2)+5*(X+1)+32)+1+
  (4*(X+1)+2)+2*(X+1)^2*(2*(4*(X+1)+2)+2)+8

theorem program_executes (oracle : BitString → ℕ) (g : ℕ) :
    ∃ t, program.Executes oracle (inputStore g)
      (outputStore g (encodeBitList (((spectralIndices g).map spectralIntegerNode).map signedBits))) t ∧
      t≤time.eval g := by
  have hi := prepare_executes oracle g
  obtain ⟨c,hc,hcb⟩ := outerLoop_executes oracle (g+1) 1 g (4*(g+1)+2) [] (by omega) (stages_bounded (g+1))
  simp only [one_mul,List.append_nil] at hc
  have hf := finish_executes oracle (4^(g+1)) g (encodeBitList ((triangle 1 (g+1)).map signedBits)).reverse
  simp only [List.reverse_reverse,List.length_reverse] at hf
  have hh := seq_executes _ _ oracle hi (seq_executes _ _ oracle hc hf)
  rw [triangle_spectral] at hh
  refine ⟨_,hh,?_⟩
  have hm := stages_bounded (g+1) (g+1) (by omega) 0 (by omega)
  simp only [one_mul,pow_zero,mul_one] at hm
  have hl := triangle_stream_length (g+1)
  rw [triangle_spectral] at hl
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat,eval_one,eval_pow,eval_comp]
  nlinarith

theorem program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (seq_queryFree _ _ (prepend_queryFree _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (push_queryFree _ _)))
    (seq_queryFree _ _ outerLoop_queryFree (seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _)))
end HiddenCircuits.Circuit.Runtime.SpectralNodes
