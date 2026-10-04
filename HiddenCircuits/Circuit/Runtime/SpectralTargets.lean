import HiddenCircuits.Circuit.Runtime.SpectralTargetsLoops

/-! Actual degree-controlled target0/−1 weight-stream generation. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralTargets
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

/-- The public interface preserves unary degree0 and mode bit1, and writes
canonical signed target words to2; all six work tapes are empty. -/
def publicStore (g : ℕ) (mode : Bool) (out : BitString) : Store 8 := fun i =>
  if i.val=0 then List.replicate g true else if i.val=1 then [mode] else if i.val=2 then out else []
noncomputable def initializeTargets : OracleBlock 8 :=
  seq (copyOn 0 7 6 (by decide) (by decide) (by decide)) (push 7 true)
noncomputable def program : OracleBlock 8 := seq initializeTargets (seq outerLoop (reverseOn 8 2 (by decide)))
noncomputable def time : Polynomial ℕ :=
  (X+1)*((X+2)*(6*(X+2)+36)+5*(X+1)+10)+12*(X+1)^2+5*X+11

theorem initializeTargets_executes (oracle : BitString → ℕ) (g : ℕ) (mode : Bool) :
    initializeTargets.Executes oracle (publicStore g mode [])
      (state g mode [] (List.replicate (g+1) true) []) (5*g+5) := by
  let s₀ := publicStore g mode []
  let s₁ := state g mode [] (List.replicate g true) []
  let s₂ := state g mode [] (List.replicate (g+1) true) []
  have h₁ : (copyOn (0:Fin 9) 7 6 (by decide) (by decide) (by decide)).Executes oracle s₀ s₁ (5*g+2) := by
    convert copyOn_executes oracle (0:Fin 9) 7 6 (by decide) (by decide) (by decide) s₀ rfl using 1
    · funext i;fin_cases i <;> simp [s₀,s₁,publicStore,state]
    · simp [s₀,publicStore]
  have h₂ : (push (7:Fin 9) true).Executes oracle s₁ s₂ 1 := by
    convert push_executes oracle (7:Fin 9) true s₁ using 1
    funext i;fin_cases i <;> simp [s₁,s₂,state,List.replicate_succ]
  convert seq_executes _ _ oracle h₁ h₂ using 1 <;> omega

/-- Exact spectralIndices order, including degree0 and both target values. -/
theorem program_executes (oracle : BitString → ℕ) (g : ℕ) (mode : Bool) :
    ∃ t, program.Executes oracle (publicStore g mode [])
      (publicStore g mode (encodeBitList ((weights g mode).map signedBits))) t ∧ t≤time.eval g := by
  have hi := initializeTargets_executes oracle g mode
  obtain ⟨c,hc,hcb⟩ := outerLoop_executes oracle g (g+1) mode []
  rw [triangle_weights] at hc
  simp only [List.append_nil] at hc
  let out := encodeBitList ((weights g mode).map signedBits)
  have hf : (reverseOn (8:Fin 9) 2 (by decide)).Executes oracle (state g mode [] [] out.reverse)
      (publicStore g mode out) (2*out.length+1) := by
    convert reverseOn_executes oracle (8:Fin 9) 2 (by decide) (state g mode [] [] out.reverse) using 1
    · funext i;fin_cases i <;> simp [state,publicStore]
    · simp [state]
  refine ⟨(5*g+5)+(c+(2*out.length+1)+2)+2,seq_executes _ _ oracle hi (seq_executes _ _ oracle hc hf),?_⟩
  have ho := weight_stream_length g mode
  unfold outerBound at hcb
  simp only [time,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat]
  change (5*g+5)+(c+(2*out.length+1)+2)+2≤(g+1)*((g+2)*(6*(g+2)+36)+5*(g+1)+10)+12*(g+1)^2+5*g+11
  dsimp [out]
  nlinarith

theorem time_cubic (g : ℕ) : time.eval g≤200*(g+1)^3 := by
  simp only [time,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat]
  nlinarith [Nat.zero_le (g*g*g),Nat.zero_le (g*g)]

theorem program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (push_queryFree _ _))
    (seq_queryFree _ _ outerLoop_queryFree (reverseOn_queryFree _ _ _))

noncomputable def programOn {k : ℕ} (φ : Fin 9 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem programOn_executes {k : ℕ} (φ : Fin 9 ↪ Fin (k+1)) (oracle : BitString → ℕ)
    (s : Store k) (g : ℕ) (mode : Bool) (hs : s∘φ=publicStore g mode []) :
    ∃ t, (programOn φ).Executes oracle s (Function.update s (φ 2) (encodeBitList ((weights g mode).map signedBits))) t ∧
      t≤time.eval g := by
  obtain ⟨t,ht,hb⟩ := program_executes oracle g mode
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ oracle ht hs
  · have he : (Function.update s (φ 2) (encodeBitList ((weights g mode).map signedBits)))∘φ=
        Function.update (s∘φ) 2 (encodeBitList ((weights g mode).map signedBits)) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro j hj;exact Function.update_of_ne (hj 2).symm _ _

theorem programOn_queryFree {k : ℕ} (φ : Fin 9 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree
end HiddenCircuits.Circuit.Runtime.SpectralTargets
