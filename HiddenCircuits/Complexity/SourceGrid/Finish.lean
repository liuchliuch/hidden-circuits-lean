import HiddenCircuits.Complexity.SourceGrid.Body
import HiddenCircuits.Complexity.FinalCountRuntime

/-! The actual final grid division and canonical natural output on stack zero. -/
namespace HiddenCircuits.Complexity.SourceGrid
open OracleBlock BinaryArithmetic Polynomial

def finishStore (n m : ℕ) (formula denominator accumulator left right : BitString) : Store 42 := fun q =>
  if q.val=0 then List.replicate n true else if q.val=1 then List.replicate m true else
  if q.val=9 then formula else if q.val=10 then denominator else if q.val=11 then accumulator else
  if q.val=17 then left else if q.val=18 then right else []

def divisionEmbedding : Fin 9 ↪ Fin 43 where
  toFun q := ⟨q.val+17,by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg (fun q : Fin 43 => q.val) h
    change i.val+17=j.val+17 at hh
    omega

noncomputable def finish : OracleBlock 42 :=
  seq (copyOn 11 17 19 (by decide) (by decide) (by decide))
    (seq (copyOn 10 18 19 (by decide) (by decide) (by decide))
      (seq (rename FinalCountRuntime.program divisionEmbedding)
        (seq (clear 0) (moveOn 17 0 18 (by decide) (by decide) (by decide)))))
noncomputable def finishTime : Polynomial ℕ :=
  FinalCountRuntime.time.comp (10*(X+1)^3)+50*(X+1)^3+7*X+24

lemma satCount_bound {n m : ℕ} (F : CNF n m) : F.satCount≤2^n := by
  classical
  unfold CNF.satCount
  calc
    _ ≤ Fintype.card (Fin n → Bool) := Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := by simp

lemma satCount_length {n m : ℕ} (F : CNF n m) :
    (Computability.encodeNat F.satCount).length≤n+1 := by
  rw [encodeNat_length]
  have h := Nat.size_le_size (satCount_bound F)
  simpa [Nat.size_pow] using h

lemma recoveryLength_bound (F : CNFInput) :
    (signedBits (gridNumerator F.1 F.2.1 (fun i j => (F.2.2.cloneCount i.val j.val : ℤ)))).length+
      (signedBits (gridDenominator F.1 F.2.1)).length≤10*((CNFInput.encode F).length+1)^3 := by
  have h := CNFInput.recovery_bits_in_source_bits F
  have hp : (CNFInput.encode F).length^3≤((CNFInput.encode F).length+1)^3 := Nat.pow_le_pow_left (by omega) 3
  have h1 : 1≤((CNFInput.encode F).length+1)^3 := Nat.one_le_pow _ _ (by omega)
  simp only [signedBits,List.length_cons,encodeNat_length]
  nlinarith only [h.1,h.2,Nat.zero_le ((CNFInput.encode F).length^3),Nat.zero_le ((CNFInput.encode F).length^2)]

theorem finish_executes (F : CNFInput) :
    ∃ s : Store 42, ∃ c, finish.Executes GraphInput.independentSetProblem
      (GridRuntime.initialStore F.1 F.2.1 (frame (persistent F
        (gridNumerator F.1 F.2.1 (fun i j => (F.2.2.cloneCount i.val j.val : ℤ)))))) s c ∧
      s 0=Computability.encodeNat F.2.2.satCount ∧ c≤finishTime.eval (CNFInput.encode F).length := by
  let g := GraphInput.independentSetProblem
  let N := signedBits (gridNumerator F.1 F.2.1 (fun i j => (F.2.2.cloneCount i.val j.val : ℤ)))
  let D := signedBits (gridDenominator F.1 F.2.1)
  let answer := Computability.encodeNat F.2.2.satCount
  let s₀ := finishStore F.1 F.2.1 (CNFInput.encode F) D N [] []
  let s₁ := finishStore F.1 F.2.1 (CNFInput.encode F) D N N []
  let s₂ := finishStore F.1 F.2.1 (CNFInput.encode F) D N N D
  let s₃ := finishStore F.1 F.2.1 (CNFInput.encode F) D N answer []
  let s₄ := finishStore 0 F.2.1 (CNFInput.encode F) D N answer []
  let s₅ := Function.update (finishStore 0 F.2.1 (CNFInput.encode F) D N [] []) (0 : Fin 43) answer
  have h₀ : (copyOn (11 : Fin 43) 17 19 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (5*N.length+2) := by
    convert copyOn_executes g (11 : Fin 43) 17 19 (by decide) (by decide) (by decide) s₀ rfl using 1
    funext q;fin_cases q <;> simp [s₀,s₁,finishStore]
  have h₁ : (copyOn (10 : Fin 43) 18 19 (by decide) (by decide) (by decide)).Executes g s₁ s₂ (5*D.length+2) := by
    convert copyOn_executes g (10 : Fin 43) 18 19 (by decide) (by decide) (by decide) s₁ rfl using 1
    funext q;fin_cases q <;> simp [s₁,s₂,finishStore]
  obtain ⟨d,hd,hdb⟩ := FinalCountRuntime.source_executes g F.2.2
  have h₂ : (rename FinalCountRuntime.program divisionEmbedding).Executes g s₂ s₃ d := by
    apply rename_executes_to _ divisionEmbedding g hd
    · funext q;fin_cases q <;> rfl
    · funext q;fin_cases q <;> rfl
    · intro q hq;fin_cases q <;> first | rfl | (exfalso;exact hq 0 rfl) | (exfalso;exact hq 1 rfl)
  have h₃ : (clear (0 : Fin 43)).Executes g s₃ s₄ (F.1+1) := by
    convert clear_executes g (0 : Fin 43) s₃ using 1
    · funext q;fin_cases q <;> rfl
    · simp [s₃,finishStore]
  have h₄ : (moveOn (17 : Fin 43) 0 18 (by decide) (by decide) (by decide)).Executes g s₄ s₅ (6*answer.length+5) := by
    convert moveOn_executes g (17 : Fin 43) 0 18 (by decide) (by decide) (by decide) s₄ rfl using 1
    funext q;fin_cases q <;> simp [s₄,s₅,finishStore]
  have hin : s₀=GridRuntime.initialStore F.1 F.2.1 (frame (persistent F
      (gridNumerator F.1 F.2.1 (fun i j => (F.2.2.cloneCount i.val j.val : ℤ))))) := by
    funext q;fin_cases q <;> rfl
  have h := seq_executes _ _ g h₀ (seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)))
  rw [hin] at h
  refine ⟨s₅,_,h,rfl,?_⟩
  have hlen := CNFInput.encode_length_lower F
  have hab := satCount_length F.2.2
  have hrec := recoveryLength_bound F
  have htime := polynomial_nat_eval_mono FinalCountRuntime.time hrec
  dsimp only at htime
  simp only [finishTime,eval_add,eval_comp,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
  dsimp only [N,D,answer] at *
  omega

end HiddenCircuits.Complexity.SourceGrid
