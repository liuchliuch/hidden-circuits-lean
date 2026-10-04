import HiddenCircuits.Complexity.UnaryArithmetic
import HiddenCircuits.Complexity.BinaryArithmetic.Parity

/-! Fresh reconstruction: actual unary-product/parity sign computation, with
all three dimension masters and an arbitrary completed factor preserved. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioNormalization
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 700000

def state (s h p : ℕ) (factor sign : BitString) : Store 21 := fun i =>
  if i.val=0 then List.replicate s true else if i.val=1 then List.replicate h true
  else if i.val=2 then List.replicate p true else if i.val=3 then factor
  else if i.val=4 then sign else []
def parityEmbedding : Fin 2 ↪ Fin 22 where
  toFun i := ![6,4] i
  inj' := by decide +kernel
noncomputable def signProgram : OracleBlock 21 := seq (copyOn 1 5 7 (by decide) (by decide) (by decide))
  (seq (repeatCopy 5 2 6 7 (by decide) (by decide) (by decide))
    (seq (push 4 true) (rename parityBlock parityEmbedding)))

lemma parity_one (n : ℕ) : parityBit n::[true]=signedBits ((-1:ℤ)^n) := by
  rw [←signedNat_parity]
  cases parityBit n <;> rfl

lemma signProgram_executes (g : BitString → ℕ) (s h p : ℕ) (factor : BitString) :
    signProgram.Executes g (state s h p factor [])
      (state s h p factor (signedBits ((-1:ℤ)^(p*h)))) (6*p*h+9*h+12) := by
  let s₀ := state s h p factor []
  let s₁ := Function.update s₀ (5:Fin 22) (List.replicate h true)
  let s₂ := Function.update s₀ (6:Fin 22) (List.replicate (h*p) true)
  let s₃ := Function.update s₂ (4:Fin 22) [true]
  have h1 : (copyOn (1:Fin 22) 5 7 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (5*h+2) := by
    simpa [s₀,s₁,state] using copyOn_executes g (1:Fin 22) 5 7 (by decide) (by decide) (by decide) s₀ rfl
  have h2 : (repeatCopy (5:Fin 22) 2 6 7 (by decide) (by decide) (by decide)).Executes g s₁ s₂ ((5*p+4)*h+1) := by
    have hh := unaryMultiply_executes g (5:Fin 22) 2 6 7 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s₁ h p (by simp [s₁]) (by simp [s₁,s₀,state]) (by simp [s₁,s₀,state])
    convert hh using 1
    funext i;fin_cases i <;> simp [s₂,s₁,s₀,state,workStore]
  have h3 : (push (4:Fin 22) true).Executes g s₂ s₃ 1 := by
    simpa [s₃,s₂,s₀,state] using push_executes g (4:Fin 22) true s₂
  have h4 : (rename parityBlock parityEmbedding).Executes g s₃
      (state s h p factor (signedBits ((-1:ℤ)^(p*h)))) (h*p+2) := by
    have hh := parityBlock_executes g (List.replicate (h*p) true) [true]
    simp only [List.length_replicate,parity_one] at hh
    rw [Nat.mul_comm h p] at hh
    rw [Nat.mul_comm h p]
    apply rename_executes_to parityBlock parityEmbedding g hh
    · funext i
      fin_cases i
      · change List.replicate (h*p) true=List.replicate (p*h) true
        rw [Nat.mul_comm h p]
      · rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have h4 : i.val≠4 := by intro h;exact hi 1 (Fin.ext h.symm)
      have h6 : i.val≠6 := by intro h;exact hi 0 (Fin.ext h.symm)
      have hi4 : i≠(4:Fin 22) := fun he => h4 (congrArg Fin.val he)
      have hi6 : i≠(6:Fin 22) := fun he => h6 (congrArg Fin.val he)
      simp only [s₃,s₂,s₀,Function.update_of_ne hi4,Function.update_of_ne hi6,state,h4,if_false]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)) using 1 <;> ring

lemma signProgram_queryFree : signProgram.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (repeatCopy_queryFree _ _ _ _ _ _ _) (seq_queryFree _ _ (push_queryFree _ _)
    (rename_queryFree _ _ parityBlock_queryFree)))
end HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioNormalization
