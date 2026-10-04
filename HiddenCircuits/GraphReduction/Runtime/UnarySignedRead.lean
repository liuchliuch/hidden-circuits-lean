import HiddenCircuits.Complexity.BinaryArithmetic.UnaryBinary
import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits

/-! Physically copy a unary field, consume the copy through binary
ripple increments, and prepend the canonical nonnegative sign bit. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnarySignedRead
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

def state (n : ℕ) (out clock : BitString) : Store 3 :=
  ![List.replicate n true,out,clock,[]]
def convertMap : Fin 3 ↪ Fin 4 where
  toFun i := ![2,1,3] i
  inj' := by decide +kernel
noncomputable def program : OracleBlock 3 :=
  seq (copyOn 0 2 3 (by decide) (by decide) (by decide))
    (seq (rename unaryBinary convertMap) (push 1 false))
def bound (n : ℕ) : ℕ := 4*n^2+10*n+8

theorem program_executes (g : BitString → ℕ) (n : ℕ) :
    ∃t,program.Executes g (state n [] []) (state n (signedBits (n:ℤ)) []) t ∧t≤bound n := by
  have hc : (copyOn (0:Fin 4) 2 3 (by decide) (by decide) (by decide)).Executes g
      (state n [] []) (state n [] (List.replicate n true)) (5*n+2) := by
    convert copyOn_executes g (0:Fin 4) 2 3 (by decide) (by decide) (by decide) (state n [] []) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have hu : (rename unaryBinary convertMap).Executes g (state n [] (List.replicate n true))
      (state n (Computability.encodeNat n) []) (unaryBinaryCost 0 n) := by
    apply rename_executes_to unaryBinary convertMap g
      (by simpa using unaryBinary_executes g (List.replicate n true) 0)
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim
  have hp : (push (1:Fin 4) false).Executes g (state n (Computability.encodeNat n) [])
      (state n (signedBits (n:ℤ)) []) 1 := by
    convert push_executes g (1:Fin 4) false (state n (Computability.encodeNat n) []) using 1
    funext i;fin_cases i <;> simp [state,signedBits,negative]
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hu hp),?_⟩
  have hb := unaryBinaryCost_le n 0 n (by omega)
  unfold bound
  nlinarith

lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _
    (rename_queryFree _ _ unaryBinary_queryFree) (push_queryFree _ _))

noncomputable def on {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) : OracleBlock k := rename program φ
 theorem on_executes {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (n : ℕ) (hs:s∘φ=state n [] []) :
    ∃t,(on φ).Executes g s (Function.update s (φ 1) (signedBits (n:ℤ))) t ∧t≤bound n := by
  obtain ⟨t,ht,hb⟩ := program_executes g n
  refine ⟨t,?_,hb⟩
  apply rename_executes_to _ φ g ht hs
  · have he : (Function.update s (φ 1) (signedBits (n:ℤ)))∘φ=
        Function.update (s∘φ) 1 (signedBits (n:ℤ)) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi;exact Function.update_of_ne (hi 1).symm _ _
lemma on_queryFree {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree
end HiddenCircuits.GraphReduction.Runtime.UnarySignedRead
