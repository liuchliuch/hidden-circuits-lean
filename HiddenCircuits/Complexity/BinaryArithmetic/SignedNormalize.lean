import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits
import HiddenCircuits.Complexity.BinaryArithmetic.SubtractionMachine

/-! Total signed-word normalization by real binary subtraction against zero.
No input canonicality or integer-magnitude runtime bound is assumed. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.SignedNormalize
open OracleBlock

def value : BitString → ℤ
  | [] => 0
  | sign::magnitude => signedNat sign (BinaryArithmetic.value magnitude)
@[simp] theorem value_signedBits (z : ℤ) : value (signedBits z)=z := by
  simp [value,signedBits]

def state (word flag : BitString) : Store 3 := subStore word [] [] flag
noncomputable def finish (sign : Bool) : OracleBlock 3 := seq subBlock (seq (clear 3) (finishOn 0 sign))
noncomputable def program : OracleBlock 3 := branchPop 0 (push 0 false) (finish false) (finish true)

theorem finish_executes (g : BitString → ℕ) (sign : Bool) (mag : BitString) :
    ∃c,(finish sign).Executes g (state mag []) (state (signedBits (signedNat sign (BinaryArithmetic.value mag))) []) c ∧
      c≤5*mag.length+15 := by
  have hb : (subRaw mag [] false).2=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hlt:=(subRaw_borrow mag []).mp h
    simpa using hlt
  have he : subtractBits mag []=Computability.encodeNat (BinaryArithmetic.value mag) := by
    simp [subtractBits_correct]
  have h1:=subBlock_executes g mag []
  rw [hb,he] at h1
  have h2 : (clear (3:Fin 4)).Executes g (state (Computability.encodeNat (BinaryArithmetic.value mag)) [false])
      (state (Computability.encodeNat (BinaryArithmetic.value mag)) []) 2 := by
    convert clear_executes g (3:Fin 4) (state (Computability.encodeNat (BinaryArithmetic.value mag)) [false]) using 1
    funext i;fin_cases i <;> rfl
  have h3 : (finishOn (0:Fin 4) sign).Executes g (state (Computability.encodeNat (BinaryArithmetic.value mag)) [])
      (state (signedBits (signedNat sign (BinaryArithmetic.value mag))) [])
      (finishCost (Computability.encodeNat (BinaryArithmetic.value mag))) := by
    convert finishOn_executes g (0:Fin 4) sign (state (Computability.encodeNat (BinaryArithmetic.value mag)) []) using 1
    funext i;fin_cases i <;> simp [state,subStore,finishSigned_encode]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  have hc:=subCost_bound mag []
  have hf:=finishCost_le (Computability.encodeNat (BinaryArithmetic.value mag))
  simp only [List.length_nil,Nat.max_zero] at hc
  omega

theorem program_executes (g : BitString → ℕ) (xs : BitString) :
    ∃c,program.Executes g (state xs []) (state (signedBits (value xs)) []) c ∧ c≤5*xs.length+17 := by
  cases xs with
  | nil =>
    refine ⟨3,?_,by simp⟩
    apply branchPop_empty (0:Fin 4) _ _ _ g rfl
    convert push_executes g (0:Fin 4) false (state [] []) using 1
    funext i;fin_cases i <;> rfl
  | cons sign mag =>
    obtain ⟨c,hc,hb⟩:=finish_executes g sign mag
    have hp : Function.update (state (sign::mag) []) 0 mag=state mag [] := by
      funext i;fin_cases i <;> rfl
    cases sign
    · exact ⟨c+2,branchPop_false (0:Fin 4) _ _ _ g rfl (by rw [hp];exact hc),by simp;omega⟩
    · exact ⟨c+2,branchPop_true (0:Fin 4) _ _ _ g rfl (by rw [hp];exact hc),by simp;omega⟩

lemma normalize_length (xs : BitString) : (BinaryArithmetic.normalize xs).length≤xs.length := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [BinaryArithmetic.normalize];split_ifs <;> simp_all
lemma signed_length (xs : BitString) : (signedBits (value xs)).length≤xs.length+1 := by
  cases xs with
  | nil => rfl
  | cons sign mag =>
    rw [value,←finishSigned_encode,←normalize_eq_encode]
    have h:=normalize_length mag
    simp only [finishSigned]
    split_ifs <;> simp_all <;> omega
lemma finish_queryFree (sign : Bool) : (finish sign).QueryFree :=
  seq_queryFree _ _ subBlock_queryFree (seq_queryFree _ _ (clear_queryFree _) (finishOn_queryFree _ _))
lemma program_queryFree : program.QueryFree :=
  branchPop_queryFree _ _ _ _ (push_queryFree _ _) (finish_queryFree false) (finish_queryFree true)
noncomputable def on {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k) (xs : BitString)
    (hs : s ∘ φ=state xs []) :
    ∃c,(on φ).Executes g s (Function.update s (φ 0) (signedBits (value xs))) c ∧c≤5*xs.length+17 := by
  obtain ⟨c,hc,hb⟩:=program_executes g xs
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ φ g hc hs
  · funext i
    simp only [Function.comp_apply,Function.update_apply,φ.injective.eq_iff]
    have hi:=congrFun hs i
    change s (φ i)=_ at hi
    rw [hi]
    fin_cases i <;> rfl
  · intro i hi;simp [Ne.symm (hi 0)]
lemma on_queryFree {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree
end HiddenCircuits.Complexity.BinaryArithmetic.SignedNormalize
