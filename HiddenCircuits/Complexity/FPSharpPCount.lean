import HiddenCircuits.Complexity.FP
import HiddenCircuits.Complexity.BinaryArithmetic.SubtractionMachine
import HiddenCircuits.Complexity.GraphVerifier.UnpairProgram

/-! Exact binary witness cardinality for FP inclusion in machine-defined #P.
Leading zero padding is fixed-length and does not duplicate represented values. -/
namespace HiddenCircuits.Complexity.FPSharpP
open BinaryArithmetic

lemma value_injective_of_length {xs ys : BitString} (hl : xs.length=ys.length) (hv : value xs=value ys) : xs=ys := by
  induction xs generalizing ys with
  | nil=>cases ys <;> simp_all
  | cons b xs ih=>
    cases ys with
    | nil=>simp at hl
    | cons c ys=>
      have hb:b=c:=by cases b <;> cases c <;> simp_all [value,bitVal] <;> omega
      subst c
      have ht:xs.length=ys.length:=by simpa using hl
      have hv':value xs=value ys:=by simp only [value_cons] at hv;omega
      rw [ih ht hv']
def valueMap (m : ℕ) (w : Fin m→Bool) : Fin (2^m):=
  ⟨value (List.ofFn w),by simpa using value_lt_pow_length (List.ofFn w)⟩
lemma valueMap_injective (m : ℕ) : Function.Injective (valueMap m) := by
  intro u v h
  have hv:value (List.ofFn u)=value (List.ofFn v):=congrArg Fin.val h
  have he:=value_injective_of_length (by simp : (List.ofFn u).length=(List.ofFn v).length) hv
  exact List.ofFn_injective he
noncomputable def valueEquiv (m : ℕ) : (Fin m→Bool)≃Fin (2^m):=
  Equiv.ofBijective (valueMap m) ((Fintype.bijective_iff_injective_and_card _).mpr ⟨valueMap_injective m,by simp⟩)
lemma valueEquiv_apply (m : ℕ) (w : Fin m→Bool) : (valueEquiv m w).val=value (List.ofFn w):=rfl
lemma valueEquiv_symm (m : ℕ) (i : Fin (2^m)) : value (List.ofFn ((valueEquiv m).symm i))=i.val := by
  change (valueEquiv m ((valueEquiv m).symm i)).val=i.val
  rw [Equiv.apply_symm_apply]

noncomputable def smallerEquiv (m N : ℕ) (hN:N ≤ 2^m) :
    {w : Fin m→Bool // value (List.ofFn w)<N} ≃ Fin N where
  toFun w:=⟨value (List.ofFn w.val),w.property⟩
  invFun i:=⟨(valueEquiv m).symm ⟨i.val,lt_of_lt_of_le i.isLt hN⟩,by rw [valueEquiv_symm];exact i.isLt⟩
  left_inv w:=by
    apply Subtype.ext
    apply (valueEquiv m).injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    rfl
  right_inv i:=by
    apply Fin.ext
    exact valueEquiv_symm m ⟨i.val,lt_of_lt_of_le i.isLt hN⟩
lemma smaller_card (m N : ℕ) (hN:N ≤ 2^m) :
    Fintype.card {w : Fin m→Bool // value (List.ofFn w)<N}=N := by
  simpa using Fintype.card_congr (smallerEquiv m N hN)

def verifier (f : BitString→ℕ) (raw : BitString) : Bool:=
  match unpairBits raw with
  | none=>false
  | some (x,w)=>decide (value w<f x)
@[simp] lemma verifier_pair (f : BitString→ℕ) (x w : BitString) : verifier f (pairBits x w)=decide (value w<f x) := by
  simp [verifier]
lemma verifier_parse (f : BitString→ℕ) (raw : BitString) :
    verifier f raw=((GraphVerifier.parse raw).ok && decide (value (GraphVerifier.parse raw).right<f (GraphVerifier.parse raw).left)) := by
  rw [verifier,GraphVerifier.parse_spec]
  cases (GraphVerifier.parse raw).ok <;> simp
lemma certificate_count (f : BitString→ℕ) (x : BitString) (m : ℕ) (h:f x ≤ 2^m) :
    certificateCount (verifier f) x m=f x := by
  unfold certificateCount
  simp only [verifier_pair,decide_eq_true_eq]
  exact smaller_card m (f x) h
lemma fp_value_bound {f : BitString→ℕ} (hf : FP f) : ∃p : Polynomial ℕ,∀x,f x ≤ 2^(p.eval x.length) := by
  obtain ⟨p,hp⟩:=hf.binary_output_bound
  refine ⟨p,fun x=>?_⟩
  have h:=value_lt_pow_length (Computability.encodeNat (f x))
  rw [value_encodeNat] at h
  exact h.le.trans (Nat.pow_le_pow_right (by decide) (hp x))
end HiddenCircuits.Complexity.FPSharpP
