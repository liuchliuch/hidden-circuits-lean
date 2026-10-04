import HiddenCircuits.Approximation.Initialization.MaskUpdate
import HiddenCircuits.Approximation.Initialization.PartialPartners
import HiddenCircuits.Approximation.SamplerRuntime.PartnerConjugation

/-! Forward extraction commits a genuine edge by clearing its two mask bits
and swapping the two still-fixed rows of the concrete partner array. -/
namespace HiddenCircuits.Approximation.Initialization.PairCommit
open Complexity Complexity.OracleBlock SamplerRuntime

abbrev unary (n : ℕ) : BitString := List.replicate n true

def state (mask data : BitString) (u v : ℕ) : Store 10 := fun r =>
  if r.val=0 then mask else if r.val=1 then data else if r.val=2 then unary u
  else if r.val=3 then unary v else []

def maskPorts (second : Bool) : Fin 5 ↪ Fin 11 where
  toFun i := if i.val=0 then 0 else if i.val=1 then (if second then 3 else 2)
    else ⟨i.val+2,by omega⟩
  inj' := by cases second <;> decide +kernel

def swapPorts : Fin 10 ↪ Fin 11 where
  toFun i := ⟨i.val+1,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have hh := congrArg Fin.val h;dsimp at hh;omega

noncomputable def program : OracleBlock 10 := seq (MaskUpdate.on (maskPorts false))
  (seq (MaskUpdate.on (maskPorts true)) (rename ArraySwap.program swapPorts))

theorem program_executes (g : BitString → ℕ) {n : ℕ} (U : Finset (Fin n))
    (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    ∃ t,program.Executes g (state (MaskEnumerationSemantics.mask U) (Output.witness π) u.val v.val)
      (state (MaskEnumerationSemantics.mask ((U.erase u).erase v))
        (Output.witness (MonotoneEndpoints.transpose π u v)) u.val v.val) t ∧
      t≤100000*(n+1)^4 := by
  obtain ⟨a,ha,hab⟩ := MaskUpdate.on_executes (maskPorts false) g
    (state (MaskEnumerationSemantics.mask U) (Output.witness π) u.val v.val)
    (MaskEnumerationSemantics.mask U) u.val
    (by funext r;fin_cases r <;> simp [state,maskPorts,MaskUpdate.state])
    (by simpa using u.isLt)
  have h1 : (MaskUpdate.on (maskPorts false)).Executes g
      (state (MaskEnumerationSemantics.mask U) (Output.witness π) u.val v.val)
      (state (MaskEnumerationSemantics.mask (U.erase u)) (Output.witness π) u.val v.val) a := by
    convert ha using 1
    funext r;fin_cases r <;> simp [state,maskPorts,MaskUpdate.mask_erase]
  obtain ⟨b,hb,hbb⟩ := MaskUpdate.on_executes (maskPorts true) g
    (state (MaskEnumerationSemantics.mask (U.erase u)) (Output.witness π) u.val v.val)
    (MaskEnumerationSemantics.mask (U.erase u)) v.val
    (by funext r;fin_cases r <;> simp [state,maskPorts,MaskUpdate.state])
    (by simpa using v.isLt)
  have h2 : (MaskUpdate.on (maskPorts true)).Executes g
      (state (MaskEnumerationSemantics.mask (U.erase u)) (Output.witness π) u.val v.val)
      (state (MaskEnumerationSemantics.mask ((U.erase u).erase v)) (Output.witness π) u.val v.val) b := by
    convert hb using 1
    funext r;fin_cases r <;> simp [state,maskPorts,MaskUpdate.mask_erase]
  obtain ⟨c,hc,hcb⟩ := ArraySwap.program_executes g (Switch.rowWords π) u.val v.val
  rw [Switch.exchange_rowWords] at hc
  have h3 : (rename ArraySwap.program swapPorts).Executes g
      (state (MaskEnumerationSemantics.mask ((U.erase u).erase v)) (Output.witness π) u.val v.val)
      (state (MaskEnumerationSemantics.mask ((U.erase u).erase v))
        (Output.witness (MonotoneEndpoints.transpose π u v)) u.val v.val) c := by
    apply rename_executes_to ArraySwap.program swapPorts g hc
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr
      fin_cases r
      all_goals first | rfl | exact False.elim (hr 0 rfl)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  have hu := u.isLt
  have hv := v.isLt
  simp only [MaskEnumerationSemantics.mask_length] at hab hbb
  have hc' : c ≤ 10000*(n+1)^4 := hcb.trans (PartnerConjugation.swap_bound π u v)
  nlinarith [Nat.zero_le (n^4),Nat.zero_le (n^3),Nat.zero_le (n^2)]

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (MaskUpdate.on_queryFree _)
  (seq_queryFree _ _ (MaskUpdate.on_queryFree _) (rename_queryFree _ _ ArraySwap.program_queryFree))

noncomputable def on {k : ℕ} (φ : Fin 11 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k n : ℕ} (φ : Fin 11 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (U : Finset (Fin n)) (π : Equiv.Perm (Fin n)) (u v : Fin n)
    (hs : s∘φ=state (MaskEnumerationSemantics.mask U) (Output.witness π) u.val v.val) :
    ∃ t,(on φ).Executes g s
      (Function.update (Function.update s (φ 0) (MaskEnumerationSemantics.mask ((U.erase u).erase v))) (φ 1)
        (Output.witness (MonotoneEndpoints.transpose π u v))) t ∧ t≤100000*(n+1)^4 := by
  obtain ⟨t,ht,hb⟩ := program_executes g U π u v
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update (Function.update s (φ 0) (MaskEnumerationSemantics.mask ((U.erase u).erase v))) (φ 1)
        (Output.witness (MonotoneEndpoints.transpose π u v)))∘φ=
      Function.update (Function.update (s∘φ) 0 (MaskEnumerationSemantics.mask ((U.erase u).erase v))) 1
        (Output.witness (MonotoneEndpoints.transpose π u v)) := by
      funext r;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext r;fin_cases r <;> rfl
  · intro r hr
    rw [Function.update_of_ne (hr 1).symm,Function.update_of_ne (hr 0).symm]

lemma on_queryFree {k : ℕ} (φ : Fin 11 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.Initialization.PairCommit
