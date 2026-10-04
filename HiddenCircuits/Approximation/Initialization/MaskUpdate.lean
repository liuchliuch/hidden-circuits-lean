import HiddenCircuits.Approximation.Initialization.MaskData
import HiddenCircuits.Approximation.SelfReduction.Runtime.MaskDelete

/-! Clear one actual retained-mask bit while preserving the unary
index. The canonical callers prove the index lies in the graph-sized mask. -/
namespace HiddenCircuits.Approximation.Initialization.MaskUpdate
open Complexity Complexity.OracleBlock SelfReduction.Runtime

def state (mask : BitString) (i : ℕ) : Store 4 := fun r =>
  if r.val=0 then mask else if r.val=1 then List.replicate i true else []

def ports : Fin 4 ↪ Fin 5 where
  toFun i := if i.val=0 then 0 else ⟨i.val+1,by omega⟩
  inj' := by decide +kernel

noncomputable def program : OracleBlock 4 :=
  seq (copyOn 1 2 3 (by decide) (by decide) (by decide)) (rename clearAt ports)

theorem program_executes (g : BitString → ℕ) (mask : BitString) (i : Fin mask.length) :
    program.Executes g (state mask i.val) (state (mask.set i.val false) i.val) (12*i.val+13) := by
  let mid : Store 4 := Function.update (state mask i.val) 2 (List.replicate i.val true)
  have hc : (copyOn (1 : Fin 5) 2 3 (by decide) (by decide) (by decide)).Executes g
      (state mask i.val) mid (5*i.val+2) := by
    convert copyOn_executes g (1 : Fin 5) 2 3 (by decide) (by decide) (by decide)
      (state mask i.val) rfl using 1
    · funext r; fin_cases r <;> simp [state,mid]
    · simp [state]
  have hd : (rename clearAt ports).Executes g mid (state (mask.set i.val false) i.val) (7*i.val+9) := by
    apply rename_executes_to clearAt ports g (clearAt_index g mask i)
    · funext r; fin_cases r <;> simp [state,mid,ports,coinStore]
    · funext r; fin_cases r <;> rfl
    · intro r hr
      fin_cases r
      all_goals first | rfl | exact (hr 0 rfl).elim | exact (hr 1 rfl).elim |
        exact (hr 2 rfl).elim | exact (hr 3 rfl).elim
  convert seq_executes _ _ g hc hd using 1 <;> omega

theorem program_queryFree : program.QueryFree := seq_queryFree _ _
  (copyOn_queryFree _ _ _ _ _ _) (rename_queryFree _ _ clearAt_queryFree)

noncomputable def on {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (mask : BitString) (i : ℕ) (hs : s ∘ φ = state mask i) (hi : i < mask.length) :
    ∃ t, (on φ).Executes g s (Function.update s (φ 0) (mask.set i false)) t ∧
      t ≤ 13*(mask.length+i+1) := by
  refine ⟨12*i+13,?_,by omega⟩
  apply rename_executes_to program φ g (program_executes g mask ⟨i,hi⟩) hs
  · funext r
    simp only [Function.comp_apply,Function.update_apply,φ.injective.eq_iff]
    change (if r=0 then mask.set i false else s (φ r)) = _
    have hh := congrFun hs r
    simp only [Function.comp_apply] at hh
    rw [hh]
    fin_cases r <;> rfl
  · intro r hr
    exact Function.update_of_ne (hr 0).symm _ _

theorem on_queryFree {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

theorem mask_erase {n : ℕ} (U : Finset (Fin n)) (v : Fin n) :
    (MaskEnumerationSemantics.mask U).set v.val false = MaskEnumerationSemantics.mask (U.erase v) :=
  MaskEnumerationSemantics.set_mask_erase U v

end HiddenCircuits.Approximation.Initialization.MaskUpdate
