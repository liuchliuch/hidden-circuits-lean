import HiddenCircuits.Approximation.Initialization.MaskData
import HiddenCircuits.Approximation.SelfReduction.Runtime.MaskDelete

/-! A literal seven-stack
copy-and-erase pair routine preserves the source and both unary indices. -/
namespace HiddenCircuits.Approximation.Initialization.MaskPair
open Complexity Complexity.OracleBlock
open SelfReduction.Runtime MaskEnumerationSemantics

 def state (data : BitString) (u v : ℕ) (out clock tmp rev : BitString) : Store 6 := fun i =>
  if i.val=0 then data else if i.val=1 then List.replicate u true
  else if i.val=2 then List.replicate v true else if i.val=3 then out
  else if i.val=4 then clock else if i.val=5 then tmp else rev

 def clearPorts : Fin 4 ↪ Fin 7 where
  toFun i := ⟨i.val+3,by omega⟩
  inj' := by intro i j h; apply Fin.ext; have hh:=congrArg Fin.val h; simp at hh; omega

noncomputable def clearOutput : OracleBlock 6 := rename clearAt clearPorts
noncomputable def program : OracleBlock 6 :=
  seq (copyOn 0 3 4 (by decide) (by decide) (by decide))
    (seq (copyOn 1 4 5 (by decide) (by decide) (by decide))
      (seq clearOutput (seq (copyOn 2 4 5 (by decide) (by decide) (by decide)) clearOutput)))

 theorem clearOutput_executes (g : BitString → ℕ) (data : BitString) (u v : ℕ)
    (word : BitString) (i : Fin word.length) :
    clearOutput.Executes g (state data u v word (List.replicate i.val true) [] [])
      (state data u v (word.set i.val false) [] [] []) (7*i.val+9) := by
  apply rename_executes_to clearAt clearPorts g (clearAt_index g word i)
  · funext j;fin_cases j <;> rfl
  · funext j;fin_cases j <;> rfl
  · intro j hj;fin_cases j
    all_goals first | rfl | exact (hj 0 rfl).elim | exact (hj 1 rfl).elim | exact (hj 2 rfl).elim | exact (hj 3 rfl).elim

 theorem program_executes (g : BitString → ℕ) {n : ℕ} (U : Finset (Fin n)) (u v : Fin n) :
    ∃ t, program.Executes g (state (mask U) u.val v.val [] [] [] [])
      (state (mask U) u.val v.val (mask ((U.erase u).erase v)) [] [] []) t ∧
      t ≤ 29*n+32 := by
  have h1 : (copyOn (0 : Fin 7) 3 4 (by decide) (by decide) (by decide)).Executes g
      (state (mask U) u.val v.val [] [] [] []) (state (mask U) u.val v.val (mask U) [] [] []) (5*n+2) := by
    convert copyOn_executes g (0 : Fin 7) 3 4 (by decide) (by decide) (by decide)
      (state (mask U) u.val v.val [] [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h2 : (copyOn (1 : Fin 7) 4 5 (by decide) (by decide) (by decide)).Executes g
      (state (mask U) u.val v.val (mask U) [] [] [])
      (state (mask U) u.val v.val (mask U) (List.replicate u.val true) [] []) (5*u.val+2) := by
    convert copyOn_executes g (1 : Fin 7) 4 5 (by decide) (by decide) (by decide)
      (state (mask U) u.val v.val (mask U) [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h3 : clearOutput.Executes g
      (state (mask U) u.val v.val (mask U) (List.replicate u.val true) [] [])
      (state (mask U) u.val v.val (mask (U.erase u)) [] [] []) (7*u.val+9) := by
    have hh:=clearOutput_executes g (mask U) u.val v.val (mask U) ⟨u.val,by simpa using u.isLt⟩
    simpa only [set_mask_erase] using hh
  have h4 : (copyOn (2 : Fin 7) 4 5 (by decide) (by decide) (by decide)).Executes g
      (state (mask U) u.val v.val (mask (U.erase u)) [] [] [])
      (state (mask U) u.val v.val (mask (U.erase u)) (List.replicate v.val true) [] []) (5*v.val+2) := by
    convert copyOn_executes g (2 : Fin 7) 4 5 (by decide) (by decide) (by decide)
      (state (mask U) u.val v.val (mask (U.erase u)) [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h5 : clearOutput.Executes g
      (state (mask U) u.val v.val (mask (U.erase u)) (List.replicate v.val true) [] [])
      (state (mask U) u.val v.val (mask ((U.erase u).erase v)) [] [] []) (7*v.val+9) := by
    have hh:=clearOutput_executes g (mask U) u.val v.val (mask (U.erase u)) ⟨v.val,by simpa using v.isLt⟩
    simpa only [set_mask_erase] using hh
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5))),?_⟩
  have hu:=u.isLt
  have hv:=v.isLt
  omega

 theorem program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (rename_queryFree _ _ clearAt_queryFree)
        (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (rename_queryFree _ _ clearAt_queryFree))))

noncomputable def on {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) : OracleBlock k := rename program φ

 theorem on_executes {k n : ℕ} (φ : Fin 7 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (U : Finset (Fin n)) (u v : Fin n)
    (hs : s∘φ=state (mask U) u.val v.val [] [] [] []) :
    ∃ t, (on φ).Executes g s (Function.update s (φ 3) (mask ((U.erase u).erase v))) t ∧
      t ≤ 29*n+32 := by
  obtain ⟨t,ht,hb⟩:=program_executes g U u v
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update s (φ 3) (mask ((U.erase u).erase v)))∘φ=
        Function.update (s∘φ) 3 (mask ((U.erase u).erase v)) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi
    exact Function.update_of_ne (hi 3).symm _ _

 theorem on_queryFree {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.Initialization.MaskPair
