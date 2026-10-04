import HiddenCircuits.DH.Runtime.WordArray

/-! Literal initialization of a repeated-word array from a preserved unary size. -/
namespace HiddenCircuits.DH.Runtime.WordArray
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

noncomputable def initializeBody : OracleBlock 7 := seq
  (copyOn 2 5 6 (by decide) (by decide) (by decide)) emit
noncomputable def initializeLoop : OracleBlock 7 := whilePop 3 initializeBody initializeBody
noncomputable def replicateArray : OracleBlock 7 := seq
  (copyOn 1 3 6 (by decide) (by decide) (by decide))
  (seq initializeLoop (reverseOn 4 0 (by decide)))

lemma initializeBody_executes (g : BitString → ℕ) (index value clock acc : BitString) :
    initializeBody.Executes g (state [] index value clock acc [] [] [])
      (state [] index value clock ((wordChunk value).reverse++acc) [] [] [])
      (11*value.length+11) := by
  have h1 : (copyOn (2 : Fin 8) 5 6 (by decide) (by decide) (by decide)).Executes g
      (state [] index value clock acc [] [] []) (state [] index value clock acc value [] [])
      (5*value.length+2) := by
    convert copyOn_executes g (2 : Fin 8) 5 6 (by decide) (by decide) (by decide)
      (state [] index value clock acc [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  convert seq_executes _ _ g h1 (emit_executes g [] index value clock acc value) using 1 <;> omega

lemma initializeLoop_execution (g : BitString → ℕ) (index value acc : BitString) (n : ℕ) :
    WhileExecution (3 : Fin 8) initializeBody initializeBody g
      (state [] index value (List.replicate n true) acc [] [] [])
      (state [] index value [] ((encodeBitList (List.replicate n value)).reverse++acc) [] [] [])
      (n*(11*value.length+13)+1) := by
  induction n generalizing acc with
  | zero => simpa [encodeBitList] using (WhileExecution.empty
      (stack:=(3 : Fin 8)) (B:=initializeBody) (C:=initializeBody)
      (g:=g) (state [] index value [] acc [] [] []) rfl)
  | succ n ih =>
    have hb := initializeBody_executes g index value (List.replicate n true) acc
    have hh := WhileExecution.one
      (show state [] index value (List.replicate (n+1) true) acc [] [] [] 3=true::List.replicate n true from rfl)
      (by simpa only [List.replicate_succ,pop_clock] using hb)
      (ih ((wordChunk value).reverse++acc))
    convert hh using 1
    · simp [List.replicate_succ,encodeBitList_eq_chunks,List.reverse_append,List.append_assoc]
    · ring

/-- Canonical repeated-word initialization clears every work stack and preserves
both the unary size and source word. The equality is the literal instruction count. -/
theorem initialize_executes (g : BitString → ℕ) (n : ℕ) (value : BitString) :
    replicateArray.Executes g (store [] (List.replicate n true) value)
      (store (encodeBitList (List.replicate n value)) (List.replicate n true) value)
      (n*(15*value.length+22)+8) := by
  have h1 : (copyOn (1 : Fin 8) 3 6 (by decide) (by decide) (by decide)).Executes g
      (store [] (List.replicate n true) value)
      (state [] (List.replicate n true) value (List.replicate n true) [] [] [] []) (5*n+2) := by
    convert copyOn_executes g (1 : Fin 8) 3 6 (by decide) (by decide) (by decide)
      (store [] (List.replicate n true) value) rfl using 1
    · funext i;fin_cases i <;> simp [state,store]
    · simp [state,store]
  have h2 := whilePop_executes _ _ _ g (initializeLoop_execution g (List.replicate n true) value [] n)
  simp only [List.append_nil] at h2
  have h3 : (reverseOn (4 : Fin 8) 0 (by decide)).Executes g
      (state [] (List.replicate n true) value [] (encodeBitList (List.replicate n value)).reverse [] [] [])
      (store (encodeBitList (List.replicate n value)) (List.replicate n true) value)
      (2*(encodeBitList (List.replicate n value)).length+1) := by
    convert reverseOn_executes g (4 : Fin 8) 0 (by decide)
      (state [] (List.replicate n true) value [] (encodeBitList (List.replicate n value)).reverse [] [] []) using 1
    · funext i;fin_cases i <;> simp [state,store]
    · simp [state]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1
  simp [encodeBitList_length,List.map_replicate,List.sum_replicate]
  ring

lemma initialize_time_polynomial (n W : ℕ) : n*(15*W+22)+8≤100*(n+W+1)^2 := by nlinarith

lemma initializeBody_queryFree : initializeBody.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) emit_queryFree
lemma initializeLoop_queryFree : initializeLoop.QueryFree :=
  whilePop_queryFree _ _ _ initializeBody_queryFree initializeBody_queryFree
lemma initialize_queryFree : replicateArray.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ initializeLoop_queryFree (reverseOn_queryFree _ _ _))

noncomputable def initializeOn {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : OracleBlock k := rename replicateArray φ

theorem initializeOn_executes {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (n : ℕ) (value : BitString) (hs : s∘φ=store [] (List.replicate n true) value) :
    (initializeOn φ).Executes g s
      (Function.update s (φ 0) (encodeBitList (List.replicate n value))) (n*(15*value.length+22)+8) := by
  apply rename_executes_to replicateArray φ g (initialize_executes g n value) hs
  · have he : (Function.update s (φ 0) (encodeBitList (List.replicate n value)))∘φ =
        Function.update (s∘φ) 0 (encodeBitList (List.replicate n value)) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi;exact Function.update_of_ne (hi 0).symm _ _

lemma initializeOn_queryFree {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : (initializeOn φ).QueryFree :=
  rename_queryFree _ _ initialize_queryFree

end HiddenCircuits.DH.Runtime.WordArray
