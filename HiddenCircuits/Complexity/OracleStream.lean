import HiddenCircuits.Complexity.OracleCleanup

/-! Sequential bitstream emission by actual finite blocks. A fixed finite list
of component blocks compiles to finite code; every continuation is charged. -/
namespace HiddenCircuits.Complexity.OracleBlock
variable {k : ℕ}

noncomputable def sequence : List (OracleBlock k) → OracleBlock k
  | [] => skip
  | B::Bs => seq B (sequence Bs)

/-- A fixed list of independently proved emitters concatenates their literal
streams in order (the output stack stores the reverse), preserving all metadata. -/
theorem sequence_emit {α : Type*} (g : BitString → ℕ) (items : List α)
    (block : α → OracleBlock k) (chunk : α → BitString) (cost : α → ℕ)
    (s : Store k) (output : Fin (k+1))
    (h : ∀ a ∈ items, ∀ acc : BitString,
      (block a).Executes g (Function.update s output acc)
        (Function.update s output ((chunk a).reverse++acc)) (cost a)) (acc : BitString) :
    (sequence (items.map block)).Executes g (Function.update s output acc)
      (Function.update s output ((items.flatMap chunk).reverse++acc))
      ((items.map cost).sum+2*items.length+1) := by
  induction items generalizing acc with
  | nil => simpa [sequence] using skip_executes g (Function.update s output acc)
  | cons a items ih =>
    have ha := h a (by simp) acc
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) ((chunk a).reverse++acc)
    have hs := seq_executes _ _ g ha ht
    convert hs using 1
    · simp [List.reverse_append,List.append_assoc]
    · simp;omega

/-- Bounded-cost variant: each real component may take a data-dependent number
of instructions, but its proved bound composes with every charged continuation. -/
theorem sequence_emit_bounded {α : Type*} (g : BitString → ℕ) (items : List α)
    (block : α → OracleBlock k) (chunk : α → BitString) (bound : α → ℕ)
    (s : Store k) (output : Fin (k+1))
    (h : ∀ a ∈ items, ∀ acc : BitString, ∃ cost,
      (block a).Executes g (Function.update s output acc)
        (Function.update s output ((chunk a).reverse++acc)) cost ∧ cost ≤ bound a) (acc : BitString) :
    ∃ cost, (sequence (items.map block)).Executes g (Function.update s output acc)
      (Function.update s output ((items.flatMap chunk).reverse++acc)) cost ∧
      cost ≤ (items.map bound).sum+2*items.length+1 := by
  induction items generalizing acc with
  | nil => exact ⟨1,by simpa [sequence] using skip_executes g (Function.update s output acc),by simp⟩
  | cons a items ih =>
    obtain ⟨ca,ha,hba⟩ := h a (by simp) acc
    obtain ⟨ct,ht,hbt⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) ((chunk a).reverse++acc)
    refine ⟨ca+ct+2,?_,?_⟩
    · have hs := seq_executes _ _ g ha ht
      simpa [List.reverse_append,List.append_assoc] using hs
    · simp;omega

lemma sequence_queryFree (blocks : List (OracleBlock k)) (h : ∀ B ∈ blocks, B.QueryFree) :
    (sequence blocks).QueryFree := by
  induction blocks with
  | nil => exact skip_queryFree
  | cons B Bs ih => exact seq_queryFree _ _ (h B (by simp)) (ih (fun C hc => h C (List.mem_cons_of_mem _ hc)))

end HiddenCircuits.Complexity.OracleBlock
