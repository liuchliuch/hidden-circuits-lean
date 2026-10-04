import HiddenCircuits.Complexity.CNFCloneEmitter.UnarySplit
import HiddenCircuits.Complexity.OracleMove

/-! A literal unary maximum, used only on polynomially bounded grid values.
The second operand is consumed and all scratch stacks are restored. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMax
open Complexity Complexity.OracleBlock

def state (a b c : ℕ) (flag : BitString) : Store 4 := fun i=>
  if i.val=0 then List.replicate a true else if i.val=1 then List.replicate b true
  else if i.val=2 then List.replicate c true else if i.val=3 then flag else []

def splitEmbedding : Fin 3 ↪ Fin 5 where
  toFun i := ![1,0,3] i
  inj' := by decide +kernel
noncomputable def program : OracleBlock 4 :=
  seq (copyOn 0 2 4 (by decide) (by decide) (by decide))
    (seq (CNFCloneEmitter.UnarySplit.on splitEmbedding)
      (seq (clear 3) (seq (reverseOn 2 0 (by decide)) (reverseOn 1 0 (by decide)))))

theorem program_executes (g : BitString → ℕ) (a b : ℕ) :
    ∃t,program.Executes g (state a b 0 []) (state (max a b) 0 0 []) t ∧
      t≤20*(a+b+1) := by
  have h1 : (copyOn (0 : Fin 5) 2 4 (by decide) (by decide) (by decide)).Executes g
      (state a b 0 []) (state a b a []) (5*a+2) := by
    convert copyOn_executes g (0 : Fin 5) 2 4 (by decide) (by decide) (by decide) (state a b 0 []) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  obtain ⟨c,hc,cb⟩ := CNFCloneEmitter.UnarySplit.on_executes splitEmbedding g (state a b a []) b a
    (by funext i;fin_cases i <;> rfl)
  have he : Function.update (Function.update (Function.update (state a b a []) (splitEmbedding 0)
      (List.replicate (b-a) true)) (splitEmbedding 1) []) (splitEmbedding 2) [decide (b<a)] =
      state 0 (b-a) a [decide (b<a)] := by funext i;fin_cases i <;> rfl
  rw [he] at hc
  have h3 : (clear (3 : Fin 5)).Executes g (state 0 (b-a) a [decide (b<a)])
      (state 0 (b-a) a []) 2 := by
    convert clear_executes g (3 : Fin 5) _ using 1
    funext i;fin_cases i <;> rfl
  have h4 : (reverseOn (2 : Fin 5) 0 (by decide)).Executes g (state 0 (b-a) a [])
      (state a (b-a) 0 []) (2*a+1) := by
    convert reverseOn_executes g (2 : Fin 5) 0 (by decide) (state 0 (b-a) a []) using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h5 : (reverseOn (1 : Fin 5) 0 (by decide)).Executes g (state a (b-a) 0 [])
      (state (max a b) 0 0 []) (2*(b-a)+1) := by
    have hm : b-a+a=max a b := by omega
    convert reverseOn_executes g (1 : Fin 5) 0 (by decide) (state a (b-a) 0 []) using 1
    · funext i;fin_cases i <;> simp [state,←List.replicate_add,hm]
    · simp [state]
  exact ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g hc
    (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5))),by omega⟩

lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (CNFCloneEmitter.UnarySplit.on_queryFree _)
      (seq_queryFree _ _ (clear_queryFree _)
        (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (reverseOn_queryFree _ _ _))))

noncomputable def on {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s t : Store k) (a b : ℕ) (hs : s∘φ=state a b 0 [])
    (ht : t∘φ=state (max a b) 0 0 [])
    (hf : ∀i,(∀j,φ j≠i)→t i=s i) :
    ∃c,(on φ).Executes g s t c ∧ c≤20*(a+b+1) := by
  obtain ⟨c,hc,hb⟩ := program_executes g a b
  exact ⟨c,rename_executes_to _ φ g hc hs ht hf,hb⟩
lemma on_queryFree {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMax
