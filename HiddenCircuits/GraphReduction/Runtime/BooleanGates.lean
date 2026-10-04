import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision

/-! Fixed eight-input read-only Boolean gates, compiled from real copies and a
finite decision tree. Functions below are compile-time Boolean truth tables. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

def gate8Args (bits : Fin 8 → Bool) : List Bool := [bits 0,bits 1,bits 2,bits 3,bits 4,bits 5,bits 6,bits 7]
def gate8Store (bits : Fin 8 → Bool) (copied : ℕ) (output : BitString) : Store 17 :=
  ![[bits 0],[bits 1],[bits 2],[bits 3],[bits 4],[bits 5],[bits 6],[bits 7],if 0<copied then [bits 0] else [],if 1<copied then [bits 1] else [],if 2<copied then [bits 2] else [],if 3<copied then [bits 3] else [],if 4<copied then [bits 4] else [],if 5<copied then [bits 5] else [],if 6<copied then [bits 6] else [],if 7<copied then [bits 7] else [],output,[]]
def gate8Bits (bits : Fin 8 → Bool) : Fin 18 → Bool := ![bits 0,bits 1,bits 2,bits 3,bits 4,bits 5,bits 6,bits 7,bits 0,bits 1,bits 2,bits 3,bits 4,bits 5,bits 6,bits 7,false,false]
def gate8Inputs : List (Fin 18) := [8,9,10,11,12,13,14,15]
noncomputable def gate8Copy : OracleBlock 17 :=
  seq (copyOn 0 8 17 (by decide) (by decide) (by decide)) (seq (copyOn 1 9 17 (by decide) (by decide) (by decide)) (seq (copyOn 2 10 17 (by decide) (by decide) (by decide)) (seq (copyOn 3 11 17 (by decide) (by decide) (by decide)) (seq (copyOn 4 12 17 (by decide) (by decide) (by decide)) (seq (copyOn 5 13 17 (by decide) (by decide) (by decide)) (seq (copyOn 6 14 17 (by decide) (by decide) (by decide)) (copyOn 7 15 17 (by decide) (by decide) (by decide))))))))
noncomputable def gate8 (f : List Bool → Bool) : OracleBlock 17 :=
  seq gate8Copy (GraphVerifier.Runtime.decision 16 gate8Inputs f)

theorem gate8Copy_executes (g : BitString → ℕ) (bits : Fin 8 → Bool) :
    gate8Copy.Executes g (gate8Store bits 0 []) (gate8Store bits 8 []) 70 := by
  have h0 : (copyOn (0 : Fin 18) 8 17 (by decide) (by decide) (by decide)).Executes g
      (gate8Store bits 0 []) (gate8Store bits 1 []) 7 := by
    convert copyOn_executes g (0 : Fin 18) 8 17 (by decide) (by decide) (by decide) (gate8Store bits 0 []) rfl using 1
    funext j; fin_cases j <;> simp [gate8Store]
  have h1 : (copyOn (1 : Fin 18) 9 17 (by decide) (by decide) (by decide)).Executes g
      (gate8Store bits 1 []) (gate8Store bits 2 []) 7 := by
    convert copyOn_executes g (1 : Fin 18) 9 17 (by decide) (by decide) (by decide) (gate8Store bits 1 []) rfl using 1
    funext j; fin_cases j <;> simp [gate8Store]
  have h2 : (copyOn (2 : Fin 18) 10 17 (by decide) (by decide) (by decide)).Executes g
      (gate8Store bits 2 []) (gate8Store bits 3 []) 7 := by
    convert copyOn_executes g (2 : Fin 18) 10 17 (by decide) (by decide) (by decide) (gate8Store bits 2 []) rfl using 1
    funext j; fin_cases j <;> simp [gate8Store]
  have h3 : (copyOn (3 : Fin 18) 11 17 (by decide) (by decide) (by decide)).Executes g
      (gate8Store bits 3 []) (gate8Store bits 4 []) 7 := by
    convert copyOn_executes g (3 : Fin 18) 11 17 (by decide) (by decide) (by decide) (gate8Store bits 3 []) rfl using 1
    funext j; fin_cases j <;> simp [gate8Store]
  have h4 : (copyOn (4 : Fin 18) 12 17 (by decide) (by decide) (by decide)).Executes g
      (gate8Store bits 4 []) (gate8Store bits 5 []) 7 := by
    convert copyOn_executes g (4 : Fin 18) 12 17 (by decide) (by decide) (by decide) (gate8Store bits 4 []) rfl using 1
    funext j; fin_cases j <;> simp [gate8Store]
  have h5 : (copyOn (5 : Fin 18) 13 17 (by decide) (by decide) (by decide)).Executes g
      (gate8Store bits 5 []) (gate8Store bits 6 []) 7 := by
    convert copyOn_executes g (5 : Fin 18) 13 17 (by decide) (by decide) (by decide) (gate8Store bits 5 []) rfl using 1
    funext j; fin_cases j <;> simp [gate8Store]
  have h6 : (copyOn (6 : Fin 18) 14 17 (by decide) (by decide) (by decide)).Executes g
      (gate8Store bits 6 []) (gate8Store bits 7 []) 7 := by
    convert copyOn_executes g (6 : Fin 18) 14 17 (by decide) (by decide) (by decide) (gate8Store bits 6 []) rfl using 1
    funext j; fin_cases j <;> simp [gate8Store]
  have h7 : (copyOn (7 : Fin 18) 15 17 (by decide) (by decide) (by decide)).Executes g
      (gate8Store bits 7 []) (gate8Store bits 8 []) 7 := by
    convert copyOn_executes g (7 : Fin 18) 15 17 (by decide) (by decide) (by decide) (gate8Store bits 7 []) rfl using 1
    funext j; fin_cases j <;> simp [gate8Store]
  exact seq_executes _ _ g h0 (seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 (seq_executes _ _ g h5 (seq_executes _ _ g h6 (h7)))))))

theorem gate8_executes (g : BitString → ℕ) (f : List Bool → Bool) (bits : Fin 8 → Bool) :
    (gate8 f).Executes g (gate8Store bits 0 []) (gate8Store bits 0 [f (gate8Args bits)]) 92 := by
  have h := GraphVerifier.Runtime.decision_executes (16 : Fin 18) gate8Inputs
    (by decide +kernel) (by decide +kernel) f (gate8Bits bits) g (gate8Store bits 8 [])
    (by intro j hj; fin_cases j <;> simp [gate8Inputs,gate8Store,gate8Bits] at *)
  have he : eraseStore gate8Inputs (gate8Store bits 8 [])=gate8Store bits 0 [] := by
    funext j; fin_cases j <;> simp [eraseStore,gate8Inputs,gate8Store]
  rw [he] at h
  have hd : (GraphVerifier.Runtime.decision 16 gate8Inputs f).Executes g
      (gate8Store bits 8 []) (gate8Store bits 0 [f (gate8Args bits)]) 20 := by
    convert h using 1
    funext j; fin_cases j <;> rfl
  exact seq_executes _ _ g (gate8Copy_executes g bits) hd

lemma gate8_queryFree (f : List Bool → Bool) : (gate8 f).QueryFree := by
  have hc : gate8Copy.QueryFree :=
    seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) ((copyOn_queryFree _ _ _ _ _ _))))))))
  exact seq_queryFree _ _ hc (GraphVerifier.Runtime.decision_queryFree _ _ _)

noncomputable def gate8On {k : ℕ} (φ : Fin 18 ↪ Fin (k+1)) (f : List Bool → Bool) : OracleBlock k :=
  rename (gate8 f) φ

theorem gate8On_executes {k : ℕ} (φ : Fin 18 ↪ Fin (k+1)) (g : BitString → ℕ)
    (f : List Bool → Bool) (bits : Fin 8 → Bool) (s : Store k)
    (hs : s∘φ=gate8Store bits 0 []) :
    (gate8On φ f).Executes g s (Function.update s (φ 16) [f (gate8Args bits)]) 92 := by
  apply rename_executes_to (gate8 f) φ g (gate8_executes g f bits) hs
  · have he : (Function.update s (φ 16) [f (gate8Args bits)])∘φ =
        Function.update (s∘φ) 16 [f (gate8Args bits)] := by
      funext i; simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i; fin_cases i <;> rfl
  · intro i hi; exact Function.update_of_ne (hi 16).symm _ _
lemma gate8On_queryFree {k : ℕ} (φ : Fin 18 ↪ Fin (k+1)) (f : List Bool → Bool) : (gate8On φ f).QueryFree :=
  rename_queryFree _ _ (gate8_queryFree f)

end HiddenCircuits.GraphReduction.Runtime
