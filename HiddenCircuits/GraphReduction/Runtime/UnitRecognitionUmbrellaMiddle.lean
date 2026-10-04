import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrellaInner

/-! The middle tail scan copies only the tail after its chosen second label,
so every innermost visit has three strictly increasing list positions. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrella
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

noncomputable def middleBody : OracleBlock 18 := seq (parseLabel 1)
  (seq (copyOn 5 6 14 (by decide) (by decide) (by decide)) (seq innerLoop (clear 8)))
noncomputable def middleLoop : OracleBlock 18 := whilePop 5 middleBody middleBody

theorem middleBody_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (u v : Fin n) (original outer : BitString) (vs : List (Fin n)) (acc : Bool) :
    ∃t, middleBody.Executes g
      (state n u.val 0 0 G.bits original outer (pairBits (List.replicate v.val true) (encoded vs)) [] [acc] [] [] [] [] [])
      (state n u.val 0 0 G.bits original outer (encoded vs) [] [acc && inner G u v vs] [] [] [] [] []) t ∧
      t≤500*(n+1)^2*(vs.length+1) := by
  have h1 : (parseLabel 1).Executes g
      (state n u.val 0 0 G.bits original outer (pairBits (List.replicate v.val true) (encoded vs)) [] [acc] [] [] [] [] [])
      (state n u.val v.val 0 G.bits original outer (encoded vs) [] [acc] [] [] [] [] []) (5*v.val+7) := by
    convert UnitRecognitionLabelRead.on_executes (parseEmbedding 1) g
      (state n u.val 0 0 G.bits original outer (pairBits (List.replicate v.val true) (encoded vs)) [] [acc] [] [] [] [] [])
      (state n u.val v.val 0 G.bits original outer (encoded vs) [] [acc] [] [] [] [] [])
      (List.replicate v.val true) (encoded vs)
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim) using 1
    simp
  have h2 : (copyOn (5 : Fin 19) 6 14 (by decide) (by decide) (by decide)).Executes g
      (state n u.val v.val 0 G.bits original outer (encoded vs) [] [acc] [] [] [] [] [])
      (state n u.val v.val 0 G.bits original outer (encoded vs) (encoded vs) [acc] [] [] [] [] [])
      (5*(encoded vs).length+2) := by
    convert copyOn_executes g (5 : Fin 19) 6 14 (by decide) (by decide) (by decide)
      (state n u.val v.val 0 G.bits original outer (encoded vs) [] [acc] [] [] [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  obtain ⟨c,h3,b3⟩ := innerLoop_execution g G u v original outer (encoded vs) vs acc
  have h4 : (clear (8 : Fin 19)).Executes g
      (state n u.val v.val 0 G.bits original outer (encoded vs) [] [acc && inner G u v vs] [] [] [] [] [])
      (state n u.val 0 0 G.bits original outer (encoded vs) [] [acc && inner G u v vs] [] [] [] [] []) (v.val+1) := by
    convert clear_executes g (8 : Fin 19) _ using 1
    · funext i;fin_cases i <;> rfl
    · simp [state]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2
    (seq_executes _ _ g (whilePop_executes _ _ _ g h3) h4)),?_⟩
  have hl := encoded_length_le vs
  have hv := v.isLt
  nlinarith [Nat.zero_le (n^2*vs.length),Nat.zero_le (n*vs.length)]

theorem middleLoop_execution (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (u : Fin n) (original outer : BitString) (ls : List (Fin n)) (acc : Bool) :
    ∃t, WhileExecution (5 : Fin 19) middleBody middleBody g
      (state n u.val 0 0 G.bits original outer (encoded ls) [] [acc] [] [] [] [] [])
      (state n u.val 0 0 G.bits original outer [] [] [acc && middle G u ls] [] [] [] [] []) t ∧
      t≤600*(n+1)^2*(ls.length+1)^2 := by
  induction ls generalizing acc with
  | nil =>
    refine ⟨1,?_,?_⟩
    · simpa only [middle,Bool.and_true,encoded_nil] using (WhileExecution.empty
        (stack := (5 : Fin 19)) (B := middleBody) (C := middleBody) (g := g)
        (state n u.val 0 0 G.bits original outer [] [] [acc] [] [] [] [] []) rfl)
    · simp; have hn := Nat.one_le_pow 2 (n+1) (by omega);omega
  | cons v vs ih =>
    obtain ⟨c,hc,hcb⟩ := middleBody_executes g G u v original outer vs acc
    obtain ⟨t,ht,htb⟩ := ih (acc && inner G u v vs)
    have he : Function.update
        (state n u.val 0 0 G.bits original outer (encoded (v::vs)) [] [acc] [] [] [] [] []) 5
        (pairBits (List.replicate v.val true) (encoded vs)) =
        state n u.val 0 0 G.bits original outer (pairBits (List.replicate v.val true) (encoded vs)) [] [acc] [] [] [] [] [] := by
      funext i;fin_cases i <;> rfl
    have h := WhileExecution.one (show state n u.val 0 0 G.bits original outer
      (encoded (v::vs)) [] [acc] [] [] [] [] [] 5=true::pairBits (List.replicate v.val true) (encoded vs) from rfl)
      (by rw [he];exact hc) ht
    refine ⟨1+c+1+t,?_,?_⟩
    · simpa only [middle,Bool.and_assoc] using h
    · simp only [List.length_cons]
      nlinarith [Nat.zero_le (n^2*vs.length),Nat.zero_le (n*vs.length)]

lemma middleBody_queryFree : middleBody.QueryFree := seq_queryFree _ _ (UnitRecognitionLabelRead.on_queryFree _)
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ innerLoop_queryFree (clear_queryFree _)))
lemma middleLoop_queryFree : middleLoop.QueryFree := whilePop_queryFree _ _ _ middleBody_queryFree middleBody_queryFree

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrella
