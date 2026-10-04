import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrellaMiddle

/-! Complete finite-stack umbrella checking by three nested canonical tail
scans. The order is computed internally by the component program. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrella
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

noncomputable def outerBody : OracleBlock 18 := seq (parseLabel 0)
  (seq (copyOn 4 5 14 (by decide) (by decide) (by decide)) (seq middleLoop (clear 7)))
noncomputable def outerLoop : OracleBlock 18 := whilePop 4 outerBody outerBody
noncomputable def program : OracleBlock 18 := seq (push 3 true)
  (seq (copyOn 2 4 14 (by decide) (by decide) (by decide)) outerLoop)

theorem outerBody_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (u : Fin n) (original : BitString) (us : List (Fin n)) (acc : Bool) :
    ∃t, outerBody.Executes g
      (state n 0 0 0 G.bits original (pairBits (List.replicate u.val true) (encoded us)) [] [] [acc] [] [] [] [] [])
      (state n 0 0 0 G.bits original (encoded us) [] [] [acc && middle G u us] [] [] [] [] []) t ∧
      t≤700*(n+1)^2*(us.length+1)^2 := by
  have h1 : (parseLabel 0).Executes g
      (state n 0 0 0 G.bits original (pairBits (List.replicate u.val true) (encoded us)) [] [] [acc] [] [] [] [] [])
      (state n u.val 0 0 G.bits original (encoded us) [] [] [acc] [] [] [] [] []) (5*u.val+7) := by
    convert UnitRecognitionLabelRead.on_executes (parseEmbedding 0) g
      (state n 0 0 0 G.bits original (pairBits (List.replicate u.val true) (encoded us)) [] [] [acc] [] [] [] [] [])
      (state n u.val 0 0 G.bits original (encoded us) [] [] [acc] [] [] [] [] [])
      (List.replicate u.val true) (encoded us)
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim) using 1
    simp
  have h2 : (copyOn (4 : Fin 19) 5 14 (by decide) (by decide) (by decide)).Executes g
      (state n u.val 0 0 G.bits original (encoded us) [] [] [acc] [] [] [] [] [])
      (state n u.val 0 0 G.bits original (encoded us) (encoded us) [] [acc] [] [] [] [] [])
      (5*(encoded us).length+2) := by
    convert copyOn_executes g (4 : Fin 19) 5 14 (by decide) (by decide) (by decide)
      (state n u.val 0 0 G.bits original (encoded us) [] [] [acc] [] [] [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  obtain ⟨c,h3,b3⟩ := middleLoop_execution g G u original (encoded us) us acc
  have h4 : (clear (7 : Fin 19)).Executes g
      (state n u.val 0 0 G.bits original (encoded us) [] [] [acc && middle G u us] [] [] [] [] [])
      (state n 0 0 0 G.bits original (encoded us) [] [] [acc && middle G u us] [] [] [] [] []) (u.val+1) := by
    convert clear_executes g (7 : Fin 19) _ using 1
    · funext i;fin_cases i <;> rfl
    · simp [state]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2
    (seq_executes _ _ g (whilePop_executes _ _ _ g h3) h4)),?_⟩
  have hl := encoded_length_le us
  have hu := u.isLt
  nlinarith [Nat.zero_le (n^2*us.length),Nat.zero_le (n*us.length),Nat.zero_le (n^2*us.length^2)]

theorem outerLoop_execution (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (original : BitString) (ls : List (Fin n)) (acc : Bool) :
    ∃t, WhileExecution (4 : Fin 19) outerBody outerBody g
      (state n 0 0 0 G.bits original (encoded ls) [] [] [acc] [] [] [] [] [])
      (state n 0 0 0 G.bits original [] [] [] [acc && check G ls] [] [] [] [] []) t ∧
      t≤800*(n+1)^2*(ls.length+1)^3 := by
  induction ls generalizing acc with
  | nil =>
    refine ⟨1,?_,?_⟩
    · simpa only [check,Bool.and_true,encoded_nil] using (WhileExecution.empty
        (stack := (4 : Fin 19)) (B := outerBody) (C := outerBody) (g := g)
        (state n 0 0 0 G.bits original [] [] [] [acc] [] [] [] [] []) rfl)
    · simp; have hn := Nat.one_le_pow 2 (n+1) (by omega);omega
  | cons u us ih =>
    obtain ⟨c,hc,hcb⟩ := outerBody_executes g G u original us acc
    obtain ⟨t,ht,htb⟩ := ih (acc && middle G u us)
    have he : Function.update
        (state n 0 0 0 G.bits original (encoded (u::us)) [] [] [acc] [] [] [] [] []) 4
        (pairBits (List.replicate u.val true) (encoded us)) =
        state n 0 0 0 G.bits original (pairBits (List.replicate u.val true) (encoded us)) [] [] [acc] [] [] [] [] [] := by
      funext i;fin_cases i <;> rfl
    have h := WhileExecution.one (show state n 0 0 0 G.bits original
      (encoded (u::us)) [] [] [acc] [] [] [] [] [] 4=true::pairBits (List.replicate u.val true) (encoded us) from rfl)
      (by rw [he];exact hc) ht
    refine ⟨1+c+1+t,?_,?_⟩
    · simpa only [check,Bool.and_assoc] using h
    · simp only [List.length_cons]
      nlinarith [Nat.zero_le (n^2*us.length),Nat.zero_le (n*us.length),Nat.zero_le (n^2*us.length^2)]

theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (ls : List (Fin n)) :
    ∃t, program.Executes g (state n 0 0 0 G.bits (encoded ls) [] [] [] [] [] [] [] [] [])
      (state n 0 0 0 G.bits (encoded ls) [] [] [] [check G ls] [] [] [] [] []) t ∧
      t≤900*(n+1)^2*(ls.length+1)^3 := by
  have h1 : (push (3 : Fin 19) true).Executes g
      (state n 0 0 0 G.bits (encoded ls) [] [] [] [] [] [] [] [] [])
      (state n 0 0 0 G.bits (encoded ls) [] [] [] [true] [] [] [] [] []) 1 := by
    convert push_executes g (3 : Fin 19) true _ using 1
    funext i;fin_cases i <;> rfl
  have h2 : (copyOn (2 : Fin 19) 4 14 (by decide) (by decide) (by decide)).Executes g
      (state n 0 0 0 G.bits (encoded ls) [] [] [] [true] [] [] [] [] [])
      (state n 0 0 0 G.bits (encoded ls) (encoded ls) [] [] [true] [] [] [] [] []) (5*(encoded ls).length+2) := by
    convert copyOn_executes g (2 : Fin 19) 4 14 (by decide) (by decide) (by decide)
      (state n 0 0 0 G.bits (encoded ls) [] [] [] [true] [] [] [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  obtain ⟨c,h3,b3⟩ := outerLoop_execution g G (encoded ls) ls true
  simp only [Bool.true_and] at h3
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (whilePop_executes _ _ _ g h3)),?_⟩
  have hl := encoded_length_le ls
  nlinarith [Nat.zero_le (n^2*ls.length),Nat.zero_le (n*ls.length),Nat.zero_le (n^2*ls.length^2),
    Nat.zero_le (n*ls.length^2),Nat.zero_le (n^2*ls.length^3),Nat.zero_le (n*ls.length^3)]

lemma outerBody_queryFree : outerBody.QueryFree := seq_queryFree _ _ (UnitRecognitionLabelRead.on_queryFree _)
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ middleLoop_queryFree (clear_queryFree _)))
lemma outerLoop_queryFree : outerLoop.QueryFree := whilePop_queryFree _ _ _ outerBody_queryFree outerBody_queryFree
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (push_queryFree _ _)
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) outerLoop_queryFree)

noncomputable def on {k : ℕ} (φ : Fin 19 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 19 ↪ Fin (k+1)) (g : BitString → ℕ)
    {n : ℕ} (G : MatrixData n) (ls : List (Fin n)) (s : Store k)
    (hs : s∘φ=state n 0 0 0 G.bits (encoded ls) [] [] [] [] [] [] [] [] []) :
    ∃t, (on φ).Executes g s (Function.update s (φ 3) [check G ls]) t ∧
      t≤900*(n+1)^2*(ls.length+1)^3 := by
  obtain ⟨t,ht,hb⟩ := program_executes g G ls
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update s (φ 3) [check G ls])∘φ=Function.update (s∘φ) 3 [check G ls] := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi;exact Function.update_of_ne (hi 3).symm _ _
lemma on_queryFree {k : ℕ} (φ : Fin 19 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrella
