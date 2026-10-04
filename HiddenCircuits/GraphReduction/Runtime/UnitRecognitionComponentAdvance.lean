import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponentState

/-! A chosen original label is inserted into the selected mask, removed from
the remaining mask, and emitted to the label array by actual finite blocks. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

lemma updateSelected_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (s : Data n) (v : Fin n) (clock score degree found : BitString) :
    ∃t, (updateMask true).Executes g
      (store G A s clock (List.replicate v.val true) score degree found [true] [])
      (store G A ⟨s.order,s.selected.set v.val true,s.remaining⟩ clock
        (List.replicate v.val true) score degree found [true] []) t ∧ t≤100*(n+1)^2 := by
  obtain ⟨t,ht,hb⟩ := DH.Runtime.WordArray.updateOn_executes (updateEmbedding true) g
    (store G A s clock (List.replicate v.val true) score degree found [true] [])
    (liveWords s.selected) v.val [true] (by funext i;fin_cases i <;> rfl)
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> simp [store,UnitRecognitionChoice.rawState,updateEmbedding,liveBits_set]
  · change t≤DH.Runtime.WordArray.updateBound (liveBits s.selected).length v.val 1 at hb
    rw [liveBits_length] at hb
    unfold DH.Runtime.WordArray.updateBound at hb
    have hi := v.isLt
    have hm := Nat.mul_le_mul_left (44*n+20) hi.le
    nlinarith

lemma updateRemaining_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (s : Data n) (v : Fin n) (clock score degree found : BitString) :
    ∃t, (updateMask false).Executes g
      (store G A s clock (List.replicate v.val true) score degree found [false] [])
      (store G A ⟨s.order,s.selected,s.remaining.set v.val false⟩ clock
        (List.replicate v.val true) score degree found [false] []) t ∧ t≤100*(n+1)^2 := by
  obtain ⟨t,ht,hb⟩ := DH.Runtime.WordArray.updateOn_executes (updateEmbedding false) g
    (store G A s clock (List.replicate v.val true) score degree found [false] [])
    (liveWords s.remaining) v.val [false] (by funext i;fin_cases i <;> rfl)
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> simp [store,UnitRecognitionChoice.rawState,updateEmbedding,liveBits_set]
  · change t≤DH.Runtime.WordArray.updateBound (liveBits s.remaining).length v.val 1 at hb
    rw [liveBits_length] at hb
    unfold DH.Runtime.WordArray.updateBound at hb
    have hi := v.isLt
    have hm := Nat.mul_le_mul_left (44*n+20) hi.le
    nlinarith

noncomputable def advanceProgram : OracleBlock 36 :=
  seq (push 35 true) (seq (updateMask true) (seq (clear 35)
    (seq (push 35 false) (seq (updateMask false) (seq (clear 35) emitLabel)))))

theorem advanceProgram_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (s : Data n) (v : Fin n) (clock score degree found : BitString) :
    ∃t, advanceProgram.Executes g
      (store G A s clock (List.replicate v.val true) score degree found [] [])
      (store G A (advance s v) clock (List.replicate v.val true) score degree found [] []) t ∧
      t≤250*(n+1)^2 := by
  let s1 : Data n := ⟨s.order,s.selected.set v.val true,s.remaining⟩
  let s2 : Data n := ⟨s.order,s.selected.set v.val true,s.remaining.set v.val false⟩
  have h1 : (push (35 : Fin 37) true).Executes g
      (store G A s clock (List.replicate v.val true) score degree found [] [])
      (store G A s clock (List.replicate v.val true) score degree found [true] []) 1 := by
    convert push_executes g (35 : Fin 37) true _ using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨c1,h2,b1⟩ := updateSelected_executes g G A s v clock score degree found
  have h3 : (clear (35 : Fin 37)).Executes g
      (store G A s1 clock (List.replicate v.val true) score degree found [true] [])
      (store G A s1 clock (List.replicate v.val true) score degree found [] []) 2 := by
    convert clear_executes g (35 : Fin 37) _ using 1
    funext i;fin_cases i <;> rfl
  have h4 : (push (35 : Fin 37) false).Executes g
      (store G A s1 clock (List.replicate v.val true) score degree found [] [])
      (store G A s1 clock (List.replicate v.val true) score degree found [false] []) 1 := by
    convert push_executes g (35 : Fin 37) false _ using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨c2,h5,b2⟩ := updateRemaining_executes g G A s1 v clock score degree found
  have h6 : (clear (35 : Fin 37)).Executes g
      (store G A s2 clock (List.replicate v.val true) score degree found [false] [])
      (store G A s2 clock (List.replicate v.val true) score degree found [] []) 2 := by
    convert clear_executes g (35 : Fin 37) _ using 1
    funext i;fin_cases i <;> rfl
  have h7 := emitLabel_executes g G A s2 v clock score degree found []
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 (seq_executes _ _ g h6 h7))))),?_⟩
  have hi := v.isLt
  nlinarith

lemma advanceProgram_queryFree : advanceProgram.QueryFree := seq_queryFree _ _ (push_queryFree _ _)
  (seq_queryFree _ _ (DH.Runtime.WordArray.updateOn_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (push_queryFree _ _)
      (seq_queryFree _ _ (DH.Runtime.WordArray.updateOn_queryFree _)
        (seq_queryFree _ _ (clear_queryFree _) emitLabel_queryFree)))))

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
