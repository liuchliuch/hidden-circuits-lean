import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionChoiceState

/-! One actual first-maximum selection iteration, including overwrite,
conditional winner replacement, source cleanup, and unary-index advance. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionChoice
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

noncomputable def overwrite (src dst : Fin 33) (hne : src≠dst) (hs : src≠15) (hd : dst≠15) : OracleBlock 32 :=
  seq (clear dst) (copyOn src dst 15 hne hs hd)

lemma overwrite_executes (g : BitString → ℕ) (src dst : Fin 33)
    (hne : src≠dst) (hs : src≠15) (hd : dst≠15) (s : Store 32) (hw : s 15=[]) :
    (overwrite src dst hne hs hd).Executes g s (Function.update s dst (s src))
      ((s dst).length+5*(s src).length+5) := by
  have hc := clear_executes g dst s
  have hp := copyOn_executes g src dst 15 hne hs hd (Function.update s dst [])
    (by simpa only [Function.update_of_ne hd.symm] using hw)
  have h := seq_executes _ _ g hc hp
  simp only [Function.update_self,Function.update_of_ne hne,List.append_nil,Function.update_idem] at h
  convert h using 1 <;> omega

noncomputable def writeBest : OracleBlock 32 :=
  seq (overwrite 9 5 (by decide) (by decide) (by decide))
    (seq (overwrite 11 6 (by decide) (by decide) (by decide))
      (seq (overwrite 12 7 (by decide) (by decide) (by decide))
        (GraphVerifier.Runtime.writeBool 8 true)))

lemma index_le {n : ℕ} (b : Best n) : index b≤n := by
  cases b with
  | none => simp [index]
  | some i => exact i.isLt.le

lemma writeBest_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A S R : Vector Bool n) (b : Best n) (i : Fin n) (clock eligible : BitString) :
    ∃t, writeBest.Executes g
      (state G A S R b i.val clock (List.replicate (UnitRecognitionScore.score G S i) true)
        (List.replicate (UnitRecognitionScore.score G A i) true) eligible [])
      (state G A S R (some i) i.val clock (List.replicate (UnitRecognitionScore.score G S i) true)
        (List.replicate (UnitRecognitionScore.score G A i) true) eligible []) t ∧ t≤30*(n+1) := by
  let s := state G A S R b i.val clock (List.replicate (UnitRecognitionScore.score G S i) true)
    (List.replicate (UnitRecognitionScore.score G A i) true) eligible []
  have h1 := overwrite_executes g 9 5 (by decide) (by decide) (by decide) s rfl
  have h2 := overwrite_executes g 11 6 (by decide) (by decide) (by decide)
    (Function.update s 5 (s 9)) rfl
  have h3 := overwrite_executes g 12 7 (by decide) (by decide) (by decide)
    (Function.update (Function.update s 5 (s 9)) 6 ((Function.update s 5 (s 9)) 11)) rfl
  have h4 := GraphVerifier.Runtime.writeBool_executes (8 : Fin 33) true g
    (Function.update (Function.update (Function.update s 5 (s 9)) 6
      ((Function.update s 5 (s 9)) 11)) 7
      ((Function.update (Function.update s 5 (s 9)) 6 ((Function.update s 5 (s 9)) 11)) 12))
  have h := seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4))
  refine ⟨index b+5*i.val+selectedScore G S b+5*UnitRecognitionScore.score G S i+
    selectedScore G A b+5*UnitRecognitionScore.score G A i+26,?_,?_⟩
  · convert h using 1
    · funext j;fin_cases j <;> simp [s,state,rawState,index,selectedScore]
    · simp [s,state,rawState];ring
  · have hi := i.isLt
    have hb := index_le b
    have h1 := selectedScore_le G S b
    have h2 := selectedScore_le G A b
    have h3 := UnitRecognitionScore.score_le G S i
    have h4 := UnitRecognitionScore.score_le G A i

    omega

noncomputable def select : OracleBlock 32 := branchPop 14 skip skip writeBest

lemma select_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A S R : Vector Bool n) (b : Best n) (i : Fin n) (clock : BitString) :
    ∃t, select.Executes g
      (state G A S R b i.val clock (List.replicate (UnitRecognitionScore.score G S i) true)
        (List.replicate (UnitRecognitionScore.score G A i) true) [R[i.val]] [prefer G A S R b i])
      (state G A S R (step G A S R i b) i.val clock (List.replicate (UnitRecognitionScore.score G S i) true)
        (List.replicate (UnitRecognitionScore.score G A i) true) [R[i.val]] []) t ∧ t≤30*(n+1)+2 := by
  have he : Function.update
      (state G A S R b i.val clock (List.replicate (UnitRecognitionScore.score G S i) true)
        (List.replicate (UnitRecognitionScore.score G A i) true) [R[i.val]] [prefer G A S R b i]) 14 [] =
      state G A S R b i.val clock (List.replicate (UnitRecognitionScore.score G S i) true)
        (List.replicate (UnitRecognitionScore.score G A i) true) [R[i.val]] [] := by
    funext j;fin_cases j <;> rfl
  cases hp : prefer G A S R b i with
  | false =>
    refine ⟨3,?_,by omega⟩
    apply branchPop_false 14 skip skip writeBest g rfl
    rw [hp] at he
    simpa [step,hp,he] using skip_executes g
      (state G A S R b i.val clock (List.replicate (UnitRecognitionScore.score G S i) true)
        (List.replicate (UnitRecognitionScore.score G A i) true) [R[i.val]] [])
  | true =>
    obtain ⟨t,ht,hb⟩ := writeBest_executes g G A S R b i clock [R[i.val]]
    refine ⟨t+2,?_,by omega⟩
    apply branchPop_true 14 skip skip writeBest g rfl
    rw [hp] at he
    simpa [step,hp,he] using ht

noncomputable def cleanReads : OracleBlock 32 := seq (clear 11) (seq (clear 12) (clear 13))
lemma cleanReads_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A S R : Vector Bool n) (b : Best n) (i : ℕ) (clock ns nd eligible : BitString) :
    cleanReads.Executes g (state G A S R b i clock ns nd eligible [])
      (state G A S R b i clock [] [] [] []) (ns.length+nd.length+eligible.length+7) := by
  have h1 : (clear (11 : Fin 33)).Executes g (state G A S R b i clock ns nd eligible [])
      (state G A S R b i clock [] nd eligible []) (ns.length+1) := by
    convert clear_executes g (11 : Fin 33) _ using 1
    funext j;fin_cases j <;> rfl
  have h2 : (clear (12 : Fin 33)).Executes g (state G A S R b i clock [] nd eligible [])
      (state G A S R b i clock [] [] eligible []) (nd.length+1) := by
    convert clear_executes g (12 : Fin 33) _ using 1
    funext j;fin_cases j <;> rfl
  have h3 : (clear (13 : Fin 33)).Executes g (state G A S R b i clock [] [] eligible [])
      (state G A S R b i clock [] [] [] []) (eligible.length+1) := by
    convert clear_executes g (13 : Fin 33) _ using 1
    funext j;fin_cases j <;> rfl
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1 <;> omega

noncomputable def body : OracleBlock 32 := seq (readScore false) (seq (readScore true)
  (seq readEligible (seq readBetter (seq select (seq cleanReads (push 9 true))))))

theorem body_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A S R : Vector Bool n) (b : Best n) (i : Fin n) (clock : BitString) :
    ∃t, body.Executes g (state G A S R b i.val clock [] [] [] [])
      (state G A S R (step G A S R i b) (i.val+1) clock [] [] [] []) t ∧
      t≤1500*(n+1)^3 := by
  obtain ⟨c1,h1,b1⟩ := readScore_false_executes g G A S R b i clock
  obtain ⟨c2,h2,b2⟩ := readScore_true_executes g G A S R b i clock _
  obtain ⟨c3,h3,b3⟩ := readEligible_executes g G A S R b i clock _ _
  obtain ⟨c4,h4,b4⟩ := readBetter_executes g G A S R b i clock
  obtain ⟨c5,h5,b5⟩ := select_executes g G A S R b i clock
  have h6 := cleanReads_executes g G A S R (step G A S R i b) i.val clock
    (List.replicate (UnitRecognitionScore.score G S i) true)
    (List.replicate (UnitRecognitionScore.score G A i) true) [R[i.val]]
  have h7 : (push (9 : Fin 33) true).Executes g
      (state G A S R (step G A S R i b) i.val clock [] [] [] [])
      (state G A S R (step G A S R i b) (i.val+1) clock [] [] [] []) 1 := by
    convert push_executes g (9 : Fin 33) true _ using 1
    funext j;fin_cases j <;> simp [state,rawState,List.replicate_succ]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 (seq_executes _ _ g h6 h7))))),?_⟩
  have hs := UnitRecognitionScore.score_le G S i
  have hd := UnitRecognitionScore.score_le G A i
  simp only [List.length_replicate,List.length_cons,List.length_nil]
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3)]

lemma overwrite_queryFree (src dst : Fin 33) (hne : src≠dst) (hs : src≠15) (hd : dst≠15) :
    (overwrite src dst hne hs hd).QueryFree := seq_queryFree _ _ (clear_queryFree _)
      (copyOn_queryFree _ _ _ _ _ _)
lemma writeBest_queryFree : writeBest.QueryFree := seq_queryFree _ _ (overwrite_queryFree _ _ _ _ _)
  (seq_queryFree _ _ (overwrite_queryFree _ _ _ _ _)
    (seq_queryFree _ _ (overwrite_queryFree _ _ _ _ _) (GraphVerifier.Runtime.writeBool_queryFree _ _)))
lemma body_queryFree : body.QueryFree := seq_queryFree _ _ (readScore_queryFree _)
  (seq_queryFree _ _ (readScore_queryFree _) (seq_queryFree _ _ readEligible_queryFree
    (seq_queryFree _ _ readBetter_queryFree (seq_queryFree _ _
      (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree writeBest_queryFree)
      (seq_queryFree _ _ (seq_queryFree _ _ (clear_queryFree _)
        (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))) (push_queryFree _ _))))))

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionChoice
