import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponentAdvance

/-! One complete physically implemented greedy component step. The positive
frontier test consumes a real unary score bit, and absent/zero-frontier choices
are stuttering steps. All temporary winner data is then physically cleared. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

noncomputable def selectAction : OracleBlock 36 := branchPop 6 skip advanceProgram advanceProgram

def winner {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (s : Data n) :=
  UnitRecognitionChoice.choose G A s.selected s.remaining
def winnerScore {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (s : Data n) :=
  UnitRecognitionChoice.selectedScore G s.selected (winner G A s)
def winnerDegree {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (s : Data n) :=
  UnitRecognitionChoice.selectedScore G A (winner G A s)

theorem selectAction_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (s : Data n) (clock : BitString) :
    ∃t, selectAction.Executes g
      (store G A s clock (List.replicate (UnitRecognitionChoice.index (winner G A s)) true)
        (List.replicate (winnerScore G A s) true) (List.replicate (winnerDegree G A s) true)
        [(winner G A s).isSome] [] [])
      (store G A (step G A s) clock (List.replicate (UnitRecognitionChoice.index (winner G A s)) true)
        (List.replicate (winnerScore G A s-1) true) (List.replicate (winnerDegree G A s) true)
        [(winner G A s).isSome] [] []) t ∧ t≤250*(n+1)^2+2 := by
  cases hw : winner G A s with
  | none =>
    have he : step G A s=s := by unfold step; change (match winner G A s with | none => s | some v => _) = s; rw [hw]
    simp only [hw,UnitRecognitionChoice.index,winnerScore,winnerDegree,hw,
      UnitRecognitionChoice.selectedScore,Option.map_none,Option.getD_none,List.replicate_zero,
      Nat.zero_sub,Option.isSome_none,he]
    refine ⟨3,?_,by have hn := Nat.one_le_pow 2 (n+1) (by omega); omega⟩
    exact branchPop_empty 6 skip advanceProgram advanceProgram g rfl (skip_executes g _)
  | some v =>
    have hidx : UnitRecognitionChoice.index (some v)=v.val := rfl
    have hs : winnerScore G A s=UnitRecognitionScore.score G s.selected v := by
      simp [winnerScore,hw,UnitRecognitionChoice.selectedScore]
    have hd : winnerDegree G A s=UnitRecognitionScore.score G A v := by
      simp [winnerDegree,hw,UnitRecognitionChoice.selectedScore]
    cases hc : UnitRecognitionScore.score G s.selected v with
    | zero =>
      have he : step G A s=s := by have hh := hw; unfold winner at hh; simp [step,hh,hc]
      simp only [hw,hidx,hs,hd,hc,Nat.zero_sub,List.replicate_zero,Option.isSome_some,he]
      refine ⟨3,?_,by have hn := Nat.one_le_pow 2 (n+1) (by omega); omega⟩
      exact branchPop_empty 6 skip advanceProgram advanceProgram g rfl (skip_executes g _)
    | succ c =>
      have he : step G A s=advance s v := by have hh := hw; unfold winner at hh; simp [step,hh,hc]
      simp only [hw,hidx,hs,hd,hc,Nat.add_sub_cancel,List.replicate_succ,Option.isSome_some,he]
      obtain ⟨t,ht,hb⟩ := advanceProgram_executes g G A s v clock (List.replicate c true)
        (List.replicate (UnitRecognitionScore.score G A v) true) [true]
      refine ⟨t+2,?_,by omega⟩
      apply branchPop_true 6 skip advanceProgram advanceProgram g rfl
      convert ht using 1
      funext i;fin_cases i <;> rfl

noncomputable def reset : OracleBlock 36 := seq (clear 5) (seq (clear 6)
  (seq (clear 7) (seq (clear 8) (push 8 false))))

theorem reset_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (s : Data n) (clock win score degree found : BitString) :
    reset.Executes g (store G A s clock win score degree found [] [])
      (store G A s clock [] [] [] [false] [] [])
      (win.length+score.length+degree.length+found.length+13) := by
  have h1 : (clear (5 : Fin 37)).Executes g (store G A s clock win score degree found [] [])
      (store G A s clock [] score degree found [] []) (win.length+1) := by
    convert clear_executes g (5 : Fin 37) _ using 1
    funext i;fin_cases i <;> rfl
  have h2 : (clear (6 : Fin 37)).Executes g (store G A s clock [] score degree found [] [])
      (store G A s clock [] [] degree found [] []) (score.length+1) := by
    convert clear_executes g (6 : Fin 37) _ using 1
    funext i;fin_cases i <;> rfl
  have h3 : (clear (7 : Fin 37)).Executes g (store G A s clock [] [] degree found [] [])
      (store G A s clock [] [] [] found [] []) (degree.length+1) := by
    convert clear_executes g (7 : Fin 37) _ using 1
    funext i;fin_cases i <;> rfl
  have h4 : (clear (8 : Fin 37)).Executes g (store G A s clock [] [] [] found [] [])
      (store G A s clock [] [] [] [] [] []) (found.length+1) := by
    convert clear_executes g (8 : Fin 37) _ using 1
    funext i;fin_cases i <;> rfl
  have h5 : (push (8 : Fin 37) false).Executes g (store G A s clock [] [] [] [] [] [])
      (store G A s clock [] [] [] [false] [] []) 1 := by
    convert push_executes g (8 : Fin 37) false _ using 1
    funext i;fin_cases i <;> rfl
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 h5))) using 1 <;> omega

noncomputable def body : OracleBlock 36 := seq choose (seq selectAction reset)

theorem body_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (s : Data n) (clock : BitString) :
    ∃t, body.Executes g (store G A s clock [] [] [] [false] [] [])
      (store G A (step G A s) clock [] [] [] [false] [] []) t ∧ t≤2000*(n+1)^4 := by
  obtain ⟨c1,h1,b1⟩ := choose_executes g G A s clock
  obtain ⟨c2,h2,b2⟩ := selectAction_executes g G A s clock
  have h3 := reset_executes g G A (step G A s) clock
    (List.replicate (UnitRecognitionChoice.index (winner G A s)) true)
    (List.replicate (winnerScore G A s-1) true) (List.replicate (winnerDegree G A s) true)
    [(winner G A s).isSome]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  have hi := UnitRecognitionChoice.index_le (winner G A s)
  have hs := UnitRecognitionChoice.selectedScore_le G s.selected (winner G A s)
  have hd := UnitRecognitionChoice.selectedScore_le G A (winner G A s)
  change winnerScore G A s≤n at hs
  change winnerDegree G A s≤n at hd
  simp only [List.length_replicate,List.length_cons,List.length_nil]
  have hss : winnerScore G A s-1≤n := by omega
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4)]

lemma reset_queryFree : reset.QueryFree := seq_queryFree _ _ (clear_queryFree _)
  (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _))))
lemma body_queryFree : body.QueryFree := seq_queryFree _ _ choose_queryFree
  (seq_queryFree _ _ (branchPop_queryFree _ _ _ _ skip_queryFree advanceProgram_queryFree
    advanceProgram_queryFree) reset_queryFree)

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
