import HiddenCircuits.GraphReduction.Runtime.UnaryCompare
import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision

/-! A fixed finite-stack comparison for the greedy recognizer: prefer a larger
selected-neighbor count, then a smaller alive-neighbor count. Equal candidates
retain the old winner. No arithmetic or comparison is a machine primitive. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionBetter
open Complexity Complexity.OracleBlock

def better (newScore newDegree oldScore oldDegree : ℕ) (found eligible : Bool) : Bool :=
  eligible && (!found || decide (oldScore<newScore) ||
    (decide (newScore=oldScore) && decide (newDegree<oldDegree)))

def state (ns nd os od : ℕ) (found eligible : Bool) (out less equal degree : BitString)
    (foundCopy eligibleCopy : BitString) : Store 14 :=
  ![List.replicate ns true,List.replicate nd true,List.replicate os true,List.replicate od true,
    [found],[eligible],out,less,equal,degree,[],[],[],foundCopy,eligibleCopy]

def scoreEmbedding : Fin 6 ↪ Fin 15 where
  toFun i := ![2,0,7,10,11,12] i
  inj' := by decide +kernel
def equalEmbedding : Fin 6 ↪ Fin 15 where
  toFun i := ![0,2,8,10,11,12] i
  inj' := by decide +kernel
def degreeEmbedding : Fin 6 ↪ Fin 15 where
  toFun i := ![1,3,9,10,11,12] i
  inj' := by decide +kernel

def decisionValue : List Bool → Bool
  | [found,eligible,less,equal,degree] => eligible && (!found || less || (equal && degree))
  | _ => false
noncomputable def decideWinner : OracleBlock 14 :=
  GraphVerifier.Runtime.decision 6 [13,14,7,8,9] decisionValue
noncomputable def program : OracleBlock 14 := seq (readOnlyLTOn scoreEmbedding)
  (seq (GraphVerifier.Runtime.readLengthOn equalEmbedding)
    (seq (readOnlyLTOn degreeEmbedding)
      (seq (copyOn 4 13 10 (by decide) (by decide) (by decide))
        (seq (copyOn 5 14 10 (by decide) (by decide) (by decide)) decideWinner))))

theorem program_executes (g : BitString → ℕ) (ns nd os od : ℕ) (found eligible : Bool) :
    ∃t, program.Executes g (state ns nd os od found eligible [] [] [] [] [] [])
      (state ns nd os od found eligible [better ns nd os od found eligible] [] [] [] [] []) t ∧
      t≤50*(ns+nd+os+od+1)+50 := by
  obtain ⟨c1,h1,b1⟩ := readOnlyLTOn_executes scoreEmbedding g
    (state ns nd os od found eligible [] [] [] [] [] []) os ns
    (by funext i;fin_cases i <;> rfl)
  have e1 : Function.update (state ns nd os od found eligible [] [] [] [] [] []) (scoreEmbedding 2)
      [decide (os<ns)] = state ns nd os od found eligible [] [decide (os<ns)] [] [] [] [] := by
    funext i;fin_cases i <;> rfl
  rw [e1] at h1
  obtain ⟨c2,h2,b2⟩ := GraphVerifier.Runtime.readLengthOn_executes equalEmbedding g
    (state ns nd os od found eligible [] [decide (os<ns)] [] [] [] [])
    (List.replicate ns true) (List.replicate os true)
    (by funext i;fin_cases i <;> rfl)
  simp only [List.length_replicate] at h2 b2
  have e2 : Function.update (state ns nd os od found eligible [] [decide (os<ns)] [] [] [] []) (equalEmbedding 2)
      [decide (ns=os)] = state ns nd os od found eligible [] [decide (os<ns)] [decide (ns=os)] [] [] [] := by
    funext i;fin_cases i <;> rfl
  rw [e2] at h2
  obtain ⟨c3,h3,b3⟩ := readOnlyLTOn_executes degreeEmbedding g
    (state ns nd os od found eligible [] [decide (os<ns)] [decide (ns=os)] [] [] []) nd od
    (by funext i;fin_cases i <;> rfl)
  have e3 : Function.update (state ns nd os od found eligible [] [decide (os<ns)] [decide (ns=os)] [] [] []) (degreeEmbedding 2)
      [decide (nd<od)] = state ns nd os od found eligible [] [decide (os<ns)] [decide (ns=os)] [decide (nd<od)] [] [] := by
    funext i;fin_cases i <;> rfl
  rw [e3] at h3
  have h4 : (copyOn (4 : Fin 15) 13 10 (by decide) (by decide) (by decide)).Executes g
      (state ns nd os od found eligible [] [decide (os<ns)] [decide (ns=os)] [decide (nd<od)] [] [])
      (state ns nd os od found eligible [] [decide (os<ns)] [decide (ns=os)] [decide (nd<od)] [found] []) 7 := by
    convert copyOn_executes g (4 : Fin 15) 13 10 (by decide) (by decide) (by decide)
      (state ns nd os od found eligible [] [decide (os<ns)] [decide (ns=os)] [decide (nd<od)] [] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  have h5 : (copyOn (5 : Fin 15) 14 10 (by decide) (by decide) (by decide)).Executes g
      (state ns nd os od found eligible [] [decide (os<ns)] [decide (ns=os)] [decide (nd<od)] [found] [])
      (state ns nd os od found eligible [] [decide (os<ns)] [decide (ns=os)] [decide (nd<od)] [found] [eligible]) 7 := by
    convert copyOn_executes g (5 : Fin 15) 14 10 (by decide) (by decide) (by decide)
      (state ns nd os od found eligible [] [decide (os<ns)] [decide (ns=os)] [decide (nd<od)] [found] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  let bits : Fin 15 → Bool := ![false,false,false,false,false,false,false,
    decide (os<ns),decide (ns=os),decide (nd<od),false,false,false,found,eligible]
  have h6 : decideWinner.Executes g
      (state ns nd os od found eligible [] [decide (os<ns)] [decide (ns=os)] [decide (nd<od)] [found] [eligible])
      (state ns nd os od found eligible [better ns nd os od found eligible] [] [] [] [] []) 14 := by
    have h := GraphVerifier.Runtime.decision_executes (6 : Fin 15) [13,14,7,8,9]
      (by decide) (by decide) decisionValue bits g
      (state ns nd os od found eligible [] [decide (os<ns)] [decide (ns=os)] [decide (nd<od)] [found] [eligible])
      (by intro i hi;fin_cases i <;> simp [state,bits] at *)
    convert h using 1
    funext i;fin_cases i <;> simp [state,bits,eraseStore,decisionValue,better]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6)))),?_⟩
  omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (readOnlyLTOn_queryFree _)
  (seq_queryFree _ _ (GraphVerifier.Runtime.readLengthOn_queryFree _)
    (seq_queryFree _ _ (readOnlyLTOn_queryFree _) (seq_queryFree _ _
      (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
        (GraphVerifier.Runtime.decision_queryFree _ _ _)))))

noncomputable def on {k : ℕ} (φ : Fin 15 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 15 ↪ Fin (k+1)) (g : BitString → ℕ)
    (ns nd os od : ℕ) (found eligible : Bool) (s : Store k)
    (hs : s ∘ φ=state ns nd os od found eligible [] [] [] [] [] []) :
    ∃t, (on φ).Executes g s (Function.update s (φ 6) [better ns nd os od found eligible]) t ∧
      t≤50*(ns+nd+os+od+1)+50 := by
  obtain ⟨t,ht,hb⟩ := program_executes g ns nd os od found eligible
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update s (φ 6) [better ns nd os od found eligible]) ∘ φ =
        Function.update (s ∘ φ) 6 [better ns nd os od found eligible] := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi
    exact Function.update_of_ne (hi 6).symm _ _

lemma on_queryFree {k : ℕ} (φ : Fin 15 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionBetter
