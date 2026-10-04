import HiddenCircuits.Complexity.LooseWordList

/-! The existing finite indexed reader terminates on all raw byte strings. -/
namespace HiddenCircuits.Complexity.CNFCloneEmitter.ClauseLookup
open OracleBlock GraphVerifier GraphVerifier.Runtime

theorem parseOne_raw (g : BitString → ℕ) (index xs : BitString) :
    parseOne.Executes g (store xs index [] [] [])
      (store (parse xs).right index (parse xs).left [] [(parse xs).ok])
      (parseCost xs+2*(parse xs).left.length+1) := by
  apply unpairOn_executes
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim

theorem skipBody_raw (g : BitString → ℕ) (index xs : BitString) :
    ∃c,skipBody.Executes g (store xs index [] [] []) (store (parse xs).right index [] [] []) c ∧c≤6*xs.length+20 := by
  have h1 : (clear (2:Fin 5)).Executes g (store (parse xs).right index (parse xs).left [] [(parse xs).ok])
      (store (parse xs).right index [] [] [(parse xs).ok]) ((parse xs).left.length+1) := by
    convert clear_executes g (2:Fin 5) (store (parse xs).right index (parse xs).left [] [(parse xs).ok]) using 1
    funext i;fin_cases i <;> rfl
  have h2 : (clear (4:Fin 5)).Executes g (store (parse xs).right index [] [] [(parse xs).ok])
      (store (parse xs).right index [] [] []) 2 := by
    convert clear_executes g (4:Fin 5) (store (parse xs).right index [] [] [(parse xs).ok]) using 1
    funext i;fin_cases i <;> rfl
  refine ⟨_,seq_executes _ _ g (parseOne_raw g index xs) (seq_executes _ _ g h1 h2),?_⟩
  have ht:=unpair_cost_bound xs
  have hl:=(parse_lengths xs).1
  omega

theorem skipOne_raw (g : BitString → ℕ) (index xs : BitString) :
    ∃c,skipOne.Executes g (store xs index [] [] []) (store (LooseWordList.tail xs) index [] [] []) c ∧
      c≤6*xs.length+20 := by
  cases xs with
  | nil => exact ⟨3,skipOne_nil g index,by simp⟩
  | cons b bs =>
    obtain ⟨c,hc,hb⟩:=skipBody_raw g index bs
    cases b
    · exact ⟨c+2,branchPop_false 0 _ _ _ g rfl (by rw [pop_data];exact hc),by simp;omega⟩
    · exact ⟨c+2,branchPop_true 0 _ _ _ g rfl (by rw [pop_data];exact hc),by simp;omega⟩

theorem skipLoop_raw (g : BitString → ℕ) (xs : BitString) (j : ℕ) :
    ∃c,WhileExecution (1:Fin 5) skipOne skipOne g (store xs (List.replicate j true) [] [] [])
      (store (LooseWordList.drop j xs) [] [] [] []) c ∧c≤j*(6*xs.length+22)+1 := by
  induction j generalizing xs with
  | zero => exact ⟨1,WhileExecution.empty _ rfl,by simp⟩
  | succ j ih =>
    obtain ⟨a,ha,hba⟩:=skipOne_raw g (List.replicate j true) xs
    obtain ⟨b,hb,hbb⟩:=ih (LooseWordList.tail xs)
    have h : WhileExecution (1:Fin 5) skipOne skipOne g (store xs (List.replicate (j+1) true) [] [] [])
        (store (LooseWordList.drop (j+1) xs) [] [] [] []) (1+a+1+b) := by
      apply WhileExecution.one rfl
      · simpa only [List.replicate_succ,pop_index] using ha
      · exact hb
    refine ⟨1+a+1+b,h,?_⟩
    have hl:=LooseWordList.tail_length xs
    have hm:=Nat.mul_le_mul_left j (show 6*(LooseWordList.tail xs).length+22≤6*xs.length+22 by omega)
    nlinarith

theorem takeBody_raw (g : BitString → ℕ) (xs : BitString) :
    ∃c,takeBody.Executes g (store xs [] [] [] []) (store [] [] (parse xs).left [] []) c ∧c≤6*xs.length+20 := by
  have h1 : (clear (4:Fin 5)).Executes g (store (parse xs).right [] (parse xs).left [] [(parse xs).ok])
      (store (parse xs).right [] (parse xs).left [] []) 2 := by
    convert clear_executes g (4:Fin 5) (store (parse xs).right [] (parse xs).left [] [(parse xs).ok]) using 1
    funext i;fin_cases i <;> rfl
  have h2 : (clear (0:Fin 5)).Executes g (store (parse xs).right [] (parse xs).left [] [])
      (store [] [] (parse xs).left [] []) ((parse xs).right.length+1) := by
    convert clear_executes g (0:Fin 5) (store (parse xs).right [] (parse xs).left [] []) using 1
    funext i;fin_cases i <;> rfl
  refine ⟨_,seq_executes _ _ g (parseOne_raw g [] xs) (seq_executes _ _ g h1 h2),?_⟩
  have ht:=unpair_cost_bound xs
  have hl:=(parse_lengths xs).2
  omega

theorem takeOne_raw (g : BitString → ℕ) (xs : BitString) :
    ∃c,takeOne.Executes g (store xs [] [] [] []) (store [] [] (LooseWordList.head xs) [] []) c ∧c≤6*xs.length+20 := by
  cases xs with
  | nil => exact ⟨3,branchPop_empty 0 _ _ _ g rfl (skip_executes g _),by simp⟩
  | cons b bs =>
    obtain ⟨c,hc,hb⟩:=takeBody_raw g bs
    cases b
    · exact ⟨c+2,branchPop_false 0 _ _ _ g rfl (by rw [pop_data];exact hc),by simp;omega⟩
    · exact ⟨c+2,branchPop_true 0 _ _ _ g rfl (by rw [pop_data];exact hc),by simp;omega⟩

theorem program_raw (g : BitString → ℕ) (xs : BitString) (j : ℕ) :
    ∃c,program.Executes g (store xs (List.replicate j true) [] [] [])
      (store [] [] ((LooseWordList.words xs)[j]?.getD []) [] []) c ∧c≤(j+1)*(6*xs.length+30)+4 := by
  obtain ⟨a,ha,hba⟩:=skipLoop_raw g xs j
  obtain ⟨b,hb,hbb⟩:=takeOne_raw g (LooseWordList.drop j xs)
  have he : LooseWordList.head (LooseWordList.drop j xs)=(LooseWordList.words xs)[j]?.getD [] := by
    rw [←LooseWordList.words_head,LooseWordList.words_drop,List.head?_drop]
  rw [he] at hb
  refine ⟨_,seq_executes _ _ g (whilePop_executes _ _ _ g ha) hb,?_⟩
  have hl:=LooseWordList.drop_length j xs
  nlinarith
end HiddenCircuits.Complexity.CNFCloneEmitter.ClauseLookup
