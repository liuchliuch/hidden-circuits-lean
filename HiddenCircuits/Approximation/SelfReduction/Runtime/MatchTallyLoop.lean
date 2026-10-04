import HiddenCircuits.Approximation.SelfReduction.Runtime.MatchTallyBody

/-! Execution and bounds for the physical occurrence tally. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def wordOccurrences (target : BitString) (xs : List BitString) : ℕ :=
  xs.countP (fun word => decide (target=word))

noncomputable def occurrenceTally : OracleBlock 9 := whilePop 1 skip matchBody

 theorem occurrenceTally_execution (g : BitString → ℕ) (target : BitString) (xs : List BitString)
    (count B : ℕ) (hxs : ∀ word ∈ xs, word.length ≤ B) :
    ∃ t, WhileExecution (1 : Fin 10) skip matchBody g
      (matchStore target (encodeBitList xs) count [] [] [])
      (matchStore target [] (count+wordOccurrences target xs) [] [] []) t ∧
      t ≤ 1+xs.length*(60*(B+target.length+1)) := by
  induction xs generalizing count with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa [wordOccurrences,encodeBitList] using
      (WhileExecution.empty (matchStore target [] count [] [] []) (by rfl))
  | cons word xs ih =>
    obtain ⟨tb,hb,hbt⟩ := matchBody_executes g target word (encodeBitList xs) count
    obtain ⟨tt,ht,htt⟩ := ih (count+if target=word then 1 else 0)
      (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    have hpop : Function.update (matchStore target (encodeBitList (word::xs)) count [] [] [])
        (1 : Fin 10) (pairBits word (encodeBitList xs)) =
        matchStore target (pairBits word (encodeBitList xs)) count [] [] [] := by
      funext i; fin_cases i <;> rfl
    have hw := WhileExecution.one
      (s := matchStore target (encodeBitList (word::xs)) count [] [] [])
      (rest := pairBits word (encodeBitList xs)) (by rfl) (by rw [hpop]; exact hb) ht
    refine ⟨2+tb+tt,?_,?_⟩
    · convert hw using 1
      · congr 1
        by_cases hh : target=word <;> simp [wordOccurrences,List.countP_cons,hh,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      · omega
    · have hwlen := hxs word (List.mem_cons_self)
      simp only [List.length_cons]
      nlinarith
 theorem occurrenceTally_executes (g : BitString → ℕ) (target : BitString) (xs : List BitString)
    (count B : ℕ) (hxs : ∀ word ∈ xs, word.length ≤ B) :
    ∃ t, occurrenceTally.Executes g (matchStore target (encodeBitList xs) count [] [] [])
      (matchStore target [] (count+wordOccurrences target xs) [] [] []) t ∧
      t ≤ 1+xs.length*(60*(B+target.length+1)) := by
  obtain ⟨t,ht,hb⟩ := occurrenceTally_execution g target xs count B hxs
  exact ⟨t,whilePop_executes _ _ _ _ ht,hb⟩

 theorem wordOccurrences_ofFn (n : ℕ) (q : Fin n → BitString) (target : BitString) :
    wordOccurrences target (List.ofFn q) =
      (Finset.univ.filter (fun i => target=q i)).card := by
  have hs (xs : List BitString) : xs.countP (fun word => decide (target=word)) =
      (xs.map (fun word => if target=word then 1 else 0)).sum := by
    induction xs with
    | nil => rfl
    | cons word xs ih =>
      simp only [List.countP_cons, List.map_cons, List.sum_cons, ih]
      by_cases h : target=word <;> simp [h] <;> omega
  unfold wordOccurrences
  rw [hs, List.map_ofFn, List.sum_ofFn, Finset.card_filter]
  rfl

/-- The machine's exact unary count is the finite empirical event count used
by the statistical proof. Failure words remain different from success words. -/
theorem occurrenceTally_ofFn (g : BitString → ℕ) (n B : ℕ) (q : Fin n → BitString)
    (hq : ∀ i, (q i).length ≤ B) (target : BitString) :
    ∃ t, occurrenceTally.Executes g (matchStore target (encodeBitList (List.ofFn q)) 0 [] [] [])
      (matchStore target [] ((Finset.univ.filter (fun i => target=q i)).card) [] [] []) t ∧
      t ≤ 1+n*(60*(B+target.length+1)) := by
  obtain ⟨t,ht,hb⟩ := occurrenceTally_executes g target (List.ofFn q) 0 B
    (by intro word hw; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw; exact hq i)
  rw [wordOccurrences_ofFn] at ht
  exact ⟨t,by simpa only [zero_add] using ht,by simpa only [List.length_ofFn] using hb⟩

end HiddenCircuits.Approximation.SelfReduction.Runtime
