import HiddenCircuits.Approximation.SelfReduction.Runtime.GroupTallyBody
import HiddenCircuits.Approximation.SelfReduction.Runtime.MapLoop
import HiddenCircuits.Approximation.SelfReduction.Runtime.UnaryValues

/-! Compute the full confidence-batch count vector with a real finite loop. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

noncomputable def groupTallyLoop : OracleBlock 13 := whilePop 10 skip groupBody
noncomputable def groupCounts : OracleBlock 13 := seq groupTallyLoop (reverseOn 11 10 (by decide))

def groupWords (groups : List (List BitString)) : BitString := encodeBitList (groups.map encodeBitList)

 theorem groupBody_uniform_bound (g : BitString → ℕ) (target rest out : BitString) (xs : List BitString)
    (M B : ℕ) (hm : xs.length ≤ M) (hxs : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t, groupBody.Executes g (groupStore target [] (pairBits (encodeBitList xs) rest) out 0 [])
      (groupStore target [] rest
        ((true::pairBits (List.replicate (wordOccurrences target xs) true) []).reverse++out) 0 []) t ∧
      t+2 ≤ 100*(M+1)*(B+target.length+1) := by
  obtain ⟨t,ht,hb⟩ := groupBody_executes g target rest out xs B hxs
  have hlen := encodedWords_length_bound xs B hxs
  have hm1 : xs.length*(60*(B+target.length+1)) ≤ M*(60*(B+target.length+1)) := by gcongr
  have hm2 : 2*xs.length*(B+1) ≤ 2*M*(B+1) := by gcongr
  exact ⟨t,ht,by nlinarith⟩

 theorem groupTallyLoop_execution (g : BitString → ℕ) (target : BitString)
    (groups : List (List BitString)) (M B : ℕ)
    (hM : ∀ xs ∈ groups, xs.length ≤ M) (hB : ∀ xs ∈ groups, ∀ x ∈ xs, x.length ≤ B) (out : BitString) :
    ∃ t, WhileExecution (10 : Fin 14) skip groupBody g
      (groupStore target [] (groupWords groups) out 0 [])
      (groupStore target [] [] ((unaryValues (groups.map (wordOccurrences target))).reverse++out) 0 []) t ∧
      t ≤ 1+groups.length*(100*(M+1)*(B+target.length+1)) := by
  induction groups generalizing out with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa [groupWords,unaryValues,encodeBitList] using
      (WhileExecution.empty (groupStore target [] [] out 0 []) (by rfl))
  | cons xs groups ih =>
    obtain ⟨tb,hb,hbt⟩ := groupBody_uniform_bound g target (groupWords groups) out xs M B
      (hM xs (by simp)) (hB xs (by simp))
    obtain ⟨tt,ht,htt⟩ := ih (fun ys hy => hM ys (by simp [hy])) (fun ys hy => hB ys (by simp [hy]))
      ((true::pairBits (List.replicate (wordOccurrences target xs) true) []).reverse++out)
    have hpop : Function.update (groupStore target [] (groupWords (xs::groups)) out 0 [])
        (10 : Fin 14) (pairBits (encodeBitList xs) (groupWords groups)) =
        groupStore target [] (pairBits (encodeBitList xs) (groupWords groups)) out 0 [] := by
      funext i; fin_cases i <;> rfl
    have hw := WhileExecution.one
      (s := groupStore target [] (groupWords (xs::groups)) out 0 [])
      (rest := pairBits (encodeBitList xs) (groupWords groups)) (by rfl) (by rw [hpop]; exact hb) ht
    refine ⟨2+tb+tt,?_,?_⟩
    · convert hw using 1
      · simp only [List.map_cons,unaryValues,encodeBitList_cons_segment,List.reverse_append,List.append_assoc]
      · omega
    · simp only [List.length_cons]; nlinarith

 theorem groupCounts_executes (g : BitString → ℕ) (target : BitString)
    (groups : List (List BitString)) (M B : ℕ)
    (hM : ∀ xs ∈ groups, xs.length ≤ M) (hB : ∀ xs ∈ groups, ∀ x ∈ xs, x.length ≤ B) :
    ∃ t, groupCounts.Executes g (groupStore target [] (groupWords groups) [] 0 [])
      (groupStore target [] (unaryValues (groups.map (wordOccurrences target))) [] 0 []) t ∧
      t ≤ 1+groups.length*(110*(M+1)*(B+target.length+1))+3 := by
  obtain ⟨tl,hl,hbl⟩ := groupTallyLoop_execution g target groups M B hM hB []
  have hloop : groupTallyLoop.Executes g (groupStore target [] (groupWords groups) [] 0 [])
      (groupStore target [] [] (unaryValues (groups.map (wordOccurrences target))).reverse 0 []) tl := by
    simpa using whilePop_executes _ _ _ _ hl
  have hr : (reverseOn (11 : Fin 14) 10 (by decide)).Executes g
      (groupStore target [] [] (unaryValues (groups.map (wordOccurrences target))).reverse 0 [])
      (groupStore target [] (unaryValues (groups.map (wordOccurrences target))) [] 0 [])
      (2*(unaryValues (groups.map (wordOccurrences target))).length+1) := by
    convert reverseOn_executes g (11 : Fin 14) 10 (by decide)
      (groupStore target [] [] (unaryValues (groups.map (wordOccurrences target))).reverse 0 []) using 1
    · funext i; fin_cases i <;> simp [groupStore]
    · simp [groupStore]
  have hlen := unaryValues_length_bound (groups.map (wordOccurrences target)) M (by
    intro c hc
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hc
    exact List.countP_le_length.trans (hM xs hxs))
  simp only [List.length_map] at hlen
  refine ⟨_,seq_executes _ _ g hloop hr,?_⟩
  nlinarith

end HiddenCircuits.Approximation.SelfReduction.Runtime
