import HiddenCircuits.Complexity.OracleElimination.Stores

/-! The final halt explicitly erases all caller work stacks. Solver and scratch
banks are already empty at every return to source control. -/
namespace HiddenCircuits.Complexity.OracleElimination
open Turing.TM2
variable (M : OracleMachine) {f : BitString → BitString}
variable (N : Turing.TM2ComputableInPolyTime id id f)

def cleaned (S : SourceStore M) (j : ℕ) : SourceStore M :=
  fun i => if j ≤ i.val ∧ i ≠ M.output then [] else S i

def halted (S : SourceStore M) : Cfg M N :=
  ⟨none,initialRegister N,fullStore M N S [] (fun _ => [])⟩

 theorem clean_one_eval (j : Fin (M.stackCount+1)) (hj : j.val < M.stackCount)
    (ho : (⟨j.val,hj⟩ : Fin M.stackCount) ≠ M.output)
    (S : SourceStore M) (xs : BitString) :
    Eval (machine M N).step
      (atLabel M N (.clean j) (Function.update S ⟨j.val,hj⟩ xs) [] (fun _ => []))
      (atLabel M N (.clean ⟨j.val+1,by omega⟩) (Function.update S ⟨j.val,hj⟩ []) [] (fun _ => []))
      (xs.length+1) := by
  induction xs with
  | nil =>
    apply Eval.single
    rw [step_atLabel]
    simp [code,hj,ho,stepAux]
  | cons b bs ih =>
    have hs : (machine M N).step
        (atLabel M N (.clean j) (Function.update S ⟨j.val,hj⟩ (b::bs)) [] (fun _ => [])) =
        some (atLabel M N (.clean j) (Function.update S ⟨j.val,hj⟩ bs) [] (fun _ => [])) := by
      rw [step_atLabel]
      simp [code,hj,ho,stepAux]
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using (Eval.single hs).trans ih

 theorem cleaned_succ_keep (S : SourceStore M) (j : ℕ) (hj : j < M.stackCount)
    (ho : (⟨j,hj⟩ : Fin M.stackCount) = M.output) : cleaned M S (j+1) = cleaned M S j := by
  funext i
  by_cases hi : i.val = j
  · have he : i = M.output := (Fin.ext hi).trans ho
    simp [cleaned,he]
  · have heq : j+1 ≤ i.val ↔ j ≤ i.val := by omega
    simp [cleaned,heq]

 theorem cleaned_succ_clear (S : SourceStore M) (j : ℕ) (hj : j < M.stackCount)
    (ho : (⟨j,hj⟩ : Fin M.stackCount) ≠ M.output) :
    cleaned M (Function.update S ⟨j,hj⟩ []) (j+1) = cleaned M S j := by
  funext i
  by_cases hi : i.val = j
  · have he : i = (⟨j,hj⟩ : Fin M.stackCount) := Fin.ext hi
    subst i
    simp [cleaned,ho]
  · have he : i ≠ (⟨j,hj⟩ : Fin M.stackCount) := fun h => hi (congrArg Fin.val h)
    have heq : j+1 ≤ i.val ↔ j ≤ i.val := by omega
    simp [cleaned,heq,Function.update_of_ne he]

 theorem cleaned_end (S : SourceStore M) : cleaned M S M.stackCount = S := by
  funext i;simp [cleaned,show ¬M.stackCount ≤ i.val by omega]

 theorem cleanup_eval (j : Fin (M.stackCount+1)) (S : SourceStore M) (n : ℕ)
    (hS : ∀ i,(S i).length ≤ n) :
    Eval (machine M N).step (atLabel M N (.clean j) S [] (fun _ => []))
      (halted M N (cleaned M S j.val)) ((M.stackCount-j.val)*(n+1)+1) := by
  generalize he : M.stackCount-j.val = r
  induction r using Nat.strong_induction_on generalizing j S with
  | h r ih =>
    by_cases hj : j.val < M.stackCount
    · let j' : Fin (M.stackCount+1) := ⟨j.val+1,by omega⟩
      have hr : M.stackCount-j'.val < r := by dsimp [j'];omega
      by_cases ho : (⟨j.val,hj⟩ : Fin M.stackCount) = M.output
      · have hs : (machine M N).step (atLabel M N (.clean j) S [] (fun _ => [])) =
          some (atLabel M N (.clean j') S [] (fun _ => [])) := by
          rw [step_atLabel]
          simp [code,hj,ho,j',stepAux,atLabel,initialRegister]
        have ht := ih _ hr j' S hS rfl
        rw [show j'.val = j.val+1 from rfl,cleaned_succ_keep M S j.val hj ho] at ht
        apply ((Eval.single hs).trans ht).mono
        rw [show r = (M.stackCount-(j.val+1))+1 by omega]
        simp only [Nat.add_mul,Nat.one_mul]
        omega
      · let S' := Function.update S ⟨j.val,hj⟩ []
        have hS' : ∀ i,(S' i).length ≤ n := by
          intro i
          simp only [S',Function.update_apply]
          split_ifs <;> simp_all
        have hs := clean_one_eval M N j hj ho S (S ⟨j.val,hj⟩)
        have ht := ih _ hr j' S' hS' rfl
        rw [show j'.val = j.val+1 from rfl,cleaned_succ_clear M S j.val hj ho] at ht
        have hh := (show Eval (machine M N).step
          (atLabel M N (.clean j) S [] (fun _ => []))
          (atLabel M N (.clean j') S' [] (fun _ => []))
          ((S ⟨j.val,hj⟩).length+1) by simpa [j',S'] using hs).trans ht
        apply hh.mono
        have hb := hS ⟨j.val,hj⟩
        rw [show r = (M.stackCount-(j.val+1))+1 by omega]
        simp only [Nat.add_mul,Nat.one_mul]
        omega
    · have heq : j.val = M.stackCount := by omega
      subst r
      rw [heq,cleaned_end]
      simp only [Nat.sub_self,Nat.zero_mul,Nat.zero_add]
      apply Eval.single
      rw [step_atLabel]
      simp [code,hj,stepAux,atLabel,halted,initialRegister]

 theorem cleaned_zero (S : SourceStore M) :
    cleaned M S 0 = Function.update (fun _ => []) M.output (S M.output) := by
  funext i
  by_cases h : i = M.output
  · subst i;simp [cleaned]
  · simp [cleaned,h,Function.update_of_ne h]

 theorem halted_output (S : SourceStore M) :
    halted M N (cleaned M S 0) = Turing.haltList (machine M N) (S M.output) := by
  rw [cleaned_zero]
  apply OracleMachine.tm2Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl a =>
      cases a with
      | inl i => simp [Turing.haltList,machine,caller,halted,fullStore,publicStore,Function.update_apply]
      | inr u => simp [Turing.haltList,machine,caller,halted,fullStore,publicStore]
    | inr k => simp [Turing.haltList,machine,caller,halted,fullStore,publicStore]

end HiddenCircuits.Complexity.OracleElimination
