import HiddenCircuits.Complexity.OracleLibrary
import HiddenCircuits.Complexity.OracleBlockNoQuery

/-! Actual finite-program cleanup and the final bridge from polynomially bounded
block executions to standard mathlib TM2 polynomial time. Dirty work tapes are
cleared by real pops, charged using the proved execution storage bound. -/
namespace HiddenCircuits.Complexity.OracleBlock
variable {k : ℕ}

noncomputable def clearList : List (Fin (k+1)) → OracleBlock k
  | [] => skip
  | i::is => seq (clear i) (clearList is)

def eraseStore (is : List (Fin (k+1))) (s : Store k) : Store k :=
  fun i => if i ∈ is then [] else s i

lemma eraseStore_cons (i : Fin (k+1)) (is : List (Fin (k+1))) (s : Store k) :
    eraseStore (i::is) s = eraseStore is (Function.update s i []) := by
  funext j
  by_cases hj : j = i <;> by_cases hm : j ∈ is <;>
    simp [eraseStore,hj,hm,Function.update_apply]

theorem clearList_executes (g : BitString → ℕ) (is : List (Fin (k+1))) (s : Store k)
    (n : ℕ) (hs : ∀ j, (s j).length ≤ n) :
    ∃ cost, (clearList is).Executes g s (eraseStore is s) cost ∧ cost ≤ is.length*(n+3)+1 := by
  induction is generalizing s with
  | nil => exact ⟨1,by simpa [clearList,eraseStore] using skip_executes g s,by simp⟩
  | cons i is ih =>
    have hnew : ∀ j, (Function.update s i [] j).length ≤ n := by
      intro j
      by_cases he : j=i
      · subst j;simp
      · simpa [he] using hs j
    obtain ⟨cost,hcost,hbound⟩ := ih _ hnew
    refine ⟨(s i).length+1+cost+2,?_,?_⟩
    · rw [clearList,eraseStore_cons]
      exact seq_executes (clear i) (clearList is) g (clear_executes g i s) hcost
    · have := hs i
      simp only [List.length_cons,Nat.add_mul]
      omega

lemma clearList_queryFree (is : List (Fin (k+1))) : (clearList is).QueryFree := by
  induction is with
  | nil => exact skip_queryFree
  | cons i is ih => exact seq_queryFree (clear i) (clearList is) (clear_queryFree i) ih

def nonoutputStacks (out : Fin (k+1)) : List (Fin (k+1)) :=
  (List.finRange (k+1)).filter (fun i => i ≠ out)

@[simp] theorem mem_nonoutputStacks (out i : Fin (k+1)) : i ∈ nonoutputStacks out ↔ i ≠ out := by
  simp [nonoutputStacks]

lemma nonoutputStacks_length (out : Fin (k+1)) : (nonoutputStacks out).length ≤ k+1 := by
  exact (List.length_filter_le _ _).trans (by simp)

noncomputable def cleanup (out : Fin (k+1)) : OracleBlock k := clearList (nonoutputStacks out)

/-- Automatic cleanup leaves exactly the selected output stack, using at most a
machine-constant multiple of the actual proved stack-length bound. -/
theorem cleanup_executes (g : BitString → ℕ) (out : Fin (k+1)) (s : Store k)
    (n : ℕ) (hs : ∀ j, (s j).length ≤ n) :
    ∃ cost, (cleanup out).Executes g s (Function.update (fun _ => []) out (s out)) cost ∧
      cost ≤ (k+1)*(n+3)+1 := by
  obtain ⟨cost,hc,hb⟩ := clearList_executes g (nonoutputStacks out) s n hs
  refine ⟨cost,?_,hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (nonoutputStacks_length out)) 1)⟩
  have he : eraseStore (nonoutputStacks out) s = Function.update (fun _ => []) out (s out) := by
    funext i
    by_cases hi : i=out <;> simp [eraseStore,hi,Function.update_apply]
  rwa [he] at hc

lemma cleanup_queryFree (out : Fin (k+1)) : (cleanup out).QueryFree := clearList_queryFree _

/-- No cleanup invariant is required of the given block: an actual compiled
cleanup routine supplies it, with polynomial overhead derived from storage. -/
noncomputable def computableOfBlock {f : BitString → BitString} (B : OracleBlock k)
    (hq : B.QueryFree) (p : Polynomial ℕ)
    (h : ∀ x, ∃ s : Store k, ∃ cost, B.Executes (fun _ => 0) (Function.update (fun _ => []) 0 x) s cost ∧
      s 0 = f x ∧ cost ≤ p.eval x.length) : Turing.TM2ComputableInPolyTime id id f := by
  let C := seq B (cleanup 0)
  apply OracleMachine.computableOfBinary C.machine (seq_queryFree B (cleanup 0) hq (cleanup_queryFree 0))
    (p+Polynomial.C (k+1)*(Polynomial.X+p+3)+3)
  intro x
  obtain ⟨s,cost,hb,ho,hcost⟩ := h x
  have hs : ∀ j, (s j).length ≤ x.length+cost :=
    hb.stack_bound (B.machine.init_stack_bound x)
  obtain ⟨t,hc,ht⟩ := cleanup_executes (fun _ => 0) (0 : Fin (k+1)) s _ hs
  refine ⟨C.config C.exit (Function.update (fun _ => []) 0 (s 0)),cost+t+2,?_,?_,?_,?_⟩
  · apply (OracleMachine.runs_iff_steps_halt C.machine).mpr
    exact ⟨seq_executes B (cleanup 0) (fun _ => 0) hb hc,by simp [OracleMachine.step,machine,config,C.exit_halt]⟩
  · simpa [C,config,machine] using ho
  · intro i hi
    change i ≠ (0 : Fin (k+1)) at hi
    change Function.update (fun _ : Fin (k+1) => ([] : BitString)) 0 (s 0) i = []
    simp [hi]
  · simp only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
    nlinarith

theorem polyTime_of_block {f : BitString → BitString} (B : OracleBlock k)
    (hq : B.QueryFree) (p : Polynomial ℕ)
    (h : ∀ x, ∃ s : Store k, ∃ cost, B.Executes (fun _ => 0) (Function.update (fun _ => []) 0 x) s cost ∧
      s 0 = f x ∧ cost ≤ p.eval x.length) : PolyTime f := ⟨computableOfBlock B hq p h⟩

/-- The same real block-to-TM2 bridge with Boolean output encoding. -/
noncomputable def verifierOfBlock (v : BitString → Bool) (B : OracleBlock k)
    (hq : B.QueryFree) (p : Polynomial ℕ)
    (h : ∀ x, ∃ s : Store k, ∃ cost, B.Executes (fun _ => 0) (Function.update (fun _ => []) 0 x) s cost ∧
      s 0 = Computability.encodeBool (v x) ∧ cost ≤ p.eval x.length) :
    Turing.TM2ComputableInPolyTime id Computability.encodeBool v :=
  let M := computableOfBlock B hq p h
  { toTM2ComputableAux := M.toTM2ComputableAux
    time := M.time
    outputsFun := M.outputsFun }

theorem polyVerifier_of_block (v : BitString → Bool) (B : OracleBlock k)
    (hq : B.QueryFree) (p : Polynomial ℕ)
    (h : ∀ x, ∃ s : Store k, ∃ cost, B.Executes (fun _ => 0) (Function.update (fun _ => []) 0 x) s cost ∧
      s 0 = Computability.encodeBool (v x) ∧ cost ≤ p.eval x.length) :
    PolyVerifier v := ⟨verifierOfBlock v B hq p h⟩

end HiddenCircuits.Complexity.OracleBlock
