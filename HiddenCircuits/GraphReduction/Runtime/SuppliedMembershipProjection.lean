import HiddenCircuits.Complexity.EvalValidation.Field
import HiddenCircuits.Complexity.OracleMove
import HiddenCircuits.Complexity.GraphVerifier.MatchingPullback

/-! A real linear-time first-field projector for supplied-representation packets.
Only the leading list marker and first pair terminator are checked. The remainder
is discarded without validating a list, coordinates, or a graph representation.
This is deliberately a projection extension, not a representation recognizer. -/
namespace HiddenCircuits.GraphReduction.Runtime.SuppliedMembership
open Complexity OracleBlock Polynomial GraphVerifier GraphVerifier.Runtime
open Complexity.EvalValidation

/-- The first field if its own marker and terminator are valid, and the empty
word otherwise. No condition is imposed on any trailing representation bytes. -/
def graphField (xs : BitString) : BitString :=
  if Field.valid xs then (Field.item xs).left else []

/-- Arbitrary trailing bytes are deliberately ignored. -/
@[simp] theorem graphField_frame (x rest : BitString) :
    graphField (true::pairBits x rest)=x := by
  simp [graphField,Field.valid,Field.item,Field.marker]

@[simp] theorem graphField_cons (x : BitString) (xs : List BitString) :
    graphField (encodeBitList (x::xs))=x := by
  simp [graphField,Field.valid,Field.item,Field.marker,encodeBitList]

lemma graphField_length (xs : BitString) : (graphField xs).length≤xs.length := by
  unfold graphField
  split_ifs
  · exact (Field.lengths xs).1
  · simp

noncomputable def selectField : OracleBlock 5 := branchPop 2 (clear 1) (clear 1) skip
noncomputable def program : OracleBlock 5 :=
  seq Field.program (seq selectField (seq (cleanup 1) (moveOn 1 0 3 (by decide) (by decide) (by decide))))
noncomputable def time : Polynomial ℕ := 20*X+70
noncomputable def size : Polynomial ℕ := X

lemma selectField_executes (g : BitString→ℕ) (right left : BitString) (ok : Bool) :
    ∃c,selectField.Executes g (Field.store right left [ok] [] [] [])
      (Field.store right (if ok then left else []) [] [] [] []) c ∧c≤left.length+3 := by
  have hp : Function.update (Field.store right left [ok] [] [] []) (2:Fin 6) []=
      Field.store right left [] [] [] [] := by funext i;fin_cases i <;> rfl
  cases ok
  · have hc : (clear (1:Fin 6)).Executes g (Field.store right left [] [] [] [])
        (Field.store right [] [] [] [] []) (left.length+1) := by
      convert clear_executes g (1:Fin 6) (Field.store right left [] [] [] []) using 1
      funext i;fin_cases i <;> rfl
    exact ⟨_,branchPop_false 2 _ _ _ g rfl (by rw [hp];exact hc),by omega⟩
  · exact ⟨3,branchPop_true 2 _ _ _ g rfl (by rw [hp];exact skip_executes g _),by omega⟩

/-- Every work stack is physically cleared. This execution holds for all bytes,
not only canonical packets, and performs no oracle calls. -/
theorem program_executes_clean (g : BitString→ℕ) (xs : BitString) :
    ∃c,program.Executes g (Function.update (fun _=>[]) 0 xs)
      (Function.update (fun _=>[]) 0 (graphField xs)) c ∧c≤time.eval xs.length := by
  obtain ⟨a,ha,hba⟩:=Field.program_executes g xs
  obtain ⟨b,hb,hbb⟩:=selectField_executes g (Field.item xs).right (Field.item xs).left (Field.valid xs)
  change selectField.Executes g _ (Field.store (Field.item xs).right (graphField xs) [] [] [] []) b at hb
  have hlen:=Field.lengths xs
  have hfield:=graphField_length xs
  obtain ⟨c,hc,hbc⟩:=cleanup_executes g (1:Fin 6)
    (Field.store (Field.item xs).right (graphField xs) [] [] [] []) xs.length (by
      intro i;fin_cases i
      · exact hlen.2
      · exact hfield
      all_goals exact Nat.zero_le _)
  change (cleanup (1:Fin 6)).Executes g _ (Function.update (fun _=>[]) 1 (graphField xs)) c at hc
  have hm : (moveOn (1:Fin 6) 0 3 (by decide) (by decide) (by decide)).Executes g
      (Function.update (fun _=>[]) 1 (graphField xs))
      (Function.update (fun _=>[]) 0 (graphField xs)) (6*(graphField xs).length+5) := by
    convert moveOn_executes g (1:Fin 6) 0 3 (by decide) (by decide) (by decide)
      (Function.update (fun _=>[]) 1 (graphField xs)) rfl using 1
    funext i;fin_cases i <;> simp
  have hi : Field.store xs [] [] [] [] []=Function.update (fun _=>[]) 0 xs := by
    funext i;fin_cases i <;> rfl
  rw [hi] at ha
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hm)),?_⟩
  simp only [time,eval_add,eval_mul,eval_ofNat,eval_X]
  omega

theorem program_executes (g : BitString→ℕ) (xs : BitString) :
    ∃s c,program.Executes g (Function.update (fun _=>[]) 0 xs) s c ∧
      s 0=graphField xs ∧c≤time.eval xs.length := by
  obtain ⟨c,hc,hb⟩:=program_executes_clean g xs
  exact ⟨_,c,hc,by simp,hb⟩

lemma field_queryFree : Field.program.QueryFree :=
  seq_queryFree _ _ (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) (push_queryFree _ _))
    (seq_queryFree _ _ (unpairOn_queryFree _) (decision_queryFree _ _ _))
lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ field_queryFree
    (seq_queryFree _ _ (branchPop_queryFree _ _ _ _ (clear_queryFree _) (clear_queryFree _) skip_queryFree)
      (seq_queryFree _ _ (cleanup_queryFree _) (moveOn_queryFree _ _ _ _ _ _)))
lemma size_bound (xs : BitString) : (graphField xs).length≤size.eval xs.length := by
  simpa only [size,eval_X] using graphField_length xs

/-- The both-supplied packet places its graph inside its first field's first
field. Each stage cleans its work stacks before the next starts. -/
def nestedGraphField (xs : BitString) : BitString := graphField (graphField xs)
noncomputable def nestedProgram : OracleBlock 5 := seq program program
noncomputable def nestedTime : Polynomial ℕ := 40*X+142
lemma nestedGraphField_length (xs : BitString) : (nestedGraphField xs).length≤xs.length :=
  (graphField_length (graphField xs)).trans (graphField_length xs)

theorem nestedProgram_executes_clean (g : BitString→ℕ) (xs : BitString) :
    ∃c,nestedProgram.Executes g (Function.update (fun _=>[]) 0 xs)
      (Function.update (fun _=>[]) 0 (nestedGraphField xs)) c ∧c≤nestedTime.eval xs.length := by
  obtain ⟨a,ha,hba⟩:=program_executes_clean g xs
  obtain ⟨b,hb,hbb⟩:=program_executes_clean g (graphField xs)
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  have hl:=graphField_length xs
  simp only [time,nestedTime,eval_add,eval_mul,eval_ofNat,eval_X] at hba hbb ⊢
  omega

theorem nestedProgram_executes (g : BitString→ℕ) (xs : BitString) :
    ∃s c,nestedProgram.Executes g (Function.update (fun _=>[]) 0 xs) s c ∧
      s 0=nestedGraphField xs ∧c≤nestedTime.eval xs.length := by
  obtain ⟨c,hc,hb⟩:=nestedProgram_executes_clean g xs
  exact ⟨_,c,hc,by simp,hb⟩
lemma nestedProgram_queryFree : nestedProgram.QueryFree :=
  seq_queryFree _ _ program_queryFree program_queryFree
lemma nestedSize_bound (xs : BitString) : (nestedGraphField xs).length≤size.eval xs.length := by
  simpa only [size,eval_X] using nestedGraphField_length xs

end HiddenCircuits.GraphReduction.Runtime.SuppliedMembership
