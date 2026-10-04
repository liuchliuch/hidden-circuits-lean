import HiddenCircuits.Complexity.OracleCleanup

/-! A concrete unary-controlled repetition routine, used for literal serialization
and polynomially bounded emitter loops. The counter is physically popped. -/
namespace HiddenCircuits.Complexity.OracleBlock
variable {k : ℕ}

noncomputable def repeatPrepend (counter target : Fin (k+1)) (pattern : BitString) : OracleBlock k :=
  whilePop counter (prepend target pattern) (prepend target pattern)

def workStore (s : Store k) (counter target : Fin (k+1)) (rest accumulated : BitString) : Store k :=
  Function.update (Function.update s counter rest) target accumulated

lemma workStore_counter (s : Store k) (counter target : Fin (k+1)) (hne : counter ≠ target)
    (rest accumulated : BitString) : workStore s counter target rest accumulated counter = rest := by
  simp [workStore,hne]

lemma workStore_pop (s : Store k) (counter target : Fin (k+1)) (hne : counter ≠ target)
    (b : Bool) (rest accumulated : BitString) :
    Function.update (workStore s counter target (b::rest) accumulated) counter rest =
      workStore s counter target rest accumulated := by
  rw [workStore,Function.update_comm (Ne.symm hne)]
  simp [workStore]

/-- Every counter bit causes one actual fixed-string prepend. The bit values are
irrelevant; only their physically scanned number determines the iteration count. -/
theorem repeatPrepend_execution (g : BitString → ℕ) (counter target : Fin (k+1))
    (hne : counter ≠ target) (pattern : BitString) (s : Store k) (xs accumulated : BitString) :
    WhileExecution counter (prepend target pattern) (prepend target pattern) g
      (workStore s counter target xs accumulated)
      (workStore s counter target [] ((List.replicate xs.length pattern).flatten++accumulated))
      ((3*pattern.length+3)*xs.length+1) := by
  induction xs generalizing accumulated with
  | nil =>
    apply WhileExecution.empty
    exact workStore_counter s counter target hne [] accumulated
  | cons bit xs ih =>
    have hp : (prepend target pattern).Executes g
        (Function.update (workStore s counter target (bit::xs) accumulated) counter xs)
        (workStore s counter target xs (pattern++accumulated)) (3*pattern.length+1) := by
      rw [workStore_pop s counter target hne]
      simpa [workStore] using prepend_executes g target pattern (workStore s counter target xs accumulated)
    have ht := ih (pattern++accumulated)
    have hscan := workStore_counter s counter target hne (bit::xs) accumulated
    have h : WhileExecution counter (prepend target pattern) (prepend target pattern) g
        (workStore s counter target (bit::xs) accumulated)
        (workStore s counter target [] ((List.replicate xs.length pattern).flatten++(pattern++accumulated)))
        (1+(3*pattern.length+1)+1+((3*pattern.length+3)*xs.length+1)) := by
      cases bit
      · exact WhileExecution.zero hscan hp ht
      · exact WhileExecution.one hscan hp ht
    convert h using 1
    · simp [List.replicate_succ',List.flatten_append,List.append_assoc]
    · simp only [List.length_cons];ring

theorem repeatPrepend_executes (g : BitString → ℕ) (counter target : Fin (k+1))
    (hne : counter ≠ target) (pattern : BitString) (s : Store k) :
    (repeatPrepend counter target pattern).Executes g s
      (Function.update (Function.update s counter []) target
        ((List.replicate (s counter).length pattern).flatten++s target))
      ((3*pattern.length+3)*(s counter).length+1) := by
  have h := whilePop_executes counter (prepend target pattern) (prepend target pattern) g
    (repeatPrepend_execution g counter target hne pattern s (s counter) (s target))
  simpa [workStore] using h

lemma prepend_queryFree (stack : Fin (k+1)) (bits : BitString) : (prepend stack bits).QueryFree := by
  induction bits with
  | nil => exact skip_queryFree
  | cons b bs ih => exact seq_queryFree _ _ ih (push_queryFree stack b)

lemma repeatPrepend_queryFree (counter target : Fin (k+1)) (pattern : BitString) :
    (repeatPrepend counter target pattern).QueryFree :=
  whilePop_queryFree _ _ _ (prepend_queryFree _ _) (prepend_queryFree _ _)

/-- Modular iteration rule for a real body that prepends a fixed runtime value
and preserves the counter remainder and all other store components. -/
theorem whilePrepend_execution (g : BitString → ℕ) (counter target : Fin (k+1))
    (hne : counter ≠ target) (B : OracleBlock k) (pattern : BitString) (bodyCost : ℕ) (s : Store k)
    (hbody : ∀ rest accumulated, B.Executes g
      (workStore s counter target rest accumulated)
      (workStore s counter target rest (pattern++accumulated)) bodyCost)
    (xs accumulated : BitString) :
    WhileExecution counter B B g (workStore s counter target xs accumulated)
      (workStore s counter target [] ((List.replicate xs.length pattern).flatten++accumulated))
      ((bodyCost+2)*xs.length+1) := by
  induction xs generalizing accumulated with
  | nil => exact WhileExecution.empty _ (workStore_counter s counter target hne [] accumulated)
  | cons bit xs ih =>
    have hp : B.Executes g
        (Function.update (workStore s counter target (bit::xs) accumulated) counter xs)
        (workStore s counter target xs (pattern++accumulated)) bodyCost := by
      rw [workStore_pop s counter target hne]
      exact hbody xs accumulated
    have ht := ih (pattern++accumulated)
    have hscan := workStore_counter s counter target hne (bit::xs) accumulated
    have h : WhileExecution counter B B g (workStore s counter target (bit::xs) accumulated)
        (workStore s counter target [] ((List.replicate xs.length pattern).flatten++(pattern++accumulated)))
        (1+bodyCost+1+((bodyCost+2)*xs.length+1)) := by
      cases bit
      · exact WhileExecution.zero hscan hp ht
      · exact WhileExecution.one hscan hp ht
    convert h using 1
    · simp [List.replicate_succ',List.flatten_append,List.append_assoc]
    · simp only [List.length_cons];ring

end HiddenCircuits.Complexity.OracleBlock
