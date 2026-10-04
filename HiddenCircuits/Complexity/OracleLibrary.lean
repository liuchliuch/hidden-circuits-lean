import HiddenCircuits.Complexity.OracleBlockLift
import HiddenCircuits.Complexity.OracleCopyProgram
import HiddenCircuits.Complexity.OracleIncrement

/-! Reusable finite bit-stack library with full-store specifications and exact
operational charges. None of these routines hide integer or list operations. -/
namespace HiddenCircuits.Complexity.OracleBlock
variable {k : ℕ}

def clear (stack : Fin (k+1)) : OracleBlock k where
  labelCount := 2
  start := 0
  exit := 1
  code q := if q = 0 then .pop stack 1 0 0 else .halt
  exit_halt := rfl

theorem clear_executes_aux (g : BitString → ℕ) (stack : Fin (k+1)) (s : Store k) (xs : BitString) :
    (clear stack).Executes g (Function.update s stack xs) (Function.update s stack []) (xs.length+1) := by
  induction xs with
  | nil => exact OracleMachine.Steps.single (by simp [OracleMachine.step,machine,clear,config])
  | cons bit xs ih =>
    have hp : (clear stack).machine.step g ((clear stack).config ⟨0,by simp [clear]⟩ (Function.update s stack (bit::xs))) =
        some ((clear stack).config ⟨0,by simp [clear]⟩ (Function.update s stack xs),1) := by
      cases bit <;> simp [OracleMachine.step,machine,clear,config]
    convert (OracleMachine.Steps.single hp).trans ih using 1 <;> simp only [List.length_cons] <;> omega

/-- Clear one stack and preserve every other stack in exactly length+1 steps. -/
theorem clear_executes (g : BitString → ℕ) (stack : Fin (k+1)) (s : Store k) :
    (clear stack).Executes g s (Function.update s stack []) ((s stack).length+1) := by
  simpa using clear_executes_aux g stack s (s stack)

lemma clear_queryFree (stack : Fin (k+1)) : (clear stack).QueryFree := by
  intro q i o next
  fin_cases q <;> simp [machine,clear]

/-- The literal constant is compiled into finitely many real pushes. -/
noncomputable def prepend (stack : Fin (k+1)) : BitString → OracleBlock k
  | [] => skip
  | b::bs => seq (prepend stack bs) (push stack b)

theorem prepend_executes (g : BitString → ℕ) (stack : Fin (k+1)) (xs : BitString) (s : Store k) :
    (prepend stack xs).Executes g s (Function.update s stack (xs++s stack)) (3*xs.length+1) := by
  induction xs with
  | nil => simpa [prepend] using skip_executes g s
  | cons b bs ih =>
    have hp := push_executes g stack b (Function.update s stack (bs++s stack))
    have h := seq_executes (prepend stack bs) (push stack b) g ih hp
    convert h using 1 <;> simp [prepend] <;> omega

def pairStore (a b : BitString) : Store 1 := Fin.cases a (fun _ => b)

def reverseBlock : OracleBlock 1 where
  labelCount := 4
  start := 0
  exit := 3
  code := BitPrograms.reverseMachine.code
  exit_halt := rfl

theorem reverseBlock_executes (g : BitString → ℕ) (a b : BitString) :
    reverseBlock.Executes g (pairStore a b) (pairStore [] (a.reverse++b)) (2*a.length+1) := by
  obtain ⟨d,hd,hc⟩ := OracleMachine.steps_embed BitPrograms.reverseMachine reverseBlock.machine
    (Function.Embedding.refl _) id (by intro q h;change BitPrograms.reverseMachine.code q = _;cases BitPrograms.reverseMachine.code q <;> rfl) g
    (d := reverseBlock.config reverseBlock.start (pairStore a b)) ⟨rfl,fun _ => rfl⟩
    (BitPrograms.reverse_steps g a b)
  have he : d = reverseBlock.config reverseBlock.exit (pairStore [] (a.reverse++b)) :=
    OracleConfig.ext hc.1 hc.2
  rwa [he] at hd

lemma reverseBlock_queryFree : reverseBlock.QueryFree := by
  intro q i o next
  fin_cases q <;> simp [machine,reverseBlock,BitPrograms.reverseMachine]

def pairEmbedding (a b : Fin (k+1)) (hne : a ≠ b) : Fin 2 ↪ Fin (k+1) where
  toFun := Fin.cases a (fun _ => b)
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hne h)
    · exact False.elim (hne h.symm)
    · rfl

@[simp] theorem pairEmbedding_zero (a b : Fin (k+1)) (hne : a ≠ b) : pairEmbedding a b hne 0 = a := rfl
@[simp] theorem pairEmbedding_one (a b : Fin (k+1)) (hne : a ≠ b) : pairEmbedding a b hne 1 = b := rfl

lemma restrict_pair (a b : Fin (k+1)) (hne : a ≠ b) (s : Store k) :
    s ∘ pairEmbedding a b hne = pairStore (s a) (s b) := by
  funext i;fin_cases i <;> rfl

lemma install_pair (a b : Fin (k+1)) (hne : a ≠ b) (s : Store k) (x y : BitString) :
    install (pairEmbedding a b hne) s (pairStore x y) = Function.update (Function.update s a x) b y := by
  funext i
  by_cases ha : i = a
  · subst i
    have h := install_image (pairEmbedding a b hne) s (pairStore x y) 0
    simpa [pairStore,hne] using h
  · by_cases hb : i = b
    · subst i
      have h := install_image (pairEmbedding a b hne) s (pairStore x y) 1
      simpa [pairStore] using h
    · rw [install_off]
      · simp [ha,hb]
      · intro j
        fin_cases j
        · exact Ne.symm ha
        · exact Ne.symm hb

noncomputable def reverseOn (a b : Fin (k+1)) (hne : a ≠ b) : OracleBlock k :=
  rename reverseBlock (pairEmbedding a b hne)

/-- Arbitrary-stack reversal with a complete frame and a preexisting target suffix. -/
theorem reverseOn_executes (g : BitString → ℕ) (a b : Fin (k+1)) (hne : a ≠ b) (s : Store k) :
    (reverseOn a b hne).Executes g s
      (Function.update (Function.update s a []) b ((s a).reverse++s b)) (2*(s a).length+1) := by
  have h := rename_executes reverseBlock (pairEmbedding a b hne) g s
    (by rw [restrict_pair];exact reverseBlock_executes g (s a) (s b))
  simpa only [install_pair] using h

lemma reverseOn_queryFree (a b : Fin (k+1)) (hne : a ≠ b) : (reverseOn a b hne).QueryFree :=
  rename_queryFree reverseBlock (pairEmbedding a b hne) reverseBlock_queryFree

def incrementBlock : OracleBlock 1 where
  labelCount := 6
  start := 0
  exit := 5
  code := BitPrograms.incrementMachine.code
  exit_halt := rfl

theorem incrementBlock_executes (g : BitString → ℕ) (s : BitString) :
    incrementBlock.Executes g (pairStore s []) (pairStore (BitPrograms.incrementBits s) [])
      (4*BitPrograms.leadingOnes s+3) :=
  (BitPrograms.increment_runs g s).toSteps

def tripleStore (a b c : BitString) : Store 2 := Fin.cases a (Fin.cases b (fun _ => c))

def tripleEmbedding (a b c : Fin (k+1)) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Fin 3 ↪ Fin (k+1) where
  toFun := Fin.cases a (Fin.cases b (fun _ => c))
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals first | rfl | exact (hab h).elim | exact (hab h.symm).elim |
      exact (hac h).elim | exact (hac h.symm).elim | exact (hbc h).elim | exact (hbc h.symm).elim

def copyBlock : OracleBlock 2 where
  labelCount := 9
  start := 0
  exit := 8
  code := BitPrograms.copyMachine.code
  exit_halt := rfl

theorem copyBlock_executes (g : BitString → ℕ) (source target : BitString) :
    copyBlock.Executes g (tripleStore source target [])
      (tripleStore source (source++target) []) (5*source.length+2) := by
  obtain ⟨d,hd,hc⟩ := OracleMachine.steps_embed BitPrograms.copyMachine copyBlock.machine
    (Function.Embedding.refl _) id
    (by intro q h;change BitPrograms.copyMachine.code q = _;cases BitPrograms.copyMachine.code q <;> rfl) g
    (d := copyBlock.config copyBlock.start (tripleStore source target [])) ⟨rfl,fun _ => rfl⟩
    (BitPrograms.copy_steps g source target)
  have he : d = copyBlock.config copyBlock.exit (tripleStore source (source++target) []) :=
    OracleConfig.ext hc.1 hc.2
  rwa [he] at hd

lemma copyBlock_queryFree : copyBlock.QueryFree := by
  intro q i o next
  fin_cases q <;> simp [machine,copyBlock,BitPrograms.copyMachine]

noncomputable def copyOn (source target temporary : Fin (k+1))
    (hst : source ≠ target) (hsu : source ≠ temporary) (htu : target ≠ temporary) : OracleBlock k :=
  rename copyBlock (tripleEmbedding source target temporary hst hsu htu)

/-- Copy to an existing target suffix while restoring the source and clearing
the temporary, preserving every other stack. -/
theorem copyOn_executes (g : BitString → ℕ) (source target temporary : Fin (k+1))
    (hst : source ≠ target) (hsu : source ≠ temporary) (htu : target ≠ temporary)
    (s : Store k) (hzero : s temporary = []) :
    (copyOn source target temporary hst hsu htu).Executes g s
      (Function.update s target (s source++s target)) (5*(s source).length+2) := by
  apply rename_executes_to copyBlock (tripleEmbedding source target temporary hst hsu htu) g
    (copyBlock_executes g (s source) (s target))
  · funext i
    fin_cases i
    · rfl
    · rfl
    · exact hzero
  · funext i
    fin_cases i
    · exact Function.update_of_ne hst _ _
    · exact Function.update_self _ _ _
    · change Function.update s target (s source++s target) temporary = []
      rw [Function.update_of_ne (Ne.symm htu)]
      exact hzero
  · intro j hj
    exact Function.update_of_ne (Ne.symm (hj 1)) _ _

lemma copyOn_queryFree (source target temporary : Fin (k+1))
    (hst : source ≠ target) (hsu : source ≠ temporary) (htu : target ≠ temporary) :
    (copyOn source target temporary hst hsu htu).QueryFree :=
  rename_queryFree copyBlock _ copyBlock_queryFree

end HiddenCircuits.Complexity.OracleBlock
