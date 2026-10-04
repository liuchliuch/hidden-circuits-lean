import HiddenCircuits.Complexity.CNFCloneEmitter.CallbackFrame

namespace HiddenCircuits.Complexity.CNFCloneEmitter.Callback
open OracleBlock
variable {n m : ℕ}

def groupEmbedding : Fin 6 ↪ Fin 30 where
  toFun i := (![16,19,3,21,22,23] : Fin 6 → Fin 30) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def indexEmbedding : Fin 6 ↪ Fin 30 where
  toFun i := (![1,2,24,21,22,23] : Fin 6 → Fin 30) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def forwardEmbedding : Fin 13 ↪ Fin 30 where
  toFun i := (![21,22,3,23,24,25,26,27,11,16,19,28,29] : Fin 13 → Fin 30) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def backwardEmbedding : Fin 13 ↪ Fin 30 where
  toFun i := (![21,22,3,23,24,25,26,27,11,19,16,28,29] : Fin 13 → Fin 30) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def groupEqual : OracleBlock 29 := GraphVerifier.Runtime.readLengthOn groupEmbedding
noncomputable def indexEqual : OracleBlock 29 := GraphVerifier.Runtime.readLengthOn indexEmbedding
noncomputable def setFalse : OracleBlock 29 := seq (clear 3) (push 3 false)
noncomputable def excludeDiagonal : OracleBlock 29 := branchPop 24 skip skip setFalse
noncomputable def sameGroup : OracleBlock 29 := seq groupEqual (seq indexEqual excludeDiagonal)
noncomputable def incidenceForward (s : Bool) : OracleBlock 29 := rename (Incidence.program s) forwardEmbedding
noncomputable def incidenceBackward (s : Bool) : OracleBlock 29 := rename (Incidence.program s) backwardEmbedding

lemma state_bit (F : CNF n m) (a b i j : ℕ) (old bit out inner outer rt rn rs ct cn cs : BitString) :
    Function.update (state F a b i j old out inner outer rt rn rs ct cn cs) 3 bit =
      state F a b i j bit out inner outer rt rn rs ct cn cs := by
  funext k;fin_cases k <;> rfl

theorem groupEqual_executes (g : BitString → ℕ) (F : CNF n m) (a b i j r c : ℕ)
    (out inner outer rs cs : BitString) :
    ∃ cost, groupEqual.Executes g
      (state F a b i j [] out inner outer [] (List.replicate r true) rs [] (List.replicate c true) cs)
      (state F a b i j [decide (r=c)] out inner outer [] (List.replicate r true) rs [] (List.replicate c true) cs) cost ∧
      cost≤13*(r+c)+23 := by
  obtain ⟨co,hc,hb⟩ := GraphVerifier.Runtime.readLengthOn_executes groupEmbedding g
    (state F a b i j [] out inner outer [] (List.replicate r true) rs [] (List.replicate c true) cs)
    (List.replicate r true) (List.replicate c true) (by funext k;fin_cases k <;> rfl)
  refine ⟨co,?_,by simpa using hb⟩
  simpa only [List.length_replicate,show groupEmbedding 2=3 from rfl,state_bit] using hc

theorem indexEqual_executes (g : BitString → ℕ) (F : CNF n m) (a b i j : ℕ)
    (bit out inner outer rn rs cn cs : BitString) :
    ∃ cost, indexEqual.Executes g (state F a b i j bit out inner outer [] rn rs [] cn cs)
      (Function.update (state F a b i j bit out inner outer [] rn rs [] cn cs) 24 [decide (i=j)]) cost ∧
      cost≤13*(i+j)+23 := by
  obtain ⟨co,hc,hb⟩ := GraphVerifier.Runtime.readLengthOn_executes indexEmbedding g
    (state F a b i j bit out inner outer [] rn rs [] cn cs)
    (List.replicate i true) (List.replicate j true) (by funext k;fin_cases k <;> rfl)
  exact ⟨co,by simpa using hc,by simpa using hb⟩

theorem setFalse_executes (g : BitString → ℕ) (F : CNF n m) (a b i j : ℕ) (bit : Bool)
    (out inner outer rn rs cn cs : BitString) :
    setFalse.Executes g (state F a b i j [bit] out inner outer [] rn rs [] cn cs)
      (state F a b i j [false] out inner outer [] rn rs [] cn cs) 5 := by
  have hc := clear_executes g (3 : Fin 30) (state F a b i j [bit] out inner outer [] rn rs [] cn cs)
  have hp := push_executes g (3 : Fin 30) false (state F a b i j [] out inner outer [] rn rs [] cn cs)
  rw [state_bit] at hc hp
  exact seq_executes _ _ g hc hp

theorem excludeDiagonal_executes (g : BitString → ℕ) (F : CNF n m) (a b i j : ℕ) (bit diagonal : Bool)
    (out inner outer rn rs cn cs : BitString) :
    ∃ cost, excludeDiagonal.Executes g
      (Function.update (state F a b i j [bit] out inner outer [] rn rs [] cn cs) 24 [diagonal])
      (state F a b i j [bit && !diagonal] out inner outer [] rn rs [] cn cs) cost ∧ cost≤7 := by
  have he : Function.update (Function.update (state F a b i j [bit] out inner outer [] rn rs [] cn cs) 24 [diagonal]) 24 []=
      state F a b i j [bit] out inner outer [] rn rs [] cn cs := by
    funext k;fin_cases k <;> simp [state,params]
  cases diagonal
  · refine ⟨3,?_,by omega⟩
    apply branchPop_false _ _ _ _ g (show (Function.update (state F a b i j [bit] out inner outer [] rn rs [] cn cs) 24 [false]) 24=false::[] by simp)
    rw [he]
    simpa using skip_executes g (state F a b i j [bit] out inner outer [] rn rs [] cn cs)
  · refine ⟨7,?_,by omega⟩
    apply branchPop_true _ _ _ _ g (show (Function.update (state F a b i j [bit] out inner outer [] rn rs [] cn cs) 24 [true]) 24=true::[] by simp)
    rw [he]
    simpa using setFalse_executes g F a b i j bit out inner outer rn rs cn cs

theorem sameGroup_executes (g : BitString → ℕ) (F : CNF n m) (a b i j r c : ℕ)
    (out inner outer rs cs : BitString) :
    ∃ cost, sameGroup.Executes g
      (state F a b i j [] out inner outer [] (List.replicate r true) rs [] (List.replicate c true) cs)
      (state F a b i j [decide (r=c ∧ i≠j)] out inner outer [] (List.replicate r true) rs [] (List.replicate c true) cs) cost ∧
      cost≤13*(r+c+i+j)+57 := by
  obtain ⟨cg,hg,hbg⟩ := groupEqual_executes g F a b i j r c out inner outer rs cs
  obtain ⟨ci,hi,hbi⟩ := indexEqual_executes g F a b i j [decide (r=c)] out inner outer (List.replicate r true) rs (List.replicate c true) cs
  obtain ⟨ce,he,hbe⟩ := excludeDiagonal_executes g F a b i j (decide (r=c)) (decide (i=j)) out inner outer
    (List.replicate r true) rs (List.replicate c true) cs
  refine ⟨cg+(ci+ce+2)+2,?_,by omega⟩
  simpa using seq_executes _ _ g hg (seq_executes _ _ g hi he)

theorem incidenceForward_executes (g : BitString → ℕ) (F : CNF n m) (a b i j : ℕ) (v : Fin n) (c : Fin m) (s : Bool)
    (out inner outer rs cs : BitString) :
    ∃ cost, (incidenceForward s).Executes g
      (state F a b i j [] out inner outer [] (List.replicate v.val true) rs [] (List.replicate c.val true) cs)
      (state F a b i j [decide ((v,s)∈F.clause c)] out inner outer [] (List.replicate v.val true) rs [] (List.replicate c.val true) cs) cost ∧
      cost≤500*((payload F).length+v.val+c.val+1)^2 := by
  obtain ⟨co,hc,hb⟩ := Incidence.program_executes g F v c s
  refine ⟨co,?_,hb⟩
  apply rename_executes_to _ forwardEmbedding g hc
  · funext k;fin_cases k <;> rfl
  · funext k;fin_cases k <;> rfl
  · intro k hk;fin_cases k <;> first | rfl | exact (hk 2 rfl).elim

theorem incidenceBackward_executes (g : BitString → ℕ) (F : CNF n m) (a b i j : ℕ) (v : Fin n) (c : Fin m) (s : Bool)
    (out inner outer rs cs : BitString) :
    ∃ cost, (incidenceBackward s).Executes g
      (state F a b i j [] out inner outer [] (List.replicate c.val true) rs [] (List.replicate v.val true) cs)
      (state F a b i j [decide ((v,s)∈F.clause c)] out inner outer [] (List.replicate c.val true) rs [] (List.replicate v.val true) cs) cost ∧
      cost≤500*((payload F).length+v.val+c.val+1)^2 := by
  obtain ⟨co,hc,hb⟩ := Incidence.program_executes g F v c s
  refine ⟨co,?_,hb⟩
  apply rename_executes_to _ backwardEmbedding g hc
  · funext k;fin_cases k <;> rfl
  · funext k;fin_cases k <;> rfl
  · intro k hk;fin_cases k <;> first | rfl | exact (hk 2 rfl).elim

lemma sameGroup_queryFree : sameGroup.QueryFree := seq_queryFree _ _ (GraphVerifier.Runtime.readLengthOn_queryFree _)
  (seq_queryFree _ _ (GraphVerifier.Runtime.readLengthOn_queryFree _)
    (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree
      (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _))))
lemma incidenceForward_queryFree (s : Bool) : (incidenceForward s).QueryFree := rename_queryFree _ _ (Incidence.program_queryFree s)
lemma incidenceBackward_queryFree (s : Bool) : (incidenceBackward s).QueryFree := rename_queryFree _ _ (Incidence.program_queryFree s)

end HiddenCircuits.Complexity.CNFCloneEmitter.Callback
