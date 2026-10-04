import HiddenCircuits.Complexity.CNFCloneEmitter.CallbackPrimitives

namespace HiddenCircuits.Complexity.CNFCloneEmitter.Callback
open OracleBlock
variable {n m : ℕ}

lemma state_rowTag (F : CNF n m) (a b i j : ℕ) (bit out inner outer rt rn rs ct cn cs next : BitString) :
    Function.update (state F a b i j bit out inner outer rt rn rs ct cn cs) 15 next=
      state F a b i j bit out inner outer next rn rs ct cn cs := by funext k;fin_cases k <;> rfl
lemma state_colTag (F : CNF n m) (a b i j : ℕ) (bit out inner outer rt rn rs ct cn cs next : BitString) :
    Function.update (state F a b i j bit out inner outer rt rn rs ct cn cs) 18 next=
      state F a b i j bit out inner outer rt rn rs next cn cs := by funext k;fin_cases k <;> rfl
lemma state_rowSign (F : CNF n m) (a b i j : ℕ) (bit out inner outer rt rn rs ct cn cs next : BitString) :
    Function.update (state F a b i j bit out inner outer rt rn rs ct cn cs) 17 next=
      state F a b i j bit out inner outer rt rn next ct cn cs := by funext k;fin_cases k <;> rfl
lemma state_colSign (F : CNF n m) (a b i j : ℕ) (bit out inner outer rt rn rs ct cn cs next : BitString) :
    Function.update (state F a b i j bit out inner outer rt rn rs ct cn cs) 20 next=
      state F a b i j bit out inner outer rt rn rs ct cn next := by funext k;fin_cases k <;> rfl

noncomputable def cleanup : OracleBlock 29 := seq (clear 16) (seq (clear 17) (seq (clear 19) (clear 20)))
noncomputable def forward : OracleBlock 29 := branchPop 17 skip (incidenceForward false) (incidenceForward true)
noncomputable def backward : OracleBlock 29 := branchPop 20 skip (incidenceBackward false) (incidenceBackward true)
noncomputable def sameDone : OracleBlock 29 := seq sameGroup cleanup
noncomputable def forwardDone : OracleBlock 29 := seq forward cleanup
noncomputable def backwardDone : OracleBlock 29 := seq backward cleanup
noncomputable def chooseClauseRow : OracleBlock 29 := branchPop 18 skip sameDone backwardDone
noncomputable def chooseVariableRow : OracleBlock 29 := branchPop 18 skip forwardDone sameDone
noncomputable def decision : OracleBlock 29 := branchPop 15 skip chooseClauseRow chooseVariableRow

theorem cleanup_executes (g : BitString → ℕ) (F : CNF n m) (a b i j : ℕ)
    (bit out inner outer rn rs cn cs : BitString) :
    cleanup.Executes g (state F a b i j bit out inner outer [] rn rs [] cn cs)
      (state F a b i j bit out inner outer [] [] [] [] [] []) (rn.length+rs.length+cn.length+cs.length+10) := by
  have h1 : (clear (16:Fin 30)).Executes g (state F a b i j bit out inner outer [] rn rs [] cn cs)
      (state F a b i j bit out inner outer [] [] rs [] cn cs) (rn.length+1) := by
    convert clear_executes g (16:Fin 30) (state F a b i j bit out inner outer [] rn rs [] cn cs) using 1
    funext k;fin_cases k <;> rfl
  have h2 : (clear (17:Fin 30)).Executes g (state F a b i j bit out inner outer [] [] rs [] cn cs)
      (state F a b i j bit out inner outer [] [] [] [] cn cs) (rs.length+1) := by
    convert clear_executes g (17:Fin 30) (state F a b i j bit out inner outer [] [] rs [] cn cs) using 1
    funext k;fin_cases k <;> rfl
  have h3 : (clear (19:Fin 30)).Executes g (state F a b i j bit out inner outer [] [] [] [] cn cs)
      (state F a b i j bit out inner outer [] [] [] [] [] cs) (cn.length+1) := by
    convert clear_executes g (19:Fin 30) (state F a b i j bit out inner outer [] [] [] [] cn cs) using 1
    funext k;fin_cases k <;> rfl
  have h4 : (clear (20:Fin 30)).Executes g (state F a b i j bit out inner outer [] [] [] [] [] cs)
      (state F a b i j bit out inner outer [] [] [] [] [] []) (cs.length+1) := by
    convert clear_executes g (20:Fin 30) (state F a b i j bit out inner outer [] [] [] [] [] cs) using 1
    funext k;fin_cases k <;> rfl
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)) using 1 <;> omega

theorem sameDone_executes (g : BitString → ℕ) (F : CNF n m) (a b i j r c : ℕ)
    (out inner outer rs cs : BitString) :
    ∃ cost, sameDone.Executes g
      (state F a b i j [] out inner outer [] (List.replicate r true) rs [] (List.replicate c true) cs)
      (state F a b i j [decide (r=c ∧ i≠j)] out inner outer [] [] [] [] [] []) cost ∧
      cost≤14*(r+c)+13*(i+j)+rs.length+cs.length+69 := by
  obtain ⟨co,hc,hb⟩ := sameGroup_executes g F a b i j r c out inner outer rs cs
  have hcl := cleanup_executes g F a b i j [decide (r=c ∧ i≠j)] out inner outer (List.replicate r true) rs (List.replicate c true) cs
  refine ⟨co+((List.replicate r true).length+rs.length+(List.replicate c true).length+cs.length+10)+2,
    seq_executes _ _ g hc hcl,?_⟩
  simp only [List.length_replicate];omega

theorem forward_executes (g : BitString → ℕ) (F : CNF n m) (a b i j : ℕ) (v : Fin n) (c : Fin m) (s : Bool)
    (out inner outer cs : BitString) :
    ∃ cost, forward.Executes g
      (state F a b i j [] out inner outer [] (List.replicate v.val true) [s] [] (List.replicate c.val true) cs)
      (state F a b i j [decide ((v,s)∈F.clause c)] out inner outer [] (List.replicate v.val true) [] [] (List.replicate c.val true) cs) cost ∧
      cost≤500*((payload F).length+v.val+c.val+1)^2+2 := by
  obtain ⟨co,hc,hb⟩ := incidenceForward_executes g F a b i j v c s out inner outer [] cs
  refine ⟨co+2,?_,by omega⟩
  cases s
  · apply branchPop_false _ _ _ _ g rfl;rw [state_rowSign];exact hc
  · apply branchPop_true _ _ _ _ g rfl;rw [state_rowSign];exact hc

theorem backward_executes (g : BitString → ℕ) (F : CNF n m) (a b i j : ℕ) (v : Fin n) (c : Fin m) (s : Bool)
    (out inner outer rs : BitString) :
    ∃ cost, backward.Executes g
      (state F a b i j [] out inner outer [] (List.replicate c.val true) rs [] (List.replicate v.val true) [s])
      (state F a b i j [decide ((v,s)∈F.clause c)] out inner outer [] (List.replicate c.val true) rs [] (List.replicate v.val true) []) cost ∧
      cost≤500*((payload F).length+v.val+c.val+1)^2+2 := by
  obtain ⟨co,hc,hb⟩ := incidenceBackward_executes g F a b i j v c s out inner outer rs []
  refine ⟨co+2,?_,by omega⟩
  cases s
  · apply branchPop_false _ _ _ _ g rfl;rw [state_colSign];exact hc
  · apply branchPop_true _ _ _ _ g rfl;rw [state_colSign];exact hc

theorem forwardDone_executes (g : BitString → ℕ) (F : CNF n m) (a b i j : ℕ) (v : Fin n) (c : Fin m) (s : Bool)
    (out inner outer cs : BitString) :
    ∃ cost, forwardDone.Executes g
      (state F a b i j [] out inner outer [] (List.replicate v.val true) [s] [] (List.replicate c.val true) cs)
      (state F a b i j [decide ((v,s)∈F.clause c)] out inner outer [] [] [] [] [] []) cost ∧
      cost≤500*((payload F).length+v.val+c.val+1)^2+v.val+c.val+cs.length+14 := by
  obtain ⟨co,hc,hb⟩ := forward_executes g F a b i j v c s out inner outer cs
  have hcl := cleanup_executes g F a b i j [decide ((v,s)∈F.clause c)] out inner outer (List.replicate v.val true) [] (List.replicate c.val true) cs
  refine ⟨co+((List.replicate v.val true).length+[].length+(List.replicate c.val true).length+cs.length+10)+2,
    seq_executes _ _ g hc hcl,?_⟩
  simp only [List.length_replicate,List.length_nil];omega

theorem backwardDone_executes (g : BitString → ℕ) (F : CNF n m) (a b i j : ℕ) (v : Fin n) (c : Fin m) (s : Bool)
    (out inner outer rs : BitString) :
    ∃ cost, backwardDone.Executes g
      (state F a b i j [] out inner outer [] (List.replicate c.val true) rs [] (List.replicate v.val true) [s])
      (state F a b i j [decide ((v,s)∈F.clause c)] out inner outer [] [] [] [] [] []) cost ∧
      cost≤500*((payload F).length+v.val+c.val+1)^2+v.val+c.val+rs.length+14 := by
  obtain ⟨co,hc,hb⟩ := backward_executes g F a b i j v c s out inner outer rs
  have hcl := cleanup_executes g F a b i j [decide ((v,s)∈F.clause c)] out inner outer (List.replicate c.val true) rs (List.replicate v.val true) []
  refine ⟨co+((List.replicate c.val true).length+rs.length+(List.replicate v.val true).length+[].length+10)+2,
    seq_executes _ _ g hc hcl,?_⟩
  simp only [List.length_replicate,List.length_nil];omega

def edgeOfBases (F : CNF n m) (i j : ℕ) : CNF.Vertex (n:=n) (m:=m) → CNF.Vertex (n:=n) (m:=m) → Bool
  | .inl r, .inl c => decide (r.1.val=c.1.val ∧ i≠j)
  | .inr r, .inr c => decide (r.val=c.val ∧ i≠j)
  | .inl r, .inr c => decide (r∈F.clause c)
  | .inr r, .inl c => decide (c∈F.clause r)

theorem decision_executes (g : BitString → ℕ) (F : CNF n m) (a b i j : ℕ)
    (r c : CNF.Vertex (n:=n) (m:=m)) (out inner outer : BitString) :
    ∃ cost, decision.Executes g
      (state F a b i j [] out inner outer [VertexRuntime.tag (baseDescriptor r)]
        (List.replicate (VertexRuntime.number (baseDescriptor r)) true) [VertexRuntime.sign (baseDescriptor r)]
        [VertexRuntime.tag (baseDescriptor c)] (List.replicate (VertexRuntime.number (baseDescriptor c)) true)
        [VertexRuntime.sign (baseDescriptor c)])
      (state F a b i j [edgeOfBases F i j r c] out inner outer [] [] [] [] [] []) cost ∧
      cost≤1000*((payload F).length+n+m+i+j+1)^2 := by
  let N := (payload F).length+n+m+i+j+1
  have hN : 1≤N := by dsimp [N];omega
  cases r with
  | inl r =>
    rcases r with ⟨r,rs⟩
    cases c with
    | inl c =>
      rcases c with ⟨c,cs⟩
      obtain ⟨co,hc,hb⟩ := sameDone_executes g F a b i j r.val c.val out inner outer [rs] [cs]
      refine ⟨co+2+2,?_,?_⟩
      · apply branchPop_true _ _ _ _ g rfl
        rw [state_rowTag]
        apply branchPop_true _ _ _ _ g rfl
        rw [state_colTag];exact hc
      · have hr := r.isLt;have hc' := c.isLt
        simp only [List.length_singleton] at hb
        change _≤1000*N^2
        have hl : 14*(r.val+c.val)+13*(i+j)+75≤100*N := by dsimp [N];omega
        nlinarith
    | inr c =>
      obtain ⟨co,hc,hb⟩ := forwardDone_executes g F a b i j r c rs out inner outer [false]
      refine ⟨co+2+2,?_,?_⟩
      · apply branchPop_true _ _ _ _ g rfl
        rw [state_rowTag]
        apply branchPop_false _ _ _ _ g rfl
        rw [state_colTag];exact hc
      · have hr := r.isLt;have hc' := c.isLt
        have hsize : (payload F).length+r.val+c.val+1≤N := by dsimp [N];omega
        have hp := Nat.pow_le_pow_left hsize 2
        simp only [List.length_singleton] at hb
        change _≤1000*N^2
        have hl : r.val+c.val+19≤20*N := by dsimp [N];omega
        nlinarith
  | inr r =>
    cases c with
    | inl c =>
      rcases c with ⟨c,cs⟩
      obtain ⟨co,hc,hb⟩ := backwardDone_executes g F a b i j c r cs out inner outer [false]
      refine ⟨co+2+2,?_,?_⟩
      · apply branchPop_false _ _ _ _ g rfl
        rw [state_rowTag]
        apply branchPop_true _ _ _ _ g rfl
        rw [state_colTag];exact hc
      · have hr := r.isLt;have hc' := c.isLt
        have hsize : (payload F).length+c.val+r.val+1≤N := by dsimp [N];omega
        have hp := Nat.pow_le_pow_left hsize 2
        simp only [List.length_singleton] at hb
        change _≤1000*N^2
        have hl : c.val+r.val+19≤20*N := by dsimp [N];omega
        nlinarith
    | inr c =>
      obtain ⟨co,hc,hb⟩ := sameDone_executes g F a b i j r.val c.val out inner outer [false] [false]
      refine ⟨co+2+2,?_,?_⟩
      · apply branchPop_false _ _ _ _ g rfl
        rw [state_rowTag]
        apply branchPop_false _ _ _ _ g rfl
        rw [state_colTag];exact hc
      · have hr := r.isLt;have hc' := c.isLt
        simp only [List.length_singleton] at hb
        change _≤1000*N^2
        have hl : 14*(r.val+c.val)+13*(i+j)+75≤100*N := by dsimp [N];omega
        nlinarith

lemma cleanup_queryFree : cleanup.QueryFree := seq_queryFree _ _ (clear_queryFree _)
  (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))
lemma sameDone_queryFree : sameDone.QueryFree := seq_queryFree _ _ sameGroup_queryFree cleanup_queryFree
lemma forwardDone_queryFree : forwardDone.QueryFree := seq_queryFree _ _
  (branchPop_queryFree _ _ _ _ skip_queryFree (incidenceForward_queryFree _) (incidenceForward_queryFree _)) cleanup_queryFree
lemma backwardDone_queryFree : backwardDone.QueryFree := seq_queryFree _ _
  (branchPop_queryFree _ _ _ _ skip_queryFree (incidenceBackward_queryFree _) (incidenceBackward_queryFree _)) cleanup_queryFree
lemma decision_queryFree : decision.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree
  (branchPop_queryFree _ _ _ _ skip_queryFree sameDone_queryFree backwardDone_queryFree)
  (branchPop_queryFree _ _ _ _ skip_queryFree forwardDone_queryFree sameDone_queryFree)

end HiddenCircuits.Complexity.CNFCloneEmitter.Callback
