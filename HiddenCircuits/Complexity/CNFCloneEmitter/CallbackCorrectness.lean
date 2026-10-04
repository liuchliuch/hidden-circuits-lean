import HiddenCircuits.Complexity.CNFCloneEmitter.CallbackDecision

namespace HiddenCircuits.Complexity.CNFCloneEmitter.Callback
open OracleBlock
variable {n m : ℕ}

lemma edgeOfBases_correct (F : CNF n m) (a b : ℕ)
    (u v : Cloning.Vertex (CNF.cloneMultiplicity (n:=n) (m:=m) a b)) :
    edgeOfBases F (CNF.cloneVertexFinEquiv a b u).val (CNF.cloneVertexFinEquiv a b v).val u.1 v.1=
      decide ((F.cloneGraph a b).Adj u v) := by
  rcases u with ⟨u,k⟩
  rcases v with ⟨v,l⟩
  cases u with
  | inl u =>
    rcases u with ⟨i,s⟩
    cases v with
    | inl v =>
      rcases v with ⟨j,t⟩
      simp only [edgeOfBases,variable_clone_adj,Fin.val_inj]
    | inr j => simp only [edgeOfBases,cross_clone_adj]
  | inr i =>
    cases v with
    | inl v =>
      rcases v with ⟨j,t⟩
      have h : (F.cloneGraph a b).Adj ⟨Sum.inr i,k⟩ ⟨Sum.inl (j,t),l⟩ ↔ (j,t)∈F.clause i :=
        ((F.cloneGraph a b).adj_comm _ _).trans (cross_clone_adj F j t i l k)
      simp only [edgeOfBases,h]
    | inr j => simp only [edgeOfBases,clause_clone_adj,Fin.val_inj]

def edge (F : CNF n m) (a b i j : ℕ) : Bool :=
  if hi : i<order (n:=n) (m:=m) a b then
    if hj : j<order (n:=n) (m:=m) a b then (F.cloneQuery a b).2.edge ⟨i,hi⟩ ⟨j,hj⟩ else false
  else false

lemma edge_fin (F : CNF n m) (a b : ℕ) (i j : Fin (order (n:=n) (m:=m) a b)) :
    edge F a b i.val j.val=(F.cloneQuery a b).2.edge i j := by simp [edge,i.isLt,j.isLt]

lemma edge_at (F : CNF n m) (a b i j : ℕ)
    (hi : i<order (n:=n) (m:=m) a b) (hj : j<order (n:=n) (m:=m) a b) :
    edgeOfBases F i j ((CNF.cloneVertexFinEquiv (n:=n) (m:=m) a b).symm ⟨i,hi⟩).1
      ((CNF.cloneVertexFinEquiv (n:=n) (m:=m) a b).symm ⟨j,hj⟩).1=edge F a b i j := by
  have h := edgeOfBases_correct F a b ((CNF.cloneVertexFinEquiv (n:=n) (m:=m) a b).symm ⟨i,hi⟩)
    ((CNF.cloneVertexFinEquiv (n:=n) (m:=m) a b).symm ⟨j,hj⟩)
  simpa [edge,hi,hj,CNF.cloneQuery,MatrixGraph.relabel] using h

noncomputable def program : OracleBlock 29 := seq row (seq column decision)
def time (F : CNF n m) (a b : ℕ) : ℕ :=
  10000*((payload F).length+n+m+order (n:=n) (m:=m) a b+a+b+1)^2

/-- Full framed adjacency callback: both unary indices are decoded by real
arithmetic, every literal incidence is read from canonical CNF bytes, and all
six descriptor fields and nine work registers are physically cleared. -/
theorem program_executes (g : BitString → ℕ) (F : CNF n m) (a b i j : ℕ)
    (hi : i<order (n:=n) (m:=m) a b) (hj : j<order (n:=n) (m:=m) a b)
    (out inner outer : BitString) :
    ∃ cost, program.Executes g (state F a b i j [] out inner outer [] [] [] [] [] [])
      (state F a b i j [edge F a b i j] out inner outer [] [] [] [] [] []) cost ∧ cost≤time F a b := by
  obtain ⟨cr,hr,hbr⟩ := row_executes g F a b i j hi [] out inner outer
  obtain ⟨cc,hc,hbc⟩ := column_executes g F a b i j hj [] out inner outer
    [VertexRuntime.tag (descriptor (n:=n) a b i)]
    (List.replicate (VertexRuntime.number (descriptor (n:=n) a b i)) true)
    [VertexRuntime.sign (descriptor (n:=n) a b i)]
  let u := (CNF.cloneVertexFinEquiv (n:=n) (m:=m) a b).symm ⟨i,hi⟩
  let v := (CNF.cloneVertexFinEquiv (n:=n) (m:=m) a b).symm ⟨j,hj⟩
  have hu : descriptor (n:=n) a b i=baseDescriptor u.1 := descriptor_correct a b ⟨i,hi⟩
  have hv : descriptor (n:=n) a b j=baseDescriptor v.1 := descriptor_correct a b ⟨j,hj⟩
  rw [hu] at hr hc
  rw [hv] at hc
  obtain ⟨cd,hd,hbd⟩ := decision_executes g F a b i j u.1 v.1 out inner outer
  have he : edgeOfBases F i j u.1 v.1=edge F a b i j := edge_at F a b i j hi hj
  rw [he] at hd
  refine ⟨cr+(cc+cd+2)+2,seq_executes _ _ g hr (seq_executes _ _ g hc hd),?_⟩
  let N := order (n:=n) (m:=m) a b
  let B := (payload F).length+n+m+N+a+b+1
  have hB : 1≤B := by dsimp [B];omega
  have hcut : n*2*a≤N := by dsimp [N,order];omega
  have hrsize : i+n*2*a+a+b+1≤2*B := by dsimp [B];omega
  have hcsize : j+n*2*a+a+b+1≤2*B := by dsimp [B];omega
  have hdsize : (payload F).length+n+m+i+j+1≤2*B := by dsimp [B];omega
  have hpr := Nat.pow_le_pow_left hrsize 2
  have hpc := Nat.pow_le_pow_left hcsize 2
  have hpd := Nat.pow_le_pow_left hdsize 2
  change _≤10000*B^2
  nlinarith

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ row_queryFree
  (seq_queryFree _ _ column_queryFree decision_queryFree)

/-- Callback contract directly in the generic matrix engine's store format. -/
theorem matrix_callback (F : CNF n m) (a b : ℕ) :
    ∀ g i j out inner outer, i<order (n:=n) (m:=m) a b → j<order (n:=n) (m:=m) a b →
      ∃ cost, program.Executes g
        (MatrixEmitter.store (order (n:=n) (m:=m) a b) i j [] out inner outer (params F a b))
        (MatrixEmitter.store (order (n:=n) (m:=m) a b) i j [edge F a b i j] out inner outer (params F a b)) cost ∧
        cost≤time F a b := by
  intro g i j out inner outer hi hj
  simpa only [state_matrix] using program_executes g F a b i j hi hj out inner outer

end HiddenCircuits.Complexity.CNFCloneEmitter.Callback
