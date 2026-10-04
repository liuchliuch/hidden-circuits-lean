import HiddenCircuits.ExactSampling.Runtime.WeightCore

/-! Physical unary-clock enumeration of the first adjacency row. Every emitted
word comes from an actual edge branch and the checked binary counter. -/
namespace HiddenCircuits.ExactSampling.Runtime.WeightCompiler
open Complexity OracleBlock BinaryArithmetic
open Approximation.SelfReduction.Runtime
set_option maxHeartbeats 1800000

lemma update_data (raw out index clock data word acc xs : BitString) :
    Function.update (state raw out index clock data word acc) 4 xs=
      state raw out index clock xs word acc := by
  funext i;fin_cases i <;> simp [state]
lemma update_clock (raw out index clock data word acc xs : BitString) :
    Function.update (state raw out index clock data word acc) 3 xs=
      state raw out index xs data word acc := by
  funext i;fin_cases i <;> simp [state]

lemma choose_executes (g : BitString→ℕ) {N : ℕ} (G : MatrixGraph (N+1))
    (j : Fin (N+1)) (out clock data acc : BitString) :
    ∃t,choose.Executes g
      (state (GraphInput.encode ⟨N+1,G⟩) out (unary j.val) clock (G.edge 0 j::data) [] acc)
      (state (GraphInput.encode ⟨N+1,G⟩) out (unary j.val) clock data (weightWord G j) acc) t ∧
      t≤countBound (GraphInput.encode ⟨N+1,G⟩).length+3 := by
  cases he : G.edge 0 j
  · refine ⟨3,?_,by omega⟩
    have hh := branchPop_false (4:Fin 60) skip skip countEdge g
      (s:=state (GraphInput.encode ⟨N+1,G⟩) out (unary j.val) clock (false::data) [] acc)
      rfl (by rw [update_data];exact skip_executes g _)
    simpa [choose,weightWord,he] using hh
  · obtain ⟨t,ht,hb⟩ := countEdge_executes g G j out clock data acc
    refine ⟨t+2,?_,by omega⟩
    have hh := branchPop_true (4:Fin 60) skip skip countEdge g
      (s:=state (GraphInput.encode ⟨N+1,G⟩) out (unary j.val) clock (true::data) [] acc)
      rfl (by rw [update_data];exact ht)
    simpa [choose,weightWord,he] using hh

lemma weightWord_length {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1)) :
    (weightWord G j).length≤(GraphInput.encode ⟨N+1,G⟩).length+
      DH.BinaryRuntime.time.eval (GraphInput.encode ⟨N+1,G⟩).length := by
  unfold weightWord
  split
  · exact (function_length _).trans (Nat.add_le_add (residual_length G j)
      (polynomial_nat_eval_mono _ (residual_length G j)))
  · simp

noncomputable def bodyBound (L : ℕ) : ℕ := countBound L+6*(L+DH.BinaryRuntime.time.eval L)+15

lemma body_executes (g : BitString→ℕ) {N : ℕ} (G : MatrixGraph (N+1))
    (j : Fin (N+1)) (out clock data acc : BitString) :
    ∃t,body.Executes g
      (state (GraphInput.encode ⟨N+1,G⟩) out (unary j.val) clock (G.edge 0 j::data) [] acc)
      (state (GraphInput.encode ⟨N+1,G⟩) out (unary (j.val+1)) clock data []
        ((wordChunk (weightWord G j)).reverse++acc)) t ∧
      t≤bodyBound (GraphInput.encode ⟨N+1,G⟩).length := by
  obtain ⟨a,ha,hab⟩ := choose_executes g G j out clock data acc
  have he := emit_executes g (GraphInput.encode ⟨N+1,G⟩) out (unary j.val) clock data (weightWord G j) acc
  have hp : (push (2:Fin 60) true).Executes g
      (state (GraphInput.encode ⟨N+1,G⟩) out (unary j.val) clock data [] ((wordChunk (weightWord G j)).reverse++acc))
      (state (GraphInput.encode ⟨N+1,G⟩) out (unary (j.val+1)) clock data [] ((wordChunk (weightWord G j)).reverse++acc)) 1 := by
    convert push_executes g (2:Fin 60) true
      (state (GraphInput.encode ⟨N+1,G⟩) out (unary j.val) clock data [] ((wordChunk (weightWord G j)).reverse++acc)) using 1
    funext i;fin_cases i <;> simp [state,List.replicate_succ]
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g he hp),?_⟩
  have hw := weightWord_length G j
  unfold bodyBound
  omega

/-- A suffix of candidates, indexed only for the semantic invariant. -/
def candidates {n : ℕ} (j r : ℕ) (h : j+r≤n) : Fin r→Fin n :=
  fun i => ⟨j+i.val,by have := i.isLt;omega⟩

lemma loop_execution (g : BitString→ℕ) {N : ℕ} (G : MatrixGraph (N+1))
    (r j : ℕ) (hjr : j+r≤N+1) (out tail acc : BitString) :
    ∃t,WhileExecution (3:Fin 60) body body g
      (state (GraphInput.encode ⟨N+1,G⟩) out (unary j) (unary r)
        (List.ofFn (fun i => G.edge 0 (candidates j r hjr i))++tail) [] acc)
      (state (GraphInput.encode ⟨N+1,G⟩) out (unary (j+r)) [] tail []
        ((encodeBitList (List.ofFn (fun i => weightWord G (candidates j r hjr i)))).reverse++acc)) t ∧
      t≤r*(bodyBound (GraphInput.encode ⟨N+1,G⟩).length+2)+1 := by
  induction r generalizing j acc with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [encodeBitList] using (WhileExecution.empty
      (stack:=(3:Fin 60)) (B:=body) (C:=body) (g:=g)
      (state (GraphInput.encode ⟨N+1,G⟩) out (unary j) [] tail [] acc) rfl)
  | succ r ih =>
    let v : Fin (N+1) := ⟨j,by omega⟩
    have hr : (j+1)+r≤N+1 := by omega
    have ec : (fun i : Fin r => candidates j (r+1) hjr i.succ)=candidates (j+1) r hr := by
      funext i;apply Fin.ext;simp [candidates];omega
    have ec' (i : Fin r) : candidates j (r+1) hjr i.succ=candidates (j+1) r hr i := congrFun ec i
    have ez : candidates j (r+1) hjr 0=v := by apply Fin.ext;simp [candidates,v]
    obtain ⟨a,ha,hab⟩ := body_executes g G v out (unary r)
      (List.ofFn (fun i => G.edge 0 (candidates (j+1) r hr i))++tail) acc
    obtain ⟨b,hb,hbb⟩ := ih (j+1) hr ((wordChunk (weightWord G v)).reverse++acc)
    have hh := WhileExecution.one (stack:=(3:Fin 60))
      (s:=state (GraphInput.encode ⟨N+1,G⟩) out (unary j) (unary (r+1))
        (G.edge 0 v::(List.ofFn (fun i => G.edge 0 (candidates (j+1) r hr i))++tail)) [] acc)
      (show unary (r+1)=true::unary r from List.replicate_succ)
      (by rw [update_clock];exact ha) hb
    refine ⟨1+a+1+b,?_,?_⟩
    · simpa [List.ofFn_succ,ez,ec',encodeBitList_eq_chunks,List.reverse_append,List.append_assoc,
        Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh
    · nlinarith

lemma firstRow {N : ℕ} (G : MatrixGraph (N+1)) :
    G.bits=List.ofFn (fun j : Fin (N+1) => G.edge 0 j)++G.bits.drop (N+1) := by
  have hh : G.bits.take (N+1)=List.ofFn (fun j : Fin (N+1) => G.edge 0 j) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      have hn : i<N+1 := by simpa using hi'
      rw [List.getElem_take,List.getElem_ofFn]
      have hidx : (finProdFinEquiv ((0:Fin (N+1)),⟨i,hn⟩)).val=i := by simp
      have hg := G.get_bits (0:Fin (N+1)) ⟨i,hn⟩ (by simp;omega)
      simpa [hidx] using hg
  rw [←hh,List.take_append_drop]

lemma loop_executes (g : BitString→ℕ) {N : ℕ} (G : MatrixGraph (N+1)) (out : BitString) :
    ∃t,loop.Executes g
      (state (GraphInput.encode ⟨N+1,G⟩) out [] (unary (N+1)) G.bits [] [])
      (state (GraphInput.encode ⟨N+1,G⟩) out (unary (N+1)) [] (G.bits.drop (N+1)) []
        (encodeBitList (List.ofFn (weightWord G))).reverse) t ∧
      t≤(N+1)*(bodyBound (GraphInput.encode ⟨N+1,G⟩).length+2)+1 := by
  obtain ⟨t,ht,hb⟩ := loop_execution g G (N+1) 0 (by omega) out (G.bits.drop (N+1)) []
  have he : candidates 0 (N+1) (by omega)=id := by funext i;apply Fin.ext;simp [candidates]
  refine ⟨t,?_,hb⟩
  apply whilePop_executes
  simp only [he,Function.id_def,List.append_nil,Nat.zero_add] at ht
  rw [←firstRow G] at ht
  exact ht

end HiddenCircuits.ExactSampling.Runtime.WeightCompiler
