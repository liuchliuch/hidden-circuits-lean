import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidualGraph

/-! A fixed nineteen-stack, query-free dense pair-deletion emitter. Parsing,
mask construction, inherited-order enumeration, matrix lookup and cleanup are
all literal finite byte programs and charged in the stated polynomial. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidual
open Complexity OracleBlock Initialization

def graph {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1)) : MatrixGraph (retained j).card :=
  InducedGraphEmitter.graph G (ResidualGraphProgram.vertexMap (retained j))

def output {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1)) : BitString :=
  GraphInput.encode ⟨(retained j).card,graph G j⟩

def graphPorts : Fin 18 ↪ Fin 19 where
  toFun i := if i.val=0 then 2 else if i.val=1 then 3 else if i.val=2 then 4
    else if i.val=3 then 0 else ⟨i.val+1,by omega⟩
  inj' := by decide +kernel

noncomputable def emitGraph : OracleBlock 18 := ResidualGraphProgram.on graphPorts
noncomputable def cleanup : OracleBlock 18 := seq (clear 2) (seq (clear 3) (clear 4))
noncomputable def program : OracleBlock 18 := seq prepare (seq emitGraph cleanup)

lemma emitGraph_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1)) :
    ∃ t,emitGraph.Executes g
      (state [] (unary j.val) (N+1) G.bits (MaskEnumerationSemantics.mask (retained j)) [])
      (state (output G j) (unary j.val) (N+1) G.bits (MaskEnumerationSemantics.mask (retained j)) []) t ∧
      t≤ResidualGraphProgram.timeBound (N+1) (N+1) ((N+1)*(2*(N+1)+2)) := by
  obtain ⟨t,ht,hb⟩ := ResidualGraphProgram.on_executes graphPorts g
    (state [] (unary j.val) (N+1) G.bits (MaskEnumerationSemantics.mask (retained j)) []) G (retained j)
    (by funext r;fin_cases r <;> simp [state,graphPorts,ResidualGraphProgram.state])
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext r;fin_cases r <;> simp [state,graphPorts,output,graph,InducedGraphEmitter.graph,InducedGraphEmitter.induced,ResidualGraphProgram.vertexMap,ResidualTest.vertex]

lemma cleanup_executes (g : BitString → ℕ) (raw chosen : BitString) {N : ℕ}
    (G : MatrixGraph (N+1)) (j : Fin (N+1)) :
    cleanup.Executes g (state raw chosen (N+1) G.bits (MaskEnumerationSemantics.mask (retained j)) [])
      (inputStore raw chosen) ((N+1)*(N+1)+2*(N+1)+7) := by
  have h1 : (clear (2:Fin 19)).Executes g
      (state raw chosen (N+1) G.bits (MaskEnumerationSemantics.mask (retained j)) [])
      (state raw chosen 0 G.bits (MaskEnumerationSemantics.mask (retained j)) []) (N+1+1) := by
    convert clear_executes g (2:Fin 19)
      (state raw chosen (N+1) G.bits (MaskEnumerationSemantics.mask (retained j)) []) using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state]
  have h2 : (clear (3:Fin 19)).Executes g
      (state raw chosen 0 G.bits (MaskEnumerationSemantics.mask (retained j)) [])
      (state raw chosen 0 [] (MaskEnumerationSemantics.mask (retained j)) []) ((N+1)*(N+1)+1) := by
    convert clear_executes g (3:Fin 19)
      (state raw chosen 0 G.bits (MaskEnumerationSemantics.mask (retained j)) []) using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state]
  have h3 : (clear (4:Fin 19)).Executes g
      (state raw chosen 0 [] (MaskEnumerationSemantics.mask (retained j)) [])
      (inputStore raw chosen) (N+1+1) := by
    convert clear_executes g (4:Fin 19)
      (state raw chosen 0 [] (MaskEnumerationSemantics.mask (retained j)) []) using 1
    · funext r;fin_cases r <;> simp [state,inputStore]
    · simp [state,MaskEnumerationSemantics.mask]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1 <;> omega

/-- Explicit polynomial clock in the original number of graph vertices. -/
def timeBound (N : ℕ) : ℕ :=
  ResidualGraphProgram.timeBound N N (N*(2*N+2))+10*N*N+37*N+70

theorem program_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1)) :
    ∃ t,program.Executes g (inputStore (GraphInput.encode ⟨N+1,G⟩) (unary j.val))
      (inputStore (output G j) (unary j.val)) t ∧ t≤timeBound (N+1) := by
  obtain ⟨a,ha,hab⟩ := prepare_executes g G j
  obtain ⟨b,hb,hbb⟩ := emitGraph_executes g G j
  have hc := cleanup_executes g (output G j) (unary j.val) G j
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb hc),?_⟩
  unfold timeBound
  nlinarith

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ prepare_queryFree
  (seq_queryFree _ _ (ResidualGraphProgram.on_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))

noncomputable def programOn {k : ℕ} (φ : Fin 19 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem programOn_executes {k N : ℕ} (φ : Fin 19 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (G : MatrixGraph (N+1)) (j : Fin (N+1))
    (hs : s∘φ=inputStore (GraphInput.encode ⟨N+1,G⟩) (unary j.val)) :
    ∃ t,(programOn φ).Executes g s (Function.update s (φ 0) (output G j)) t ∧ t≤timeBound (N+1) := by
  obtain ⟨t,ht,hb⟩ := program_executes g G j
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · funext i
    have he := congrFun hs i
    fin_cases i <;> simp_all [Function.comp_def,Function.update_apply,φ.injective.eq_iff,inputStore,state]
  · intro i hi
    exact Function.update_of_ne (hi 0).symm _ _

lemma programOn_queryFree {k : ℕ} (φ : Fin 19 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidual
