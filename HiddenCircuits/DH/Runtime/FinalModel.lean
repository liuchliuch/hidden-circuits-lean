import HiddenCircuits.DH.Runtime.NumericStateModel

/-! Actual cached-table output and the ordinary-graph correctness target for
the slower literal binary implementation. -/
namespace HiddenCircuits.DH.Runtime.NumericStateModel
open PruningModel ModuleExecution

 def result {n : ℕ} (s : State n) : ℕ :=
  ((List.finRange n).map (fun v=>if s.alive[v.val] then CoefficientModel.read s.rows[v.val] 0 else 1)).prod

 def rootProduct {n : ℕ} (s : ModuleExecution.Store n) : ℕ :=
  (((List.finRange n).filter (fun v=>s.alive[v.val])).map (fun v=>s.bags[v.val].state 0)).prod

 lemma prod_select {α : Type*} (xs : List α) (p : α→Bool) (f : α→ℕ) :
    (xs.map (fun x=>if p x then f x else 1)).prod=((xs.filter p).map f).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp,ih]

 lemma result_of_represents {n : ℕ} (s : State n) (bags : ModuleExecution.Store n) (h : Represents s bags) :
    result s=rootProduct bags := by
  unfold result rootProduct
  rw [prod_select,h.1]
  congr 1
  apply List.map_congr_left
  intro v hv
  exact h.2.2 v 0

 lemma forest_execute_value (es : List BagExpr) :
    (BagForest.execute es).value=(((es.map (fun e=>e.state 0)).prod : ℕ):ℤ) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change ArrayColumn.read e.execute.value 0*(BagForest.execute es).value=( _ :ℕ)
    rw [BagExpr.execute_state,ih,List.map_cons,List.prod_cons,Nat.cast_mul]

 lemma disjointTree_zero {n : ℕ} (bags : Vector BagExpr n) (first : Fin n) (rest : List (Fin n)) :
    ((disjointTree first rest).value.substitute (fun v=>bags[v.val])).state 0=
      (((first::rest).map (fun v=>bags[v.val].state 0)).prod) := by
  induction rest generalizing first with
  | nil => simp [disjointTree,LabeledCographTree.substitute]
  | cons v vs ih =>
    change (∑i : Fin 1, bags[first.val].state i.val *
      ((disjointTree v vs).value.substitute (fun v=>bags[v.val])).state (0-i.val))=_
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero,Nat.sub_zero,ih,List.map_cons,List.prod_cons]

 lemma finish_value {n : ℕ} (s : ModuleExecution.Store n) :
    (BagForest.execute (finish s).value).value=(rootProduct s : ℤ) := by
  let roots := (collectLive s.alive (List.finRange n)).value
  have hroot : rootProduct s=(roots.map (fun v=>s.bags[v.val].state 0)).prod := by
    simp only [roots,rootProduct,collectLive_value]
  rw [hroot,forest_execute_value]
  cases he : roots with
  | nil =>
    have hroots : (collectLive s.alive (List.finRange n)).value=[] := he
    simp only [finish,hroots,he,List.map_nil,List.prod_nil]
  | cons v vs =>
    have hroots : (collectLive s.alive (List.finRange n)).value=v::vs := he
    simp only [finish,hroots,he,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
      substituteArray_expression,disjointTree_zero]

/-- A pure cached-table program, with no bag/pruning witness supplied as input.
Its finite bit-stack refinement is the remaining operational layer. -/
 def count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ :=
  result (execute (PruningModel.run G n (Vector.replicate n true)).actions (initial n))

 theorem count_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : DistanceHereditaryGraph G) : count G=perfectMatchingCount G := by
  let plan := PruningModel.run G n (Vector.replicate n true)
  let bags := executeActions plan.actions (ModuleExecution.initial n)
  let numeric := execute plan.actions (initial n)
  have ht := run_trace G n (Vector.replicate n true)
  obtain ⟨ha,⟨I⟩⟩ := ht.executeActions (ModuleExecution.initial n) rfl (ModuleExecution.initialInterpretation G)
  have hn := trace_represents ht (ModuleExecution.initial n) rfl (ModuleExecution.initialInterpretation G)
    (initial n) (initial_represents n)
  have hedges := run_edgeless G hG n (Vector.replicate n true) (liveCount_le _)
  have he : ∀u v : ModuleExecution.Live bags, ¬(ModuleExecution.liveGraph G bags).Adj u v := by
    intro u v huv
    exact hedges ⟨u.val,ha ▸ u.property⟩ ⟨v.val,ha ▸ v.property⟩ huv
  have hpm := I.finish_execution_spec he |>.2.1
  rw [finish_value] at hpm
  have hresult : result numeric=rootProduct bags := result_of_represents numeric bags hn
  have heq : rootProduct bags=perfectMatchingCount G := by exact_mod_cast hpm
  exact hresult.trans heq

end HiddenCircuits.DH.Runtime.NumericStateModel
