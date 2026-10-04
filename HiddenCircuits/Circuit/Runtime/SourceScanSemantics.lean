import HiddenCircuits.Circuit.Runtime.GateEncoding

/-! Row-major adjacency scan semantics for the restoring source emitter. Each
actual matrix bit controls precisely one local restoring edge program. -/
namespace HiddenCircuits.Circuit.Runtime
open HiddenCircuits.Complexity

/-- Every ordered vertex pair occurs once, in literal row-major order. -/
def sourcePairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i,j)))

def edgeGates {n : ℕ} (G : MatrixGraph n) (i j : Fin n) : List (ConstraintGate n) :=
  if h : G.edge i j=true then (restoringEdgeProgram ⟨i,j,by
    intro he;subst j;simpa [G.loopless] using h⟩).gates else []

def edgeSwapPairs {n : ℕ} (G : MatrixGraph n) (i j : Fin n) : ℕ :=
  if h : G.edge i j=true then (edgeRouteIndices 1 (⟨i,j,by
    intro he;subst j;simpa [G.loopless] using h⟩ : SourceEdge n)).length else 0

lemma restoringEdges_gates {n : ℕ} (es : List (SourceEdge n)) :
    (restoringEdges es).gates=es.flatMap (fun e => (restoringEdgeProgram e).gates) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [restoringEdges,ConstraintProgram.compose,ih]

lemma orderedEdges_eq_filter_pairs {n : ℕ} (G : MatrixGraph n) :
    orderedEdges G=(sourcePairs n).filter (fun e => G.edge e.1 e.2) := by
  simp [orderedEdges,sourcePairs,List.filter_flatMap,List.filter_map,Function.comp_def]

lemma flatMap_filter_eq {α β : Type*} (xs : List α) (p : α → Bool) (f : α → List β) :
    (xs.filter p).flatMap f=xs.flatMap (fun a => if p a then f a else []) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h:p a <;> simp [h,ih]

lemma map_filter_sum_eq {α : Type*} (xs : List α) (p : α → Bool) (f : α → ℕ) :
    ((xs.filter p).map f).sum=(xs.map (fun a => if p a then f a else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h:p a <;> simp [h,ih]

/-- The scanned gate stream is exactly the previously proved source circuit,
including every original ordered edge and every reverse route. -/
theorem sourceScan_gates {n : ℕ} (G : MatrixGraph n) :
    (sourcePairs n).flatMap (fun e => edgeGates G e.1 e.2)=
      (restoringEdges (sourceEdges G)).gates := by
  rw [restoringEdges_gates]
  unfold sourceEdges
  rw [List.flatMap_map]
  have he : (orderedEdges G).attach.flatMap (fun e => (restoringEdgeProgram
        ⟨e.val.1,e.val.2,orderedEdges_ne G _ _ e.property⟩).gates) =
      (orderedEdges G).flatMap (fun e => edgeGates G e.1 e.2) := by
    calc
      _ = (orderedEdges G).attach.flatMap (fun e => edgeGates G e.val.1 e.val.2) := by
        apply List.flatMap_congr
        intro e he
        simp only [edgeGates,dif_pos ((orderedEdges_mem G e.val).mp e.property)]
      _ = _ := by
        have hmap := List.attach_map_subtype_val (orderedEdges G)
        have hh := congrArg (fun es : List (Fin n × Fin n) => es.flatMap (fun e => edgeGates G e.1 e.2)) hmap
        simpa only [List.flatMap_map,Function.comp_def] using hh
  rw [he,orderedEdges_eq_filter_pairs,flatMap_filter_eq]
  apply List.flatMap_congr
  intro e he
  by_cases hh : G.edge e.1 e.2=true
  · simp [hh]
  · simp [edgeGates,hh]

theorem sourceScan_swaps {n : ℕ} (G : MatrixGraph n) :
    ((sourcePairs n).map (fun e => edgeSwapPairs G e.1 e.2)).sum=restoringSwapPairs (sourceEdges G) := by
  unfold restoringSwapPairs sourceEdges
  rw [List.map_map]
  simp only [Function.comp_def]
  have he : (orderedEdges G).attach.map (fun e => (edgeRouteIndices 1
        (⟨e.val.1,e.val.2,orderedEdges_ne G _ _ e.property⟩ : SourceEdge n)).length) =
      (orderedEdges G).map (fun e => edgeSwapPairs G e.1 e.2) := by
    calc
      _ = (orderedEdges G).attach.map (fun e => edgeSwapPairs G e.val.1 e.val.2) := by
        apply List.map_congr_left
        intro e he
        simp only [edgeSwapPairs,dif_pos ((orderedEdges_mem G e.val).mp e.property)]
      _ = _ := List.attach_map_val (l := orderedEdges G) (f := fun e : Fin n × Fin n => edgeSwapPairs G e.1 e.2)
  rw [he,orderedEdges_eq_filter_pairs,map_filter_sum_eq]
  congr 1
  apply List.map_congr_left
  intro e he
  by_cases hh : G.edge e.1 e.2=true
  · simp [hh]
  · simp [edgeSwapPairs,hh]

end HiddenCircuits.Circuit.Runtime
