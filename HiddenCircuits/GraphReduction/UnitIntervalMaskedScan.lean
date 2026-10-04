import HiddenCircuits.GraphReduction.UnitIntervalGreedyRun

/-! Fixed-label alive-mask refinement of the semantic induced-graph scan.
All runtime data stays in the original vertex type: alive, selected, remaining,
and the emitted label list. Counts inspect the ordinary original adjacency. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalMaskedScan
open UnitIntervalGreedy
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

def induced (A : Finset V) : SimpleGraph {v // v ∈ A} := G.comap Subtype.val

instance induced_decidable (A : Finset V) : DecidableRel (induced G A).Adj :=
  fun _ _ => inferInstanceAs (Decidable (G.Adj _ _))

def lift (A : Finset V) (S : Finset {v // v ∈ A}) : Finset V :=
  S.map ⟨Subtype.val,Subtype.val_injective⟩

@[simp] lemma lift_card (A : Finset V) (S : Finset {v // v ∈ A}) : (lift A S).card = S.card := by
  simp [lift]
@[simp] lemma lift_univ (A : Finset V) : lift A Finset.univ = A := by
  ext v
  simp [lift]

lemma closedAdj_induce (A : Finset V) (x y : {v // v ∈ A}) :
    ClosedAdj (induced G A) x y ↔ ClosedAdj G x.val y.val := by
  change (x=y ∨ G.Adj x.val y.val) ↔ (x.val=y.val ∨ G.Adj x.val y.val)
  simp only [Subtype.ext_iff]

lemma lift_neighbors (A : Finset V) (S : Finset {v // v ∈ A}) (v : {v // v ∈ A}) :
    lift A (neighbors (induced G A) S v) = neighbors G (lift A S) v.val := by
  ext w
  simp only [lift,neighbors,Finset.mem_map,Finset.mem_filter,Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨u,⟨hu,ha⟩,rfl⟩
    exact ⟨⟨u,hu,rfl⟩,(closedAdj_induce G A v u).mp ha⟩
  · rintro ⟨⟨u,hu,rfl⟩,ha⟩
    exact ⟨u,⟨hu,(closedAdj_induce G A v u).mpr ha⟩,rfl⟩

lemma score_lift (A : Finset V) (S : Finset {v // v ∈ A}) (v : {v // v ∈ A}) :
    score G (lift A S) v.val = score (induced G A) S v := by
  unfold score
  rw [←lift_neighbors,lift_card]

lemma degree_lift (A : Finset V) (v : {v // v ∈ A}) :
    score G A v.val = degree (induced G A) v := by
  simpa only [lift_univ,degree] using score_lift G A Finset.univ v

/-- Degree is measured inside the current alive mask, not inside the original
whole graph. This is exactly the induced-residual selector. -/
def priority (A S : Finset V) (v : V) : ℕ :=
  (A.card+1)*score G S v + (A.card-score G A v)

def choose (A S R : Finset V) : Option V := (R.sort (· ≤ ·)).argmax (priority G A S)

lemma priority_lift (A : Finset V) (S : Finset {v // v ∈ A}) (v : {v // v ∈ A}) :
    priority G A (lift A S) v.val = UnitIntervalGreedy.priority (induced G A) S v := by
  simp only [priority,UnitIntervalGreedy.priority,score_lift,degree_lift,Fintype.card_coe]

lemma lift_sort (A : Finset V) (S : Finset {v // v ∈ A}) :
    (S.sort (· ≤ ·)).map Subtype.val = (lift A S).sort (· ≤ ·) := by
  exact Finset.map_sort ⟨Subtype.val,Subtype.val_injective⟩ S (· ≤ ·) (· ≤ ·)
    (fun _ _ _ _ => Iff.rfl)

private lemma argmax_map {α β : Type*} (f : α → β) (p : β → ℕ) (ls : List α) :
    (ls.map f).argmax p = (ls.argmax (p ∘ f)).map f := by
  induction ls with
  | nil => rfl
  | cons a ls ih =>
    rw [List.map_cons,List.argmax_cons,List.argmax_cons,ih]
    cases he : ls.argmax (p ∘ f) with
    | none => rfl
    | some b =>
      simp only [Option.map_some,Function.comp_apply]
      split <;> rfl

/-- Exact selected-label agreement, including deterministic tie breaking. -/
theorem choose_lift (A : Finset V) (S R : Finset {v // v ∈ A}) :
    choose G A (lift A S) (lift A R) =
      (UnitIntervalGreedy.choose (induced G A) S R).map Subtype.val := by
  rw [choose,←lift_sort,argmax_map]
  have he : priority G A (lift A S) ∘ Subtype.val =
      UnitIntervalGreedy.priority (induced G A) S := by
    funext v; exact priority_lift G A S v
  rw [he]
  rfl

/-- The whole scan stores only original labels and fixed-size masks. -/
def run (A : Finset V) : ℕ → List V → Finset V → List V × Finset V
  | 0,ls,R => (ls,R)
  | fuel+1,ls,R =>
    match choose G A ls.toFinset R with
    | none => (ls,R)
    | some y => if score G ls.toFinset y = 0 then (ls,R)
      else run A fuel (ls++[y]) (R.erase y)

lemma lift_toFinset (A : Finset V) (ls : List {v // v ∈ A}) :
    lift A ls.toFinset = (ls.map Subtype.val).toFinset := by
  ext v; simp [lift]

lemma lift_erase (A : Finset V) (S : Finset {v // v ∈ A}) (v : {v // v ∈ A}) :
    lift A (S.erase v) = (lift A S).erase v.val := by
  exact Finset.map_erase (⟨Subtype.val,Subtype.val_injective⟩ : {v // v ∈ A} ↪ V) S v

/-- Finite-mask scans are a semantic refinement of the already verified
induced-graph algorithm, for arbitrary fuel and arbitrary selected prefixes. -/
theorem run_lift (A : Finset V) (fuel : ℕ) (ls : List {v // v ∈ A}) (R : Finset {v // v ∈ A}) :
    run G A fuel (ls.map Subtype.val) (lift A R) =
      ((UnitIntervalGreedy.run (induced G A) fuel ls R).1.map Subtype.val,
        lift A (UnitIntervalGreedy.run (induced G A) fuel ls R).2) := by
  induction fuel generalizing ls R with
  | zero => rfl
  | succ fuel ih =>
    rw [run,←lift_toFinset,choose_lift,UnitIntervalGreedy.run]
    cases hy : UnitIntervalGreedy.choose (induced G A) ls.toFinset R with
    | none => rfl
    | some y =>
      simp only [Option.map_some]
      rw [score_lift]
      split
      · rfl
      · rw [←lift_erase]
        simpa only [List.map_append,List.map_cons,List.map_nil] using ih (ls++[y]) (R.erase y)

end HiddenCircuits.GraphReduction.UnitIntervalMaskedScan
