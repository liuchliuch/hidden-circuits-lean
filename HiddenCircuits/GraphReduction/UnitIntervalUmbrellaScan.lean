import HiddenCircuits.GraphReduction.UnitIntervalListOrder

/-! Tail-structural umbrella checking for the physical reversed label array.
The checker has precisely three bounded nested list scans. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalUmbrellaScan
open UnitIntervalOrder
variable {V : Type*}

def inner (edge : V → V → Bool) (u v : V) (tail : List V) : Bool :=
  tail.all (fun w => !(edge u w) || (edge u v && edge v w))
def middle (edge : V → V → Bool) (u : V) : List V → Bool
  | [] => true
  | v::vs => inner edge u v vs && middle edge u vs
def umbrella (edge : V → V → Bool) : List V → Bool
  | [] => true
  | u::us => middle edge u us && umbrella edge us

/-- The equivalent order-free sublist formulation is useful for reversing lists. -/
def Triples (G : SimpleGraph V) (xs : List V) : Prop :=
  ∀ u v w, [u,v,w].Sublist xs → G.Adj u w → G.Adj u v ∧ G.Adj v w

lemma triples_cons (G : SimpleGraph V) (u : V) (xs : List V) :
    Triples G (u::xs) ↔
      xs.Pairwise (fun v w => G.Adj u w → G.Adj u v ∧ G.Adj v w) ∧ Triples G xs := by
  constructor
  · intro h
    constructor
    · apply List.pairwise_iff_forall_sublist.mpr
      intro v w hvw
      exact h u v w (hvw.cons₂ u)
    · intro v w z hsub
      exact h v w z (hsub.cons u)
  · rintro ⟨hp,ht⟩ v w z hsub
    cases hsub with
    | cons _ hsub => exact ht v w z hsub
    | cons₂ _ hsub => exact (List.pairwise_iff_forall_sublist.mp hp) hsub

lemma inner_graph_iff (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (xs : List V) :
    inner (fun a b => decide (G.Adj a b)) u v xs = true ↔
      ∀ w ∈ xs, G.Adj u w → G.Adj u v ∧ G.Adj v w := by
  simp only [inner,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true,decide_eq_false_iff_not,
    Bool.and_eq_true,decide_eq_true_eq]
  apply forall_congr'
  intro w
  apply forall_congr'
  intro _
  by_cases h : G.Adj u w <;> simp [h]

lemma middle_graph_iff (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (xs : List V) :
    middle (fun a b => decide (G.Adj a b)) u xs = true ↔
      xs.Pairwise (fun v w => G.Adj u w → G.Adj u v ∧ G.Adj v w) := by
  induction xs with
  | nil => simp [middle]
  | cons v vs ih => simp only [middle,Bool.and_eq_true,inner_graph_iff,ih,List.pairwise_cons]

lemma umbrella_triples (G : SimpleGraph V) [DecidableRel G.Adj] (xs : List V) :
    umbrella (fun a b => decide (G.Adj a b)) xs = true ↔ Triples G xs := by
  induction xs with
  | nil => simp [umbrella,Triples]
  | cons u us ih => simp only [umbrella,Bool.and_eq_true,middle_graph_iff,ih,triples_cons]

/-- Structural triple positions and finite increasing index triples coincide,
without a distinct-label assumption. -/
theorem triples_iff_listUmbrella (G : SimpleGraph V) (xs : List V) : Triples G xs ↔ ListUmbrella G xs := by
  constructor
  · intro h i j k hij hjk hik
    apply h (xs.get i) (xs.get j) (xs.get k) _ hik
    have hp : ([i,j,k] : List (Fin xs.length)).Pairwise (· < ·) := by
      simp [List.pairwise_cons,hij,hjk,lt_trans hij hjk]
    simpa only [List.map_cons,List.map_nil,List.get_eq_getElem] using List.map_getElem_sublist hp
  · intro h u v w hsub huw
    obtain ⟨is,he,hp⟩ := List.sublist_eq_map_getElem hsub
    cases is with
    | nil => simp at he
    | cons i is =>
      cases is with
      | nil => simp at he
      | cons j is =>
        cases is with
        | nil => simp at he
        | cons k rest =>
          have hr : rest = [] := by
            have hl := congrArg List.length he
            simp only [List.length_cons,List.length_nil,List.length_map] at hl
            exact List.length_eq_zero_iff.mp (by omega)
          subst rest
          simp only [List.map_cons,List.map_nil,List.cons.injEq,and_true] at he
          obtain ⟨rfl,rfl,rfl⟩ := he
          have hij : i<j := (List.pairwise_cons.mp hp).1 j (by simp)
          have hjk : j<k := (List.pairwise_cons.mp (List.pairwise_cons.mp hp).2).1 k (by simp)
          exact h i j k hij hjk huw

/-- The exact tail-recursive Boolean checker tests the verified umbrella predicate. -/
theorem umbrella_correct (G : SimpleGraph V) [DecidableRel G.Adj] (xs : List V) :
    umbrella (fun a b => decide (G.Adj a b)) xs = true ↔ ListUmbrella G xs :=
  (umbrella_triples G xs).trans (triples_iff_listUmbrella G xs)

lemma triples_reverse (G : SimpleGraph V) (xs : List V) (h : Triples G xs) : Triples G xs.reverse := by
  intro u v w hsub huw
  have hs : [w,v,u].Sublist xs := by simpa using hsub.reverse
  obtain ⟨hwv,hvu⟩ := h w v u hs huw.symm
  exact ⟨hvu.symm,hwv.symm⟩

/-- Reversal preserves umbrella orders for ordinary undirected graphs. -/
theorem listUmbrella_reverse_iff (G : SimpleGraph V) (xs : List V) :
    ListUmbrella G xs.reverse ↔ ListUmbrella G xs := by
  rw [←triples_iff_listUmbrella,←triples_iff_listUmbrella]
  constructor
  · intro h; simpa using triples_reverse G xs.reverse h
  · exact triples_reverse G xs

/-- The runtime may check the reversed stored label array directly. -/
theorem umbrella_reverse_correct (G : SimpleGraph V) [DecidableRel G.Adj] (xs : List V) :
    umbrella (fun a b => decide (G.Adj a b)) xs.reverse = true ↔ ListUmbrella G xs :=
  (umbrella_correct G xs.reverse).trans (listUmbrella_reverse_iff G xs)

theorem umbrella_reverse (G : SimpleGraph V) [DecidableRel G.Adj] (xs : List V) :
    umbrella (fun a b => decide (G.Adj a b)) xs.reverse = umbrella (fun a b => decide (G.Adj a b)) xs := by
  apply Bool.eq_iff_iff.mpr
  rw [umbrella_reverse_correct,umbrella_correct]

end HiddenCircuits.GraphReduction.UnitIntervalUmbrellaScan
