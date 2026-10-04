import HiddenCircuits.GraphReduction.UnitIntervalGreedyGeometry
import HiddenCircuits.GraphReduction.UnitIntervalListOrder

/-!
# Ordinary-graph unit-interval recognition

Try each labeled vertex as the start of the count-based greedy component scan.
Accept the first produced umbrella order, delete its closed component, and
repeat. The fuel is the original vertex count, so the algorithm never enumerates
permutations or takes an unbounded search. A separate binary-machine refinement
is needed before claiming the project's charged bit-time `PolyTime` endpoint.
-/
namespace HiddenCircuits.GraphReduction.UnitIntervalRecognition
open UnitIntervalGreedy UnitIntervalOrder

variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

def goodRoot : Option V :=
  (Finset.univ.sort (· ≤ ·)).find? (fun root => decide (ListUmbrella G (component G root)))

lemma goodRoot_spec {root : V} (h : goodRoot G = some root) :
    ListUmbrella G (component G root) := by
  unfold goodRoot at h
  have hh : decide (ListUmbrella G (component G root)) = true := List.find?_some (p := fun v : V => decide (ListUmbrella G (component G v))) h
  exact of_decide_eq_true hh

lemma goodRoot_exists (r : RealUnitInterval.Representation G) (hn : 0 < Fintype.card V) :
    ∃ root, goodRoot G = some root := by
  have hne : (Finset.univ : Finset V).Nonempty := Finset.card_pos.mp (by simpa using hn)
  obtain ⟨root,_,hmin⟩ := Finset.univ.exists_min_image r.left hne
  obtain ⟨r',hord⟩ := component_sorted r root (fun v => hmin v (Finset.mem_univ _))
  have hu := listUmbrella_of_sorted r' _ (component_nodup G root) hord
  cases he : goodRoot G with
  | some v => exact ⟨v,rfl⟩
  | none =>
    have hn := List.find?_eq_none.mp he root (by simp)
    exact (hn (by simpa using hu)).elim

/-- A concrete terminating recognizer; recursive calls use induced residual
vertex sets and their inherited ordinary adjacency relation. -/
def search (fuel : ℕ) {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Option (List V) :=
  match fuel with
  | 0 => if Fintype.card V = 0 then some [] else none
  | fuel+1 =>
    if Fintype.card V = 0 then some [] else
      match goodRoot G with
      | none => none
      | some root =>
        let ls := component G root
        (search fuel (G.induce {v | v ∉ ls})).map (fun rest => ls++rest.map Subtype.val)

/-- Recognition starts with enough fuel for every nonempty component. -/
def recognize (G : SimpleGraph V) [DecidableRel G.Adj] : Option (List V) := search (Fintype.card V) G

/-- A returned list is a bijective labeled umbrella order. -/
theorem search_sound : ∀ fuel {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ls : List V), search fuel G = some ls →
    ls.Nodup ∧ (∀ v, v ∈ ls) ∧ ListUmbrella G ls := by
  intro fuel
  induction fuel with
  | zero =>
    intro V _ _ G _ ls hs
    simp only [search] at hs
    split at hs
    · rename_i h0
      haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp h0
      cases hs
      exact ⟨by simp,fun v => isEmptyElim v,by intro i; exact Fin.elim0 i⟩
    · contradiction
  | succ fuel ih =>
    intro V _ _ G _ ls hs
    simp only [search] at hs
    split at hs
    · rename_i h0
      haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp h0
      cases hs
      exact ⟨by simp,fun v => isEmptyElim v,by intro i; exact Fin.elim0 i⟩
    · split at hs
      · contradiction
      · rename_i root hroot
        obtain ⟨rest,hrest,he⟩ := Option.map_eq_some_iff.mp hs
        subst ls
        obtain ⟨hn,hcover,hu⟩ := ih _ rest hrest
        refine ⟨?_,?_,?_⟩
        · rw [List.nodup_append]
          refine ⟨component_nodup G root,hn.map Subtype.val_injective,?_⟩
          intro a ha b hb hab
          obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hb
          exact b.property (hab ▸ ha)
        · intro v
          by_cases hv : v ∈ component G root
          · exact List.mem_append_left _ hv
          · exact List.mem_append_right _ (List.mem_map.mpr ⟨⟨v,hv⟩,hcover _,rfl⟩)
        · apply listUmbrella_append _ _ (goodRoot_spec G hroot) (listUmbrella_map Subtype.val _ hu)
          intro a ha b hb
          obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hb
          exact component_closed G root ha b.property

/-- Every real unit-interval graph is accepted. No order or recognition witness
is supplied to the algorithm: a leftmost root is used only in this proof. -/
theorem search_complete : ∀ fuel {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V ≤ fuel → RealUnitInterval.UnitIntervalGraph G → ∃ ls, search fuel G = some ls := by
  intro fuel
  induction fuel with
  | zero =>
    intro V _ _ G _ hn _
    have h0 : Fintype.card V = 0 := Nat.eq_zero_of_le_zero hn
    exact ⟨[],by simp [search,h0]⟩
  | succ fuel ih =>
    intro V _ _ G _ hn ⟨r⟩
    by_cases h0 : Fintype.card V = 0
    · exact ⟨[],by simp [search,h0]⟩
    · obtain ⟨root,hroot⟩ := goodRoot_exists G r (Nat.pos_of_ne_zero h0)
      have hc : Fintype.card {v : V // v ∉ component G root} < Fintype.card V :=
        Fintype.card_subtype_lt (not_not.mpr (component_root_mem G root))
      have hc' : Fintype.card ↑{v : V | v ∉ component G root} ≤ fuel := by
        change Fintype.card {v : V // v ∉ component G root} ≤ fuel
        omega
      obtain ⟨rest,hrest⟩ := ih (G.induce {v | v ∉ component G root}) hc'
        ⟨r.induce {v | v ∉ component G root}⟩
      exact ⟨component G root++rest.map Subtype.val,by simp [search,h0,hroot,hrest]⟩

/-- Total ordinary-graph recognition is exactly the natural real unit-interval
predicate, with empty, disconnected, coincident, and touching cases included. -/
theorem recognize_iff : (recognize G).isSome = true ↔ RealUnitInterval.UnitIntervalGraph G := by
  constructor
  · intro h
    obtain ⟨ls,he⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hn,hc,hu⟩ := search_sound (Fintype.card V) G ls he
    exact ⟨(representationOfList G ls hn hc hu).toReal⟩
  · intro h
    obtain ⟨ls,he⟩ := search_complete (Fintype.card V) G le_rfl h
    simp [recognize,he]

end HiddenCircuits.GraphReduction.UnitIntervalRecognition
