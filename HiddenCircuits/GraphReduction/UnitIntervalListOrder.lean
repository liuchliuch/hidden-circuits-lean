import HiddenCircuits.GraphReduction.UnitIntervalOrdering
import Mathlib.Data.List.NodupEquivFin

/-! Executable umbrella tests on literal vertex lists, and their semantic
meaning. The final list test needs no supplied representation. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalOrder
variable {V : Type*} {G : SimpleGraph V}

def ListUmbrella (G : SimpleGraph V) (ls : List V) : Prop := Umbrella (G.comap ls.get)

instance listUmbrellaDecidable [DecidableRel G.Adj] (ls : List V) : Decidable (ListUmbrella G ls) :=
  inferInstanceAs (Decidable (∀ i j k : Fin ls.length,
    i < j → j < k → G.Adj (ls.get i) (ls.get k) →
      G.Adj (ls.get i) (ls.get j) ∧ G.Adj (ls.get j) (ls.get k)))

lemma listUmbrella_of_sorted (r : RealUnitInterval.Representation G) (ls : List V)
    (hn : ls.Nodup) (hs : ls.Pairwise (fun v w => r.left v ≤ r.left w)) : ListUmbrella G ls := by
  have hm : Monotone (fun i : Fin ls.length => r.left (ls.get i)) := by
    intro i j hij
    rcases eq_or_lt_of_le hij with he|he
    · subst j; exact le_refl _
    · exact (List.pairwise_iff_getElem.mp hs) i.val j.val i.isLt j.isLt he
  apply umbrella_of_monotone_endpoints (fun i => r.left (ls.get i))
    (fun i => r.left (ls.get i)+r.length) hm
  · intro i j hij; have := hm hij; linarith
  · intro i; linarith [r.positive]
  · intro i j
    change G.Adj (ls.get i) (ls.get j) ↔ _
    rw [r.adjacency,RealUnitInterval.icc_overlap (by linarith [r.positive]) (by linarith [r.positive])]
    simp only [ne_eq,hn.get_inj_iff]

noncomputable def representationOfList [DecidableEq V] (G : SimpleGraph V) (ls : List V)
    (hn : ls.Nodup) (hc : ∀ v, v ∈ ls) (hu : ListUmbrella G ls) : UnitInterval.Representation G := by
  let e := hn.getEquivOfForallMemList ls hc
  let r := (exists_strictModel ls.length (G.comap ls.get) hu).some.representation
  refine { length := r.length, positive := r.positive, left := fun v => r.left (e.symm v), adjacency := ?_ }
  intro v w
  have he : ∀ i, e i = ls.get i := fun _ => rfl
  have hv : ls.get (e.symm v) = v := by rw [←he]; exact e.apply_symm_apply v
  have hw : ls.get (e.symm w) = w := by rw [←he]; exact e.apply_symm_apply w
  simpa only [SimpleGraph.comap_adj,hv,hw,ne_eq,e.symm.injective.eq_iff]
    using r.adjacency (e.symm v) (e.symm w)

def checkList [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (ls : List V) : Bool :=
  decide (ls.Nodup ∧ (∀ v, v ∈ ls) ∧ ListUmbrella G ls)

theorem checkList_sound [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (ls : List V) (h : checkList G ls = true) : RealUnitInterval.UnitIntervalGraph G := by
  obtain ⟨hn,hc,hu⟩ := of_decide_eq_true h
  exact ⟨(representationOfList G ls hn hc hu).toReal⟩

end HiddenCircuits.GraphReduction.UnitIntervalOrder

namespace HiddenCircuits.GraphReduction.UnitIntervalOrder
variable {V : Type*} {G : SimpleGraph V}

lemma listUmbrella_append (xs ys : List V) (hx : ListUmbrella G xs) (hy : ListUmbrella G ys)
    (hcross : ∀ x ∈ xs, ∀ y ∈ ys, ¬G.Adj x y) : ListUmbrella G (xs++ys) := by
  intro i j k hij hjk hik
  by_cases hk : k.val < xs.length
  · have hi : i.val < xs.length := by omega
    have hj : j.val < xs.length := by omega
    have he : G.Adj (xs.get ⟨i.val,hi⟩) (xs.get ⟨k.val,hk⟩) := by
      simpa only [SimpleGraph.comap_adj,List.get_eq_getElem,List.getElem_append_left hi,
        List.getElem_append_left hk] using hik
    have hh := hx ⟨i.val,hi⟩ ⟨j.val,hj⟩ ⟨k.val,hk⟩ hij hjk he
    simpa only [SimpleGraph.comap_adj,List.get_eq_getElem,List.getElem_append_left hi,
      List.getElem_append_left hj,List.getElem_append_left hk] using hh
  · by_cases hi : i.val < xs.length
    · have hky : k.val-xs.length < ys.length := by have := k.isLt; simp only [List.length_append] at this; omega
      have he : G.Adj (xs.get ⟨i.val,hi⟩) (ys.get ⟨k.val-xs.length,hky⟩) := by
        simpa only [SimpleGraph.comap_adj,List.get_eq_getElem,List.getElem_append_left hi,
          List.getElem_append_right (Nat.le_of_not_lt hk)] using hik
      exact (hcross _ (List.get_mem _ _) _ (List.get_mem _ _) he).elim
    · have hj : ¬j.val < xs.length := by omega
      have hiy : i.val-xs.length < ys.length := by have := i.isLt; simp only [List.length_append] at this; omega
      have hjy : j.val-xs.length < ys.length := by have := j.isLt; simp only [List.length_append] at this; omega
      have hky : k.val-xs.length < ys.length := by have := k.isLt; simp only [List.length_append] at this; omega
      have he : G.Adj (ys.get ⟨i.val-xs.length,hiy⟩) (ys.get ⟨k.val-xs.length,hky⟩) := by
        simpa only [SimpleGraph.comap_adj,List.get_eq_getElem,
          List.getElem_append_right (Nat.le_of_not_lt hi),List.getElem_append_right (Nat.le_of_not_lt hk)] using hik
      have hh := hy ⟨i.val-xs.length,hiy⟩ ⟨j.val-xs.length,hjy⟩ ⟨k.val-xs.length,hky⟩
        (by change i.val-xs.length < j.val-xs.length; omega)
        (by change j.val-xs.length < k.val-xs.length; omega) he
      simpa only [SimpleGraph.comap_adj,List.get_eq_getElem,
        List.getElem_append_right (Nat.le_of_not_lt hi),List.getElem_append_right (Nat.le_of_not_lt hj),
        List.getElem_append_right (Nat.le_of_not_lt hk)] using hh

lemma listUmbrella_map {W : Type*} (f : W → V) (ls : List W)
    (h : ListUmbrella (G.comap f) ls) : ListUmbrella G (ls.map f) := by
  intro i j k hij hjk hik
  have hi : i.val < ls.length := by simpa using i.isLt
  have hj : j.val < ls.length := by simpa using j.isLt
  have hk : k.val < ls.length := by simpa using k.isLt
  have he : (G.comap f).Adj (ls.get ⟨i.val,hi⟩) (ls.get ⟨k.val,hk⟩) := by
    simpa only [SimpleGraph.comap_adj,List.get_eq_getElem,List.getElem_map] using hik
  have hh := h ⟨i.val,hi⟩ ⟨j.val,hj⟩ ⟨k.val,hk⟩ hij hjk he
  simpa only [SimpleGraph.comap_adj,List.get_eq_getElem,List.getElem_map] using hh

end HiddenCircuits.GraphReduction.UnitIntervalOrder
