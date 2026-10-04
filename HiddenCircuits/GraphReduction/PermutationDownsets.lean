import HiddenCircuits.GraphReduction.NestedDownsetIntervals
import HiddenCircuits.GraphReduction.IntervalChordal

/-! A chordal permutation diagram has nested downsets in its two-coordinate
order: two incomparable downsets would produce an actual induced four-cycle. -/
namespace HiddenCircuits.GraphReduction

lemma Chordal.no_induced_four {V : Type*} {G : SimpleGraph V} (hG : Chordal G)
    (a b c d : V) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : ¬G.Adj a c) (hbd : ¬G.Adj b d) (hneac : a≠c) (hnebd : b≠d) : False := by
  have hba := G.adj_symm hab
  have hcb := G.adj_symm hbc
  have hdc := G.adj_symm hcd
  have had := G.adj_symm hda
  have hca : ¬G.Adj c a := by simpa only [G.adj_comm] using hac
  have hdb : ¬G.Adj d b := by simpa only [G.adj_comm] using hbd
  have hnab := hab.ne
  have hnbc := hbc.ne
  have hncd := hcd.ne
  have hnda := hda.ne
  let f : Fin 4 → V := ![a,b,c,d]
  apply (hG 4 (by decide)).false
  refine { toFun := f, inj' := ?_, map_rel_iff' := ?_ }
  · intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [f,eq_comm]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [f,SimpleGraph.cycleGraph_adj',sub_val_explicit]
    all_goals decide +kernel

namespace PermutationDiagram
variable {V : Type*} (D : PermutationDiagram V)

/-- The strict two-coordinate order whose incomparability graph is the diagram. -/
def below (x y : V) : Prop := D.upper x < D.upper y ∧ D.lower x < D.lower y
instance below_decidable : DecidableRel D.below := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
lemma below_irrefl (x : V) : ¬D.below x x := by simp [below]
lemma below_trans {x y z : V} (hxy : D.below x y) (hyz : D.below y z) : D.below x z :=
  ⟨hxy.1.trans hyz.1,hxy.2.trans hyz.2⟩
lemma below_ne {x y : V} (hxy : D.below x y) : x≠y := by
  intro he
  subst y
  exact D.below_irrefl x hxy

lemma adj_iff_incomparable (x y : V) :
    D.graph.Adj x y ↔ x≠y ∧ ¬D.below x y ∧ ¬D.below y x := by
  by_cases he : x=y
  · subst y
    simp [below]
  have hu : D.upper x≠D.upper y := fun h => he (D.upper.injective h)
  have hl : D.lower x≠D.lower y := fun h => he (D.lower.injective h)
  change (_ ∧ _) ∨ (_ ∧ _) ↔ _
  simp only [below,he,ne_eq,not_false_eq_true,true_and] at *
  omega

/-- No chosen elimination order is needed for this full-graph characterization. -/
theorem nestedDownsets (hG : Chordal D.graph) : Interval.NestedDownsets D.below := by
  intro x y
  by_contra hn
  simp only [not_or,not_forall,_root_.not_imp] at hn
  obtain ⟨⟨a,hax,hnay⟩,⟨b,hby,hnbx⟩⟩ := hn
  have hnab : ¬D.below a b := fun h => hnay (D.below_trans h hby)
  have hnba : ¬D.below b a := fun h => hnbx (D.below_trans h hax)
  have hnxy : ¬D.below x y := fun h => hnay (D.below_trans hax h)
  have hnyx : ¬D.below y x := fun h => hnbx (D.below_trans hby h)
  have hnxb : ¬D.below x b := fun h => hnay (D.below_trans hax (D.below_trans h hby))
  have hnya : ¬D.below y a := fun h => hnbx (D.below_trans hby (D.below_trans h hax))
  have hab : D.graph.Adj a b := (D.adj_iff_incomparable a b).mpr
    ⟨by intro he; rw [he] at hax; exact hnbx hax,hnab,hnba⟩
  have hbx : D.graph.Adj b x := (D.adj_iff_incomparable b x).mpr
    ⟨by intro he; rw [he] at hby; exact hnxy hby,hnbx,hnxb⟩
  have hxy : D.graph.Adj x y := (D.adj_iff_incomparable x y).mpr
    ⟨by intro he; rw [he] at hax; exact hnay hax,hnxy,hnyx⟩
  have hya : D.graph.Adj y a := (D.adj_iff_incomparable y a).mpr
    ⟨by intro he; rw [he] at hby; exact hnba hby,hnya,hnay⟩
  have hnax : ¬D.graph.Adj a x := fun h => ((D.adj_iff_incomparable a x).mp h).2.1 hax
  have hnby : ¬D.graph.Adj b y := fun h => ((D.adj_iff_incomparable b y).mp h).2.1 hby
  exact hG.no_induced_four a b x y hab hbx hxy hya hnax hnby (D.below_ne hax) (D.below_ne hby)

end PermutationDiagram
end HiddenCircuits.GraphReduction
