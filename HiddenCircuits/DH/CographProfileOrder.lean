import HiddenCircuits.DH.CographStaircase

/-! Instantiation of the alternating staircase by literal graph profile classes. -/
namespace HiddenCircuits.DH
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma pivotProfile_equal_adj {r x y z : V}
    (he : pivotProfile G r x = pivotProfile G r y) (hz : G.Adj r z) :
    G.Adj x z ↔ G.Adj y z := by
  have h := Set.ext_iff.mp he z
  change (G.Adj r z ∧ G.Adj x z) ↔ (G.Adj r z ∧ G.Adj y z) at h
  exact ⟨fun hx => (h.mp ⟨hz,hx⟩).2,fun hy => (h.mpr ⟨hz,hy⟩).2⟩

lemma complement_pivotProfile_equal_adj {r x y a : V}
    (he : pivotProfile Gᶜ r x = pivotProfile Gᶜ r y)
    (hx : G.Adj r x) (hy : G.Adj r y) (ha : a∈nonneighbors G r) :
    G.Adj a x ↔ G.Adj a y := by
  have hra : Gᶜ.Adj r a := (G.compl_adj _ _).mpr ⟨ha.1.symm,ha.2⟩
  have h := pivotProfile_equal_adj he hra
  have hxa : x≠a := fun he => ha.2 (he ▸ hx)
  have hya : y≠a := fun he => ha.2 (he ▸ hy)
  constructor
  · intro hax
    by_contra hay
    have hya' : Gᶜ.Adj y a := (G.compl_adj _ _).mpr ⟨hya,fun he => hay he.symm⟩
    exact ((G.compl_adj _ _).mp (h.mpr hya')).2 hax.symm
  · intro hay
    by_contra hax
    have hxa' : Gᶜ.Adj x a := (G.compl_adj _ _).mpr ⟨hxa,fun he => hax he.symm⟩
    exact ((G.compl_adj _ _).mp (h.mp hxa')).2 hay.symm

/-- A strict list of normal profile classes becomes strictly decreasing rows on
any complete choice of complementary class representatives. -/
theorem pivotProfiles_rows (r : V) (as bs : List V)
    (ha : ∀a∈as, a∈nonneighbors G r) (hb : ∀b∈bs, G.Adj r b)
    (hcover : ∀z, G.Adj r z → ∃b∈bs, pivotProfile Gᶜ r z = pivotProfile Gᶜ r b)
    (horder : as.Pairwise (fun a a' => pivotProfile G r a' ⊂ pivotProfile G r a)) :
    CographStaircase.Rows G.Adj as bs := by
  apply horder.imp_of_mem
  intro a a' ham ham' h
  refine ⟨?_,?_⟩
  · intro b hbm hab
    exact (h.le ⟨hb b hbm,hab⟩).2
  · obtain ⟨z,hza,hza'⟩ := Set.exists_of_ssubset h
    obtain ⟨b,hbm,he⟩ := hcover z hza.1
    have hba := complement_pivotProfile_equal_adj he hza.1 (hb b hbm) (ha a ham)
    have hba' := complement_pivotProfile_equal_adj he hza.1 (hb b hbm) (ha a' ham')
    exact ⟨b,hbm,hba.mp hza.2,fun hh => hza' ⟨hza.1,hba'.mpr hh⟩⟩

/-- Complementary profile order is exactly strict increase of the corresponding
original-graph columns. -/
theorem pivotProfiles_cols (r : V) (as bs : List V)
    (ha : ∀a∈as, a∈nonneighbors G r) (hb : ∀b∈bs, G.Adj r b)
    (hcover : ∀z∈nonneighbors G r, ∃a∈as, pivotProfile G r z = pivotProfile G r a)
    (horder : bs.Pairwise (fun b b' => pivotProfile Gᶜ r b' ⊂ pivotProfile Gᶜ r b)) :
    CographStaircase.Cols G.Adj as bs := by
  apply horder.imp_of_mem
  intro b b' hbm hbm' h
  refine ⟨?_,?_⟩
  · intro a ham hab
    by_contra hab'
    have haN := ha a ham
    have hrac : Gᶜ.Adj r a := (G.compl_adj _ _).mpr ⟨haN.1.symm,haN.2⟩
    have hb'ac : Gᶜ.Adj b' a := (G.compl_adj _ _).mpr
      ⟨fun he => haN.2 (he ▸ hb b' hbm'),fun he => hab' he.symm⟩
    exact ((G.compl_adj _ _).mp (h.le ⟨hrac,hb'ac⟩).2).2 hab.symm
  · obtain ⟨z,hzb,hzb'⟩ := Set.exists_of_ssubset h
    have hz : z∈nonneighbors G r :=
      ⟨((G.compl_adj _ _).mp hzb.1).1.symm,((G.compl_adj _ _).mp hzb.1).2⟩
    have hzbEdge : ¬G.Adj z b := fun he => ((G.compl_adj _ _).mp hzb.2).2 he.symm
    have hzb'Edge : G.Adj z b' := by
      by_contra hnot
      apply hzb'
      exact ⟨hzb.1,(G.compl_adj _ _).mpr
        ⟨fun he => hz.2 (he ▸ hb b' hbm'),fun he => hnot he.symm⟩⟩
    obtain ⟨a,ham,he⟩ := hcover z hz
    have hbEq := pivotProfile_equal_adj he (hb b hbm)
    have hb'Eq := pivotProfile_equal_adj he (hb b' hbm')
    exact ⟨a,ham,hb'Eq.mp hzb'Edge,fun hh => hzbEdge (hbEq.mpr hh)⟩

/-- Actual graph profiles, listed once in descending inclusion, supply all
hypotheses of the linear alternating spine reconstruction. -/
theorem pivotProfiles_weave (r : V) (s : Bool) (as bs : List V)
    (ha : ∀a∈as, a∈nonneighbors G r) (hb : ∀b∈bs, G.Adj r b)
    (hcoverA : ∀z∈nonneighbors G r, ∃a∈as, pivotProfile G r z = pivotProfile G r a)
    (hcoverB : ∀z, G.Adj r z → ∃b∈bs, pivotProfile Gᶜ r z = pivotProfile Gᶜ r b)
    (horderA : as.Pairwise (fun a a' => pivotProfile G r a' ⊂ pivotProfile G r a))
    (horderB : bs.Pairwise (fun b b' => pivotProfile Gᶜ r b' ⊂ pivotProfile Gᶜ r b))
    (hhead : CographStaircase.HeadChoice G.Adj s as bs) :
    (CographStaircase.weave s as bs).Pairwise
      (fun x y => CographStaircase.cross G.Adj x y ↔ CographStaircase.joined y = true) :=
  CographStaircase.weave_spec G.Adj s as bs
    (pivotProfiles_rows r as bs ha hb hcoverB horderA)
    (pivotProfiles_cols r as bs ha hb hcoverA horderB) hhead

end HiddenCircuits.DH
