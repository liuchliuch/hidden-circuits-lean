import HiddenCircuits.DH.CographFamilySpec
import HiddenCircuits.DH.CographProfileOrder

/-! Relative module profile families give the strict staircase matrix. External
vertices cannot witness a profile difference because the module cut is uniform. -/
namespace HiddenCircuits.DH
open SimpleGraph CographStaircase
variable {V : Type*} {G : SimpleGraph V}

lemma ProfileFamily.original_neighbors {M : Set V} {r : V} {bs : List V}
    (h : ProfileFamily Gᶜ M r bs) : ∀b∈bs, G.Adj r b := by
  intro b hb
  have he := (h.members b hb).2
  rwa [nonneighbors_compl] at he

theorem ProfileFamily.matrix_rows {M : Set V} {r : V} {as bs : List V}
    (hM : GraphModule G M) (ha : ProfileFamily G M r as) (hb : ProfileFamily Gᶜ M r bs)
    (horder : as.Pairwise (fun a a' => pivotProfile G r a' ⊂ pivotProfile G r a)) :
    Rows G.Adj as bs := by
  apply horder.imp_of_mem
  intro a a' ham ham' h
  refine ⟨?_,?_⟩
  · intro b hbm hab
    exact (h.le ⟨hb.original_neighbors b hbm,hab⟩).2
  · obtain ⟨z,hza,hza'⟩ := Set.exists_of_ssubset h
    have hzM : z∈M := by
      by_contra hz
      exact hza' ⟨hza.1,(hM a (ha.members a ham).1 a' (ha.members a' ham').1 z hz).mp hza.2⟩
    have hzN : z∈nonneighbors Gᶜ r := by rw [nonneighbors_compl]; exact hza.1
    obtain ⟨b,hbm,he⟩ := hb.covers z hzM hzN
    have hba := complement_pivotProfile_equal_adj he hza.1 (hb.original_neighbors b hbm) (ha.members a ham).2
    have hba' := complement_pivotProfile_equal_adj he hza.1 (hb.original_neighbors b hbm) (ha.members a' ham').2
    exact ⟨b,hbm,hba.mp hza.2,fun hh => hza' ⟨hza.1,hba'.mpr hh⟩⟩

theorem ProfileFamily.matrix_cols {M : Set V} {r : V} {as bs : List V}
    (hM : GraphModule G M) (ha : ProfileFamily G M r as) (hb : ProfileFamily Gᶜ M r bs)
    (horder : bs.Pairwise (fun b b' => pivotProfile Gᶜ r b' ⊂ pivotProfile Gᶜ r b)) :
    Cols G.Adj as bs := by
  apply horder.imp_of_mem
  intro b b' hbm hbm' h
  refine ⟨?_,?_⟩
  · intro a ham hab
    by_contra hab'
    have haN := (ha.members a ham).2
    have hrac : Gᶜ.Adj r a := (G.compl_adj _ _).mpr ⟨haN.1.symm,haN.2⟩
    have hb'ac : Gᶜ.Adj b' a := (G.compl_adj _ _).mpr
      ⟨fun he => haN.2 (he ▸ hb.original_neighbors b' hbm'),fun he => hab' he.symm⟩
    exact ((G.compl_adj _ _).mp (h.le ⟨hrac,hb'ac⟩).2).2 hab.symm
  · obtain ⟨z,hzb,hzb'⟩ := Set.exists_of_ssubset h
    have hzM : z∈M := by
      by_contra hz
      exact hzb' ⟨hzb.1,(hM.compl b (hb.members b hbm).1 b' (hb.members b' hbm').1 z hz).mp hzb.2⟩
    have hz : z∈nonneighbors G r :=
      ⟨((G.compl_adj _ _).mp hzb.1).1.symm,((G.compl_adj _ _).mp hzb.1).2⟩
    have hzbEdge : ¬G.Adj z b := fun he => ((G.compl_adj _ _).mp hzb.2).2 he.symm
    have hzb'Edge : G.Adj z b' := by
      by_contra hnot
      apply hzb'
      exact ⟨hzb.1,(G.compl_adj _ _).mpr
        ⟨fun he => hz.2 (he ▸ hb.original_neighbors b' hbm'),fun he => hnot he.symm⟩⟩
    obtain ⟨a,ham,he⟩ := ha.covers z hzM hz
    have hbEq := pivotProfile_equal_adj he (hb.original_neighbors b hbm)
    have hb'Eq := pivotProfile_equal_adj he (hb.original_neighbors b' hbm')
    exact ⟨a,ham,hb'Eq.mp hzb'Edge,fun hh => hzbEdge (hbEq.mpr hh)⟩

/-- Ordered local families reconstruct every branch cross-edge with one initial
head query, even though their sort keys counted global outside neighbors. -/
theorem ProfileFamily.weave_cross {M : Set V} {r : V} {as bs : List V}
    (hM : GraphModule G M) (ha : ProfileFamily G M r as) (hb : ProfileFamily Gᶜ M r bs)
    (horderA : as.Pairwise (fun a a' => pivotProfile G r a' ⊂ pivotProfile G r a))
    (horderB : bs.Pairwise (fun b b' => pivotProfile Gᶜ r b' ⊂ pivotProfile Gᶜ r b))
    (s : Bool) (hchoice : HeadChoice G.Adj s as bs) :
    (weave s as bs).Pairwise (fun x y => cross G.Adj x y ↔ joined y=true) :=
  weave_spec G.Adj s as bs (ProfileFamily.matrix_rows hM ha hb horderA) (ProfileFamily.matrix_cols hM ha hb horderB) hchoice

end HiddenCircuits.DH
