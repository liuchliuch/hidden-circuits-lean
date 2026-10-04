import HiddenCircuits.DH.Pruning
import Mathlib.Data.Finset.Max

/-! Finite P4-free graphs have genuine twin vertices; no cotree assumption. -/
namespace HiddenCircuits.DH
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma P4Free.no_path4 (hG : P4Free G) (a b c d : V)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hac : ¬G.Adj a c) (had : ¬G.Adj a d) (hbd : ¬G.Adj b d) : False := by
  have habn := hab.ne
  have hbcn := hbc.ne
  have hcdn := hcd.ne
  have hacn : a≠c := by intro h; subst c; exact had hcd
  have hbdn : b≠d := by intro h; subst d; exact had hab
  have hadn : a≠d := by intro h; subst d; exact hbd hab.symm
  let f : Fin 4 → V := ![a,b,c,d]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f,eq_comm]
  have hba := hab.symm
  have hcb := hbc.symm
  have hdc := hcd.symm
  have hca : ¬G.Adj c a := fun h => hac h.symm
  have hda : ¬G.Adj d a := fun h => had h.symm
  have hdb : ¬G.Adj d b := fun h => hbd h.symm
  apply hG.false
  exact {
    toFun := f
    inj' := hf
    map_rel_iff' := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp_all [f,pathGraph_adj] }

lemma P4Free.distance_le_two (hG : P4Free G) {a b : V} (hab : G.Reachable a b) :
    G.dist a b ≤ 2 := by
  obtain ⟨p,hp⟩ := hab.exists_walk_length_eq_dist
  by_contra h
  have h3 : 3 ≤ p.length := by omega
  have he (i : ℕ) (hi : i<3) : G.Adj (p.getVert i) (p.getVert (i+1)) :=
    p.adj_getVert_succ (by omega)
  have hn (i j : ℕ) (hi : i+1<j) (hj : j≤3) : ¬G.Adj (p.getVert i) (p.getVert j) := by
    intro hA
    have hd := shortest_segment_dist p hp i j (by omega) (by omega)
    have h1 := dist_eq_one_iff_adj.mpr hA
    omega
  exact hG.no_path4 _ _ _ _ (he 0 (by decide)) (he 1 (by decide)) (he 2 (by decide))
    (hn 0 2 (by decide) (by decide)) (hn 0 3 (by decide) (by decide))
    (hn 1 3 (by decide) (by decide))

lemma P4Free.common_neighbor (hG : P4Free G) (hc : G.Connected) {r c : V}
    (hne : r≠c) (hn : ¬G.Adj r c) : ∃ a, G.Adj r a ∧ G.Adj c a := by
  have hlo := (hc r c).one_lt_dist_of_ne_of_not_adj hne hn
  have hhi := hG.distance_le_two (hc r c)
  obtain ⟨a,ha,hb⟩ := exists_commonNeighbor_of_dist_two (show G.dist r c=2 by omega)
  exact ⟨a,ha,hb.symm⟩

lemma P4Free.neighbor_cut_complete (hG : P4Free G) {r c a b : V}
    (hn : ¬G.Adj r c) (hra : G.Adj r a) (hrb : G.Adj r b)
    (hca : G.Adj c a) (hcb : ¬G.Adj c b) : G.Adj a b := by
  by_contra hab
  exact hG.no_path4 c a r b hca hra.symm hrb (fun h => hn h.symm) hcb hab

lemma P4Free.adjacent_far_neighbors (hG : P4Free G) {r c d a : V}
    (hrc : ¬G.Adj r c) (hrd : ¬G.Adj r d) (hcd : G.Adj c d)
    (hra : G.Adj r a) (hca : G.Adj c a) : G.Adj d a := by
  by_contra hda
  exact hG.no_path4 r a c d hra hca.symm hcd hrc hrd (fun h => hda h.symm)

lemma P4Free.common_neighbors_nested (hG : P4Free G) {r c d : V}
    (hrc : ¬G.Adj r c) (hrd : ¬G.Adj r d) :
    (∀ a, G.Adj r a → G.Adj c a → G.Adj d a) ∨
      (∀ a, G.Adj r a → G.Adj d a → G.Adj c a) := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨⟨a,hra,hca,hda⟩,b,hrb,hdb,hcb⟩ := h
  have hab := hG.neighbor_cut_complete hrc hra hrb hca hcb
  have hcd : ¬G.Adj c d := fun he => hda (hG.adjacent_far_neighbors hrc hrd he hra hca)
  exact hG.no_path4 c a b d hca hab hdb.symm hcb hcd (fun he => hda he.symm)

noncomputable def commonNeighbors [Fintype V] (G : SimpleGraph V) (r c : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun a => G.Adj r a ∧ G.Adj c a)

@[simp] lemma mem_commonNeighbors [Fintype V] (r c a : V) :
    a∈commonNeighbors G r c ↔ G.Adj r a ∧ G.Adj c a := by
  classical
  simp [commonNeighbors]

/-- A connected nontrivial P4-free graph has a nontrivial complete join cut. -/
theorem P4Free.connected_join_cut [Fintype V] [Nontrivial V]
    (hG : P4Free G) (hc : G.Connected) :
    ∃ S : Set V, S.Nonempty ∧ Sᶜ.Nonempty ∧ ∀ x∈S, ∀ y∉S, G.Adj x y := by
  classical
  let r : V := Classical.arbitrary V
  let far : Finset V := Finset.univ.filter (fun c => c≠r ∧ ¬G.Adj r c)
  by_cases hfar : far.Nonempty
  · obtain ⟨c,hcF,hmin⟩ := far.exists_min_image (fun c => (commonNeighbors G r c).card) hfar
    have hcF' : c≠r ∧ ¬G.Adj r c := by simpa [far] using hcF
    have hincl (d : V) (hd : d∈far) : commonNeighbors G r c ⊆ commonNeighbors G r d := by
      have hd' : d≠r ∧ ¬G.Adj r d := by simpa [far] using hd
      rcases hG.common_neighbors_nested hcF'.2 hd'.2 with h | h
      · intro a ha
        obtain ⟨hra,hca⟩ := (mem_commonNeighbors r c a).mp ha
        exact (mem_commonNeighbors r d a).mpr ⟨hra,h a hra hca⟩
      · have hsub : commonNeighbors G r d ⊆ commonNeighbors G r c := by
          intro a ha
          obtain ⟨hra,hda⟩ := (mem_commonNeighbors r d a).mp ha
          exact (mem_commonNeighbors r c a).mpr ⟨hra,h a hra hda⟩
        have he := Finset.eq_of_subset_of_card_le hsub (hmin d hd)
        rw [he]
    refine ⟨(commonNeighbors G r c : Set V),?_,?_,?_⟩
    · obtain ⟨a,hra,hca⟩ := hG.common_neighbor hc hcF'.1.symm hcF'.2
      exact ⟨a,(mem_commonNeighbors r c a).mpr ⟨hra,hca⟩⟩
    · refine ⟨r,?_⟩
      simp
    · intro x hx y hy
      obtain ⟨hrx,hcx⟩ := (mem_commonNeighbors r c x).mp hx
      by_cases hyr : y=r
      · subst y; exact hrx.symm
      · by_cases hry : G.Adj r y
        · have hcy : ¬G.Adj c y := fun h => hy ((mem_commonNeighbors r c y).mpr ⟨hry,h⟩)
          exact hG.neighbor_cut_complete hcF'.2 hrx hry hcx hcy
        · have hyF : y∈far := by simp [far,hyr,hry]
          exact ((mem_commonNeighbors r y x).mp (hincl y hyF hx)).2.symm
  · refine ⟨{r},by simp,?_,?_⟩
    · obtain ⟨y,hy⟩ := exists_ne r
      exact ⟨y,by simpa using hy⟩
    · intro x hx y hy
      have hx' : x=r := hx
      subst x
      by_contra hry
      exact hfar ⟨y,by simpa [far] using And.intro (show y≠r from hy) hry⟩

/-- Every nontrivial P4-free graph admits a proper split whose two sides are modules. -/
theorem P4Free.module_split [Fintype V] [Nontrivial V] (hG : P4Free G) :
    ∃ S : Set V, S.Nonempty ∧ Sᶜ.Nonempty ∧ GraphModule G S ∧ GraphModule G Sᶜ := by
  classical
  have build (S : Set V) (hS : S.Nonempty) (hT : Sᶜ.Nonempty)
      (hcut : (∀ x∈S, ∀ y∉S, G.Adj x y) ∨ (∀ x∈S, ∀ y∉S, ¬G.Adj x y)) :
      ∃ S : Set V, S.Nonempty ∧ Sᶜ.Nonempty ∧ GraphModule G S ∧ GraphModule G Sᶜ := by
    refine ⟨S,hS,hT,?_,?_⟩
    · intro u hu v hv x hx
      rcases hcut with h | h
      · exact ⟨fun _ => h v hv x hx,fun _ => h u hu x hx⟩
      · exact ⟨fun he => (h u hu x hx he).elim,fun he => (h v hv x hx he).elim⟩
    · intro u hu v hv x hx
      have hx' : x∈S := by simpa using hx
      rcases hcut with h | h
      · exact ⟨fun _ => (h x hx' v hv).symm,fun _ => (h x hx' u hu).symm⟩
      · exact ⟨fun he => (h x hx' u hu he.symm).elim,fun he => (h x hx' v hv he.symm).elim⟩
  by_cases hc : G.Connected
  · obtain ⟨S,hS,hT,hcut⟩ := hG.connected_join_cut hc
    exact build S hS hT (Or.inl hcut)
  · have hh : ∀ r : V, ∃ s, ¬G.Reachable r s := by
      simpa only [connected_iff_exists_forall_reachable,not_exists,not_forall] using hc
    let r : V := Classical.arbitrary V
    obtain ⟨s,hs⟩ := hh r
    let S : Set V := {x | G.Reachable r x}
    apply build S ⟨r,Reachable.refl r⟩ ⟨s,hs⟩ (Or.inr ?_)
    intro x hx y hy hxy
    exact hy (hx.trans hxy.reachable)

universe u

private theorem p4free_twins_card (n : ℕ) :
    ∀ (V : Type u) [Fintype V] [Nontrivial V] (G : SimpleGraph V),
      Fintype.card V=n → P4Free G → ∃ u v, TwinPair G u v := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G hn hG
    obtain ⟨S,hS,hT,hmS,hmT⟩ := hG.module_split
    obtain ⟨s,hs⟩ := hS
    obtain ⟨t,ht⟩ := hT
    by_cases hSN : Nontrivial S
    · letI : Nontrivial S := hSN
      have hlt : Fintype.card S<n := by rw [← hn]; exact Fintype.card_subtype_lt ht
      obtain ⟨u,v,huv⟩ := ih (Fintype.card S) hlt S (G.induce S) rfl (hG.induce S)
      exact ⟨u.val,v.val,huv.of_induce_module hmS⟩
    · by_cases hTN : Nontrivial ↥(Sᶜ : Set V)
      · letI : Nontrivial ↥(Sᶜ : Set V) := hTN
        have hlt : Fintype.card ↥(Sᶜ : Set V)<n := by
          rw [← hn]
          apply Fintype.card_subtype_lt (x := s)
          simpa using hs
        obtain ⟨u,v,huv⟩ := ih (Fintype.card ↥(Sᶜ : Set V)) hlt ↥(Sᶜ : Set V) (G.induce Sᶜ) rfl (hG.induce Sᶜ)
        exact ⟨u.val,v.val,huv.of_induce_module hmT⟩
      · haveI : Subsingleton S := not_nontrivial_iff_subsingleton.mp hSN
        haveI : Subsingleton ↥(Sᶜ : Set V) := not_nontrivial_iff_subsingleton.mp hTN
        refine ⟨s,t,?_,?_⟩
        · intro he; exact ht (he ▸ hs)
        · intro x hxs hxt
          exfalso
          by_cases hx : x∈S
          · exact hxs (congrArg Subtype.val (Subsingleton.elim (⟨x,hx⟩ : S) ⟨s,hs⟩))
          · exact hxt (congrArg Subtype.val (Subsingleton.elim (⟨x,hx⟩ : ↥(Sᶜ : Set V)) ⟨t,ht⟩))

/-- Every finite nontrivial P4-free graph contains two genuine twins. -/
theorem P4Free.exists_twins [Finite V] [Nontrivial V] (hG : P4Free G) :
    ∃ u v, TwinPair G u v := by
  classical
  letI := Fintype.ofFinite V
  exact p4free_twins_card (Fintype.card V) V G rfl hG

end HiddenCircuits.DH
