import HiddenCircuits.DH.BagSubstitution
import HiddenCircuits.DH.DeletionOrder

/-! Collapse an actual representative module to any chosen member.
The remaining representative graph is the literal induced graph; no edge oracle is substituted. -/
namespace HiddenCircuits.DH
open SimpleGraph
variable {V R : Type*} [DecidableEq R] {G : SimpleGraph V} {H : SimpleGraph R}

abbrev ModuleSurvivor (S : Finset R) (keep : R) := {r : R // r=keep ∨ r∉S}

def moduleRep (S : Finset R) (keep : R) (r : R) : ModuleSurvivor S keep :=
  if hr : r∈S then ⟨keep,Or.inl rfl⟩ else ⟨r,Or.inr hr⟩

def moduleKeep (S : Finset R) (keep : R) : ModuleSurvivor S keep := ⟨keep,Or.inl rfl⟩

lemma moduleRep_surviving (S : Finset R) (keep : R) (r : ModuleSurvivor S keep) :
    moduleRep S keep r.val = r := by
  apply Subtype.ext
  by_cases hr : r.val∈S
  · have he : r.val=keep := r.property.resolve_right (not_not.mpr hr)
    simpa only [moduleRep,hr,↓reduceDIte] using he.symm
  · simp [moduleRep,hr]

lemma moduleRep_onto (S : Finset R) (keep : R) : Function.Surjective (moduleRep S keep) :=
  fun r => ⟨r.val,moduleRep_surviving S keep r⟩

lemma moduleRep_eq_keep (S : Finset R) (keep r : R) (hk : keep∈S) :
    moduleRep S keep r = moduleKeep S keep ↔ r∈S := by
  by_cases hr : r∈S
  · simp [moduleRep,moduleKeep,hr]
  · constructor
    · intro he
      have hval := congrArg Subtype.val he
      simp only [moduleRep,hr,↓reduceDIte,moduleKeep] at hval
      exact False.elim (hr (hval ▸ hk))
    · exact fun h => False.elim (hr h)

lemma moduleRep_eq_other (S : Finset R) (keep r : R) (s : ModuleSurvivor S keep) (hs : s.val≠keep) :
    moduleRep S keep r=s ↔ r=s.val := by
  by_cases hr : r∈S
  · constructor
    · intro he
      have hval := congrArg Subtype.val he
      simp only [moduleRep,hr,↓reduceDIte] at hval
      exact False.elim (hs hval.symm)
    · intro he
      have hnot : s.val∉S := s.property.resolve_left hs
      exact False.elim (hnot (he ▸ hr))
  · constructor
    · intro he
      simpa only [moduleRep,hr,↓reduceDIte] using congrArg Subtype.val he
    · intro he
      subst r
      exact moduleRep_surviving S keep s

/-- A module's representative has precisely its external graph adjacency. -/
lemma GraphModule.adj_moduleRep {S : Finset R} {keep : R} (hm : GraphModule H (S : Set R)) (hk : keep∈S)
    (a b : R) (hne : moduleRep S keep a ≠ moduleRep S keep b) :
    H.Adj a b ↔ (H.induce {r | r=keep ∨ r∉S}).Adj (moduleRep S keep a) (moduleRep S keep b) := by
  by_cases ha : a∈S <;> by_cases hb : b∈S
  · exact False.elim (hne (by simp [moduleRep,ha,hb]))
  · simpa only [moduleRep,ha,hb,↓reduceDIte,induce_adj] using hm a ha keep hk b hb
  · have h := hm b hb keep hk a ha
    simpa only [moduleRep,ha,hb,↓reduceDIte,induce_adj,H.adj_comm] using h
  · simp [moduleRep,ha,hb]

/-- Removing all other module vertices preserves connectivity, independently of cotree shape. -/
theorem GraphModule.connected_moduleDelete {S : Finset R} {keep : R}
    (hm : GraphModule H (S : Set R)) (hk : keep∈S) (hc : H.Connected) :
    (H.induce {r | r=keep ∨ r∉S}).Connected := by
  have hf : ∀ a b, H.Adj a b → (H.induce {r | r=keep ∨ r∉S}).Reachable
      (moduleRep S keep a) (moduleRep S keep b) := by
    intro a b hab
    by_cases he : moduleRep S keep a = moduleRep S keep b
    · rw [he]
    · exact ((hm.adj_moduleRep hk a b he).mp hab).reachable
  refine { preconnected := ?_, nonempty := ⟨moduleKeep S keep⟩ }
  intro a b
  have h := reachable_map_weak (moduleRep S keep) hf (hc a.val b.val)
  simpa only [moduleRep_surviving] using h

/-- Module contraction does not split any pre-existing connected component. -/
theorem GraphModule.reachable_moduleDelete {S : Finset R} {keep : R}
    (hm : GraphModule H (S : Set R)) (hk : keep∈S) (a b : ModuleSurvivor S keep) :
    (H.induce {r | r=keep ∨ r∉S}).Reachable a b ↔ H.Reachable a.val b.val := by
  constructor
  · intro h
    exact h.map (Embedding.induce {r | r=keep ∨ r∉S}).toHom
  · intro h
    have hf : ∀ x y, H.Adj x y → (H.induce {r | r=keep ∨ r∉S}).Reachable
        (moduleRep S keep x) (moduleRep S keep y) := by
      intro x y hxy
      by_cases he : moduleRep S keep x=moduleRep S keep y
      · rw [he]
      · exact ((hm.adj_moduleRep hk x y he).mp hxy).reachable
    simpa only [moduleRep_surviving] using reachable_map_weak (moduleRep S keep) hf h

namespace BoundaryPartition

/-- Module contraction preserves the original graph and every original active vertex. -/
def mergeModule (p : BoundaryPartition G H) (S : Finset R) (keep : R)
    (hk : keep∈S) (hm : GraphModule H (S : Set R)) :
    BoundaryPartition G (H.induce {r | r=keep ∨ r∉S}) where
  place a := moduleRep S keep (p.place a)
  onto := (moduleRep_onto S keep).comp p.onto
  active := p.active
  active_nonempty r := by
    obtain ⟨a,ha,haA⟩ := p.active_nonempty r.val
    exact ⟨a,by rw [ha,moduleRep_surviving],haA⟩
  block a b hne := by
    have hab : p.place a≠p.place b := fun he => hne (congrArg (moduleRep S keep) he)
    rw [p.block a b hab,hm.adj_moduleRep hk (p.place a) (p.place b) hne]

/-- The retained bag is exactly the union of original fibers over the module. -/
def mergedRegionEquiv (p : BoundaryPartition G H) (S : Finset R) (keep : R)
    (hk : keep∈S) (hm : GraphModule H (S : Set R)) :
    {a : V // p.place a∈S} ≃ (p.mergeModule S keep hk hm).Fiber (moduleKeep S keep) where
  toFun a := ⟨a.val,(moduleRep_eq_keep S keep (p.place a.val) hk).mpr a.property⟩
  invFun a := ⟨a.val,(moduleRep_eq_keep S keep (p.place a.val) hk).mp a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def mergedRegionIso (p : BoundaryPartition G H) (S : Finset R) (keep : R)
    (hk : keep∈S) (hm : GraphModule H (S : Set R)) :
    G.induce {a | p.place a∈S} ≃g (p.mergeModule S keep hk hm).fiberGraph (moduleKeep S keep) where
  toEquiv := p.mergedRegionEquiv S keep hk hm
  map_rel_iff' := by rfl

/-- Every other original-vertex bag is unchanged by module contraction. -/
def moduleOtherEquiv (p : BoundaryPartition G H) (S : Finset R) (keep : R)
    (hk : keep∈S) (hm : GraphModule H (S : Set R)) (r : ModuleSurvivor S keep) (hr : r.val≠keep) :
    p.Fiber r.val ≃ (p.mergeModule S keep hk hm).Fiber r where
  toFun a := ⟨a.val,(moduleRep_eq_other S keep (p.place a.val) r hr).mpr a.property⟩
  invFun a := ⟨a.val,(moduleRep_eq_other S keep (p.place a.val) r hr).mp a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def moduleOtherIso (p : BoundaryPartition G H) (S : Finset R) (keep : R)
    (hk : keep∈S) (hm : GraphModule H (S : Set R)) (r : ModuleSurvivor S keep) (hr : r.val≠keep) :
    p.fiberGraph r.val ≃g (p.mergeModule S keep hk hm).fiberGraph r where
  toEquiv := p.moduleOtherEquiv S keep hk hm r hr
  map_rel_iff' := by rfl

lemma moduleOther_active (p : BoundaryPartition G H) (S : Finset R) (keep : R)
    (hk : keep∈S) (hm : GraphModule H (S : Set R)) (r : ModuleSurvivor S keep) (hr : r.val≠keep) :
    p.moduleOtherIso S keep hk hm r hr '' p.fiberActive r.val =
      (p.mergeModule S keep hk hm).fiberActive r := by
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro ha
    exact ⟨(p.moduleOtherIso S keep hk hm r hr).symm a,ha,
      (p.moduleOtherIso S keep hk hm r hr).apply_symm_apply a⟩

/-- Retaining labels allows the cotree region and the module set to be connected by identity. -/
def regionModuleIso (p : BoundaryPartition G H) (t : LabeledCographTree R) (S : Finset R)
    (hcover : ∀ r, r∈t.leaves ↔ r∈S) :
    G.induce (p.region t) ≃g G.induce {a | p.place a∈S} where
  toEquiv :=
    { toFun := fun a => ⟨a.val,(hcover (p.place a.val)).mp a.property⟩
      invFun := fun a => ⟨a.val,(hcover (p.place a.val)).mpr a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := by rfl

noncomputable def substituteModuleIso (p : BoundaryPartition G H) (rep : p.Representation)
    (t : LabeledCographTree R) (S : Finset R) (keep : R)
    (hk : keep∈S) (hm : GraphModule H (S : Set R)) (hn : t.leaves.Nodup) (hc : t.Correct H)
    (hcover : ∀ r, r∈t.leaves ↔ r∈S) :
    (t.substitute rep.expr).graph ≃g (p.mergeModule S keep hk hm).fiberGraph (moduleKeep S keep) :=
  ((p.substituteIso rep t hn hc).trans (p.regionModuleIso t S hcover)).trans
    (p.mergedRegionIso S keep hk hm)

lemma substituteModuleIso_active (p : BoundaryPartition G H) (rep : p.Representation)
    (t : LabeledCographTree R) (S : Finset R) (keep : R)
    (hk : keep∈S) (hm : GraphModule H (S : Set R)) (hn : t.leaves.Nodup) (hc : t.Correct H)
    (hcover : ∀ r, r∈t.leaves ↔ r∈S) :
    p.substituteModuleIso rep t S keep hk hm hn hc hcover '' (t.substitute rep.expr).active =
      (p.mergeModule S keep hk hm).fiberActive (moduleKeep S keep) := by
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (p.realize_active rep t x).mpr hx
  · intro ha
    obtain ⟨x,rfl⟩ := (p.substituteModuleIso rep t S keep hk hm hn hc hcover).toEquiv.surjective a
    exact ⟨x,(p.realize_active rep t x).mp ha,rfl⟩

/-- Executable table update: old expressions are reused at leaves, with one new expression
for the chosen representative and unchanged entries for every other surviving representative. -/
def moduleExprUpdate (bags : R → BagExpr) (t : LabeledCographTree R) (S : Finset R) (keep : R)
    (r : ModuleSurvivor S keep) : BagExpr :=
  if r.val=keep then t.substitute bags else bags r.val

/-- The exact executable expression-table update preserves graph and active-boundary semantics. -/
noncomputable def moduleRepresentation (p : BoundaryPartition G H) (rep : p.Representation)
    (t : LabeledCographTree R) (S : Finset R) (keep : R)
    (hk : keep∈S) (hm : GraphModule H (S : Set R)) (hn : t.leaves.Nodup) (hc : t.Correct H)
    (hcover : ∀ r, r∈t.leaves ↔ r∈S) : (p.mergeModule S keep hk hm).Representation := by
  let payload (r : ModuleSurvivor S keep) :
      {iso : (moduleExprUpdate rep.expr t S keep r).graph ≃g (p.mergeModule S keep hk hm).fiberGraph r //
        iso '' (moduleExprUpdate rep.expr t S keep r).active = (p.mergeModule S keep hk hm).fiberActive r} := by
    by_cases hr : r.val=keep
    · have he : r=moduleKeep S keep := Subtype.ext hr
      have pack : {iso : (t.substitute rep.expr).graph ≃g (p.mergeModule S keep hk hm).fiberGraph r //
          iso '' (t.substitute rep.expr).active = (p.mergeModule S keep hk hm).fiberActive r} := by
        subst r
        exact ⟨p.substituteModuleIso rep t S keep hk hm hn hc hcover,
          p.substituteModuleIso_active rep t S keep hk hm hn hc hcover⟩
      have hex : moduleExprUpdate rep.expr t S keep r = t.substitute rep.expr := if_pos hr
      exact Eq.mp (congrArg (fun e : BagExpr =>
        {iso : e.graph ≃g (p.mergeModule S keep hk hm).fiberGraph r //
          iso '' e.active = (p.mergeModule S keep hk hm).fiberActive r}) hex).symm pack
    · have pack : {iso : (rep.expr r.val).graph ≃g (p.mergeModule S keep hk hm).fiberGraph r //
          iso '' (rep.expr r.val).active = (p.mergeModule S keep hk hm).fiberActive r} := by
        refine ⟨(rep.iso r.val).trans (p.moduleOtherIso S keep hk hm r hr),?_⟩
        have hi := Set.image_image (p.moduleOtherIso S keep hk hm r hr) (rep.iso r.val)
          (rep.expr r.val).active
        exact hi.symm.trans ((congrArg (Set.image (p.moduleOtherIso S keep hk hm r hr))
          (rep.active_image r.val)).trans (p.moduleOther_active S keep hk hm r hr))
      have hex : moduleExprUpdate rep.expr t S keep r = rep.expr r.val := if_neg hr
      exact Eq.mp (congrArg (fun e : BagExpr =>
        {iso : e.graph ≃g (p.mergeModule S keep hk hm).fiberGraph r //
          iso '' e.active = (p.mergeModule S keep hk hm).fiberActive r}) hex).symm pack
  exact
    { expr := moduleExprUpdate rep.expr t S keep
      iso := fun r => (payload r).1
      active_image := fun r => (payload r).2 }

end BoundaryPartition
end HiddenCircuits.DH
