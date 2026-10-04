import HiddenCircuits.DH.ModuleStoreSemantics

/-! Constant-time actual pendant-bag update with full original-graph refinement. -/
namespace HiddenCircuits.DH.ModuleExecution
open SimpleGraph LexBFSPartition

def absorb {n : ℕ} (s : Store n) (keep removed : Fin n) : Counted (Store n) :=
  ⟨⟨s.alive.set removed.val false,
    s.bags.set keep.val (.pendant s.bags[keep.val] s.bags[removed.val])⟩,5⟩

lemma absorb_alive {n : ℕ} (s : Store n) (keep removed v : Fin n) :
    (absorb s keep removed).value.alive[v.val]=true ↔ s.alive[v.val]=true ∧ v≠removed := by
  by_cases hv : v=removed
  · subst v; simp [absorb]
  · have hv' : removed.val≠v.val := fun he => hv (Fin.ext he).symm
    simp [absorb,hv,hv']

@[simp] lemma absorb_kept_bag {n : ℕ} (s : Store n) (keep removed : Fin n) :
    (absorb s keep removed).value.bags[keep.val] = .pendant s.bags[keep.val] s.bags[removed.val] := by
  simp [absorb]

lemma absorb_other_bag {n : ℕ} (s : Store n) (keep removed v : Fin n) (hv : v≠keep) :
    (absorb s keep removed).value.bags[v.val] = s.bags[v.val] := by
  have hv' : keep.val≠v.val := fun he => hv (Fin.ext he).symm
  simp [absorb,hv']

def absorbRepresentativeIso {n : ℕ} (G : SimpleGraph (Fin n)) (s : Store n) (keep removed : Fin n)
    (hd : s.alive[removed.val]=true) :
    (liveGraph G s).induce {r | r≠⟨removed,hd⟩} ≃g liveGraph G (absorb s keep removed).value where
  toEquiv :=
    { toFun := fun r => ⟨r.val.val,(absorb_alive s keep removed r.val.val).mpr
        ⟨r.val.property,fun he => r.property (Subtype.ext he)⟩⟩
      invFun := fun r =>
        let h := (absorb_alive s keep removed r.val).mp r.property
        ⟨⟨r.val,h.1⟩,fun he => h.2 (congrArg Subtype.val he)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := by intro a b; rfl

/-- The two reads, constructor and two writes implement the proved actual pendant merge. -/
noncomputable def Interpretation.absorb {n : ℕ} {G : SimpleGraph (Fin n)} {s : Store n}
    (I : Interpretation G s) (keep removed : Fin n)
    (hk : s.alive[keep.val]=true) (hd : s.alive[removed.val]=true)
    (hp : PendantPair (liveGraph G s) ⟨keep,hk⟩ ⟨removed,hd⟩) :
    Interpretation G (ModuleExecution.absorb s keep removed).value := by
  let p := I.partition.pendantMerge hp
  let rep := I.representation.pendant hp
  let e := absorbRepresentativeIso G s keep removed hd
  refine ⟨p.reindex e,p.reindexRepresentation rep e,?_⟩
  intro r
  change (I.representation.pendant hp).expr (e.symm r) =
    (ModuleExecution.absorb s keep removed).value.bags[r.val.val]
  rw [BoundaryPartition.Representation.pendant_expr]
  have hraw : (e.symm r).val.val=r.val := rfl
  by_cases hr : r.val=keep
  · have he : (e.symm r).val=⟨keep,hk⟩ := Subtype.ext (hraw.trans hr)
    rw [BoundaryPartition.updateExpr,if_pos he,I.bags_eq,I.bags_eq]
    exact (absorb_kept_bag s keep removed).symm.trans
      (congrArg (fun v : Fin n => (ModuleExecution.absorb s keep removed).value.bags[v.val]) hr.symm)
  · have he : (e.symm r).val≠⟨keep,hk⟩ := fun h => hr (hraw.symm.trans (congrArg Subtype.val h))
    rw [BoundaryPartition.updateExpr,if_neg he,I.bags_eq,absorb_other_bag s keep removed r.val hr]
    rfl

@[simp] theorem absorb_accesses {n : ℕ} (s : Store n) (keep removed : Fin n) :
    (absorb s keep removed).accesses=5 := rfl

end HiddenCircuits.DH.ModuleExecution
