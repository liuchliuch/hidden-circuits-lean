import HiddenCircuits.DH.LayerScheduleForest

/-! Literal-mask refinement of the graph-semantic deletion invariants. -/
namespace HiddenCircuits.DH.LayerScheduleForest
open SimpleGraph LayerSchedule
variable {V : Type*} {G : SimpleGraph V}

/-- Identity on original labels between nested and flat induced restrictions. -/
def restrictionIso (G : SimpleGraph V) {A B : Set V} (hBA : B⊆A) (Q : Set A)
    (hQ : ∀v:A, v.val∈B ↔ v∈Q) : (G.induce A).induce Q ≃g G.induce B where
  toEquiv :=
    { toFun := fun v => ⟨v.val.val,(hQ v.val).mpr v.property⟩
      invFun := fun v => ⟨⟨v.val,hBA v.property⟩,(hQ ⟨v.val,hBA v.property⟩).mp v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := by intro a b; rfl

/-- All-pairs reachability preservation transports through a literal mask refinement. -/
lemma restriction_reachable {A B : Set V} (hBA : B⊆A) (Q : Set A)
    (hQ : ∀v:A, v.val∈B ↔ v∈Q)
    (hr : ∀a b:Q, ((G.induce A).induce Q).Reachable a b ↔ (G.induce A).Reachable a.val b.val)
    (a b : B) :
    (G.induce B).Reachable a b ↔ (G.induce A).Reachable ⟨a.val,hBA a.property⟩ ⟨b.val,hBA b.property⟩ := by
  let e := restrictionIso G hBA Q hQ
  constructor
  · intro h
    exact (hr (e.symm a) (e.symm b)).mp (h.map e.symm.toHom)
  · intro h
    have h' := (hr (e.symm a) (e.symm b)).mpr h
    exact h'.map e.toHom

/-- A one-depth module contraction preserves the fixed original BFS forest
invariant for any concrete mask having exactly the required retained labels. -/
theorem LiveInvariant.module_mask [DecidableEq V]
    {root : V → V} {depth : V → ℕ} {A B : Set V}
    (hi : LiveInvariant G root depth A) (S : Finset A) (keep : A)
    (hk : keep∈S) (hm : HiddenCircuits.DH.GraphModule (G.induce A) (S : Set A))
    (k : ℕ) (hd : ∀v∈S, depth v.val=k)
    (hroots : ∀v, (⟨root v,hi.roots_alive v⟩ : A)=keep ∨ ⟨root v,hi.roots_alive v⟩∉S)
    (hmask : ∀v, v∈B ↔ ∃ha:v∈A, (⟨v,ha⟩ : A)=keep ∨ ⟨v,ha⟩∉S) :
    LiveInvariant G root depth B := by
  have hBA : B⊆A := by intro v hv; exact ((hmask v).mp hv).choose
  let Q : Set A := {v | v=keep ∨ v∉S}
  have hQ (v : A) : v.val∈B ↔ v∈Q := by
    constructor
    · rintro hv; obtain ⟨ha,h⟩ := (hmask v.val).mp hv; exact h
    · intro hv; exact (hmask v.val).mpr ⟨v.property,hv⟩
  refine ⟨?_,?_,?_⟩
  · intro v; exact (hmask (root v)).mpr ⟨hi.roots_alive v,hroots v⟩
  · intro a b
    exact (restriction_reachable hBA Q hQ (hm.reachable_moduleDelete hk) a b).trans
      (hi.reachable ⟨a.val,hBA a.property⟩ ⟨b.val,hBA b.property⟩)
  · intro a b
    have hSame : ∀a b:Q, (((sameDepthGraph G depth).induce A).induce Q).Reachable a b ↔
        ((sameDepthGraph G depth).induce A).Reachable a.val b.val := by
      intro a b
      simpa only [sameDepthGraph_induce] using module_sameDepth_reachable hm hk (fun v=>depth v.val) k hd a b
    exact (restriction_reachable hBA Q hQ hSame a b).trans
      (hi.sameDepth ⟨a.val,hBA a.property⟩ ⟨b.val,hBA b.property⟩)

/-- A pendant deletion at distinct depths preserves both reachability relations. -/
theorem LiveInvariant.pendant_mask
    {root : V → V} {depth : V → ℕ} {A B : Set V}
    (hi : LiveInvariant G root depth A) (keep removed : A)
    (hp : PendantPair (G.induce A) keep removed)
    (hd : depth removed.val≠depth keep.val)
    (hroots : ∀v, root v≠removed.val)
    (hmask : ∀v, v∈B ↔ v∈A ∧ v≠removed.val) :
    LiveInvariant G root depth B := by
  have hBA : B⊆A := by intro v hv; exact ((hmask v).mp hv).1
  let Q : Set A := {v | v≠removed}
  have hQ (v : A) : v.val∈B ↔ v∈Q := by
    rw [hmask]
    exact ⟨fun h he => h.2 (congrArg Subtype.val he),fun h=>⟨v.property,fun he=>h (Subtype.ext he)⟩⟩
  refine ⟨fun v=>(hmask _).mpr ⟨hi.roots_alive v,hroots v⟩,?_,?_⟩
  · intro a b
    exact (restriction_reachable hBA Q hQ (pendant_reachable_delete hp) a b).trans
      (hi.reachable ⟨a.val,hBA a.property⟩ ⟨b.val,hBA b.property⟩)
  · intro a b
    have hSame : ∀a b:Q, (((sameDepthGraph G depth).induce A).induce Q).Reachable a b ↔
        ((sameDepthGraph G depth).induce A).Reachable a.val b.val := by
      intro a b
      simpa only [sameDepthGraph_induce] using pendant_sameDepth_reachable hp (fun v=>depth v.val) hd a b
    exact (restriction_reachable hBA Q hQ hSame a b).trans
      (hi.sameDepth ⟨a.val,hBA a.property⟩ ⟨b.val,hBA b.property⟩)

end HiddenCircuits.DH.LayerScheduleForest
