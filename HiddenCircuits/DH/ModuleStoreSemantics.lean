import HiddenCircuits.DH.ModuleExecution
import HiddenCircuits.DH.BagReindex

/-! Refinement of the fixed-size live/bag arrays to the original-graph boundary partition. -/
namespace HiddenCircuits.DH.ModuleExecution
open SimpleGraph

abbrev Live {n : ℕ} (s : Store n) := {v : Fin n // s.alive[v.val]=true}

def liveGraph {n : ℕ} (G : SimpleGraph (Fin n)) (s : Store n) : SimpleGraph (Live s) :=
  G.induce {v : Fin n | s.alive[v.val]=true}

/-- The concrete bag array is linked to genuine fibers of the unchanged original graph. -/
structure Interpretation {n : ℕ} (G : SimpleGraph (Fin n)) (s : Store n) where
  partition : BoundaryPartition G (liveGraph G s)
  representation : partition.Representation
  bags_eq : ∀ r : Live s, representation.expr r = s.bags[r.val.val]

def initial (n : ℕ) : Store n := ⟨Vector.replicate n true,Vector.replicate n .leaf⟩

def initialIso {n : ℕ} (G : SimpleGraph (Fin n)) : G ≃g liveGraph G (initial n) where
  toEquiv :=
    { toFun := fun v => ⟨v,by simp [initial]⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := by intro a b; rfl

noncomputable def initialInterpretation {n : ℕ} (G : SimpleGraph (Fin n)) : Interpretation G (initial n) where
  partition := (BoundaryPartition.initial G).reindex (initialIso G)
  representation := (BoundaryPartition.initial G).reindexRepresentation
    (BoundaryPartition.initialRepresentation G) (initialIso G)
  bags_eq := by intro r; simp [BoundaryPartition.reindexRepresentation,BoundaryPartition.initialRepresentation,initial]

/-- Proof-side lift is identity on every actual live tree label. The fallback is unused
by a tree whose supplied region is live. -/
def liveLift {n : ℕ} (s : Store n) (keep : Fin n) (hk : s.alive[keep.val]=true) (v : Fin n) : Live s :=
  if hv : s.alive[v.val]=true then ⟨v,hv⟩ else ⟨keep,hk⟩

lemma liveLift_val {n : ℕ} (s : Store n) (keep : Fin n) (hk : s.alive[keep.val]=true)
    (v : Fin n) (hv : s.alive[v.val]=true) : (liveLift s keep hk v).val=v := by
  simp [liveLift,hv]

lemma liveLift_live {n : ℕ} (s : Store n) (keep : Fin n) (hk : s.alive[keep.val]=true) (v : Live s) :
    liveLift s keep hk v.val=v := by
  apply Subtype.ext
  exact liveLift_val s keep hk v.val v.property

def liveModule {n : ℕ} (s : Store n) (vertices : List (Fin n)) : Finset (Live s) :=
  Finset.univ.filter (fun r => r.val∈vertices)

@[simp] lemma mem_liveModule {n : ℕ} (s : Store n) (vertices : List (Fin n)) (r : Live s) :
    r∈liveModule s vertices ↔ r.val∈vertices := by simp [liveModule]

lemma lifted_cover {n : ℕ} (s : Store n) (vertices : List (Fin n)) (keep : Fin n)
    (hk : s.alive[keep.val]=true) (tree : LabeledCographTree (Fin n))
    (hlive : ∀ v∈vertices, s.alive[v.val]=true)
    (hcover : ∀ v, v∈tree.leaves ↔ v∈vertices) (r : Live s) :
    r∈(tree.mapLabels (liveLift s keep hk)).leaves ↔ r∈liveModule s vertices := by
  rw [LabeledCographTree.mapLabels_leaves,List.mem_map,mem_liveModule]
  constructor
  · rintro ⟨v,hv,he⟩
    have hl := hlive v ((hcover v).mp hv)
    have hval : v=r.val := (liveLift_val s keep hk v hl).symm.trans (congrArg Subtype.val he)
    exact hval ▸ (hcover v).mp hv
  · intro hr
    exact ⟨r.val,(hcover r.val).mpr hr,liveLift_live s keep hk r⟩

lemma lifted_nodup {n : ℕ} (s : Store n) (vertices : List (Fin n)) (keep : Fin n)
    (hk : s.alive[keep.val]=true) (tree : LabeledCographTree (Fin n))
    (hlive : ∀ v∈vertices, s.alive[v.val]=true)
    (hcover : ∀ v, v∈tree.leaves ↔ v∈vertices) (hn : tree.leaves.Nodup) :
    (tree.mapLabels (liveLift s keep hk)).leaves.Nodup := by
  rw [LabeledCographTree.mapLabels_leaves]
  apply List.Nodup.map_on ?_ hn
  intro a ha b hb he
  have ha' := liveLift_val s keep hk a (hlive a ((hcover a).mp ha))
  have hb' := liveLift_val s keep hk b (hlive b ((hcover b).mp hb))
  exact ha'.symm.trans ((congrArg Subtype.val he).trans hb')

lemma lifted_correct {n : ℕ} (G : SimpleGraph (Fin n)) (s : Store n) (vertices : List (Fin n))
    (keep : Fin n) (hk : s.alive[keep.val]=true) (tree : LabeledCographTree (Fin n))
    (hlive : ∀ v∈vertices, s.alive[v.val]=true)
    (hcover : ∀ v, v∈tree.leaves ↔ v∈vertices) (hc : tree.Correct G) :
    (tree.mapLabels (liveLift s keep hk)).Correct (liveGraph G s) := by
  apply LabeledCographTree.Correct.mapLabels _ _ hc
  intro a ha b hb
  change G.Adj (liveLift s keep hk a).val (liveLift s keep hk b).val ↔ G.Adj a b
  rw [liveLift_val s keep hk a (hlive a ((hcover a).mp ha)),
    liveLift_val s keep hk b (hlive b ((hcover b).mp hb))]

/-- The nested representative subtype after semantic module contraction is exactly the
new live mask computed by the actual markExcept loop. -/
def contractRepresentativeIso {n : ℕ} (G : SimpleGraph (Fin n)) (s : Store n)
    (vertices : List (Fin n)) (keep : Fin n) (hk : s.alive[keep.val]=true)
    (tree : LabeledCographTree (Fin n)) :
    (liveGraph G s).induce {r | r=⟨keep,hk⟩ ∨ r∉liveModule s vertices} ≃g
      liveGraph G (contract s vertices keep tree).value where
  toEquiv :=
    { toFun := fun r => ⟨r.val.val,(contract_alive s vertices keep tree r.val.val).mpr ⟨r.val.property,by
        rcases r.property with he | he
        · exact Or.inl (congrArg Subtype.val he)
        · exact Or.inr (by simpa using he)⟩⟩
      invFun := fun r =>
        let hr := (contract_alive s vertices keep tree r.val).mp r.property
        ⟨⟨r.val,hr.1⟩,by
          rcases hr.2 with he | he
          · exact Or.inl (Subtype.ext he)
          · exact Or.inr (by simpa using he)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := by intro a b; rfl

/-- Actual fixed-array contraction preserves the full original-graph interpretation.
The only semantic side conditions are the actual module and the computed cotree's
independently established correctness, distinct labels, and coverage. -/
noncomputable def Interpretation.contract {n : ℕ} {G : SimpleGraph (Fin n)} {s : Store n}
    (I : Interpretation G s) (vertices : List (Fin n)) (keep : Fin n)
    (hkeep : keep∈vertices) (hlive : ∀ v∈vertices, s.alive[v.val]=true)
    (tree : LabeledCographTree (Fin n)) (hn : tree.leaves.Nodup) (hc : tree.Correct G)
    (hcover : ∀ v, v∈tree.leaves ↔ v∈vertices)
    (hm : GraphModule (liveGraph G s) (liveModule s vertices : Set (Live s))) :
    Interpretation G (ModuleExecution.contract s vertices keep tree).value := by
  let hk := hlive keep hkeep
  let S := liveModule s vertices
  let k : Live s := ⟨keep,hk⟩
  let t := tree.mapLabels (liveLift s keep hk)
  have hkS : k∈S := by simpa [S,k] using hkeep
  have htN : t.leaves.Nodup := lifted_nodup s vertices keep hk tree hlive hcover hn
  have htC : t.Correct (liveGraph G s) := lifted_correct G s vertices keep hk tree hlive hcover hc
  have htS : ∀ r, r∈t.leaves ↔ r∈S := lifted_cover s vertices keep hk tree hlive hcover
  let p := I.partition.mergeModule S k hkS hm
  let rep := I.partition.moduleRepresentation I.representation t S k hkS hm htN htC htS
  let e := contractRepresentativeIso G s vertices keep hk tree
  refine ⟨p.reindex e,p.reindexRepresentation rep e,?_⟩
  intro r
  change BoundaryPartition.moduleExprUpdate I.representation.expr t S k (e.symm r) =
    (ModuleExecution.contract s vertices keep tree).value.bags[r.val.val]
  have hraw : (e.symm r).val.val=r.val := rfl
  by_cases hr : r.val=keep
  · have hsame : (e.symm r).val=k := Subtype.ext (hraw.trans hr)
    rw [BoundaryPartition.moduleExprUpdate,if_pos hsame]
    have hsub : t.substitute I.representation.expr = tree.substitute (fun v => s.bags[v.val]) := by
      rw [LabeledCographTree.mapLabels_substitute]
      apply LabeledCographTree.substitute_congr
      intro v hv
      rw [I.bags_eq]
      exact congrArg (fun a : Fin n => s.bags[a.val])
        (liveLift_val s keep hk v (hlive v ((hcover v).mp hv)))
    exact hsub.trans ((contract_kept_bag s vertices keep tree).symm.trans
      (congrArg (fun a : Fin n => (ModuleExecution.contract s vertices keep tree).value.bags[a.val]) hr.symm))
  · have hother : (e.symm r).val≠k := fun he => hr (hraw.symm.trans (congrArg Subtype.val he))
    rw [BoundaryPartition.moduleExprUpdate,if_neg hother,I.bags_eq,
      contract_other_bag s vertices keep tree r.val hr]
    rfl

end HiddenCircuits.DH.ModuleExecution
