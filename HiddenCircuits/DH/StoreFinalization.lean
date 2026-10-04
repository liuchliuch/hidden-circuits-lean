import HiddenCircuits.DH.PendantExecution

/-! Linear finalization of the live bag table once all representative edges are gone. -/
namespace HiddenCircuits.DH.ModuleExecution
open SimpleGraph LexBFSPartition

/-- Collect each still-live original representative once, in fixed input-label order. -/
def collectLive {n : ℕ} (alive : Vector Bool n) : List (Fin n) → Counted (List (Fin n))
  | [] => ⟨[],0⟩
  | v::vs =>
      let q := collectLive alive vs
      if alive[v.val] then ⟨v::q.value,q.accesses+2⟩ else ⟨q.value,q.accesses+1⟩

@[simp] lemma collectLive_value {n : ℕ} (alive : Vector Bool n) (vs : List (Fin n)) :
    (collectLive alive vs).value = vs.filter (fun v => alive[v.val]) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    by_cases hv : alive[v.val]=true <;> simp [collectLive,hv,ih]

lemma collectLive_accesses {n : ℕ} (alive : Vector Bool n) (vs : List (Fin n)) :
    (collectLive alive vs).accesses ≤ 2*vs.length := by
  induction vs with
  | nil => simp [collectLive]
  | cons v vs ih => simp only [collectLive,List.length_cons]; split <;> dsimp only <;> omega

/-- A linear explicit cotree for an edgeless set of representative labels. -/
def disjointTree {n : ℕ} (first : Fin n) : List (Fin n) → Counted (LabeledCographTree (Fin n))
  | [] => ⟨.leaf first,1⟩
  | v::vs =>
      let q := disjointTree v vs
      ⟨.node false (.leaf first) q.value,q.accesses+2⟩

@[simp] lemma disjointTree_leaves {n : ℕ} (first : Fin n) (vs : List (Fin n)) :
    (disjointTree first vs).value.leaves = first::vs := by
  induction vs generalizing first with
  | nil => rfl
  | cons v vs ih => simp [disjointTree,LabeledCographTree.leaves,ih]

lemma disjointTree_resources {n : ℕ} (first : Fin n) (vs : List (Fin n)) :
    (disjointTree first vs).accesses = 2*vs.length+1 ∧
      (disjointTree first vs).value.shape.nodes = 2*vs.length+1 := by
  induction vs generalizing first with
  | nil => exact ⟨rfl,rfl⟩
  | cons v vs ih =>
    have h := ih v
    simp only [disjointTree,LabeledCographTree.shape,CographTree.nodes,List.length_cons]
    constructor <;> omega

lemma disjointTree_correct {n : ℕ} (G : SimpleGraph (Fin n)) (first : Fin n) (vs : List (Fin n))
    (hn : ∀ a∈first::vs, ∀ b∈first::vs, ¬G.Adj a b) :
    (disjointTree first vs).value.Correct G := by
  induction vs generalizing first with
  | nil => exact LabeledCographTree.correct_leaf _ _
  | cons v vs ih =>
    apply LabeledCographTree.Correct.node false (LabeledCographTree.correct_leaf _ _)
    · exact ih v (fun a ha b hb => hn a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
    · intro a ha b hb
      have ha' : a=first := by simpa [LabeledCographTree.leaves] using ha
      subst a
      have hb' : b∈v::vs := by simpa only [disjointTree_leaves] using hb
      exact iff_of_false (hn first List.mem_cons_self b (List.mem_cons_of_mem _ hb')) Bool.false_ne_true

/-- Final output is empty on an empty live table; otherwise combine the independent root bags
by the genuine false-twin operation and return one bag expression. -/
def finish {n : ℕ} (s : Store n) : Counted (List BagExpr) :=
  let roots := collectLive s.alive (List.finRange n)
  match roots.value with
  | [] => ⟨[],roots.accesses+n⟩
  | v::vs =>
      let t := disjointTree v vs
      let e := substituteArray s.bags t.value
      ⟨[e.expression],roots.accesses+n+t.accesses+e.accesses+1⟩

lemma finish_accesses {n : ℕ} (s : Store n) : (finish s).accesses ≤ 10*n := by
  have hc := collectLive_accesses s.alive (List.finRange n)
  have hl : (collectLive s.alive (List.finRange n)).value.length ≤ n := by
    rw [collectLive_value]
    simpa using List.length_filter_le (fun v : Fin n => s.alive[v.val]) (List.finRange n)
  simp only [List.length_finRange] at hc
  cases hroots : (collectLive s.alive (List.finRange n)).value with
  | nil => simp only [finish,hroots]; omega
  | cons v vs =>
    have ht := disjointTree_resources v vs
    have he := (substituteArray_resources s.bags (disjointTree v vs).value).1
    rw [hroots,List.length_cons] at hl
    simp only [finish,hroots]
    omega

/-- A singleton bag forest has the same actual graph as its bag. -/
def singletonBagIso (e : BagExpr) : BagForest.graph [e] ≃g e.graph where
  toEquiv :=
    { toFun := Sum.elim id Empty.elim
      invFun := Sum.inl
      left_inv := by intro x; cases x with | inl x => rfl | inr x => exact x.elim
      right_inv := fun _ => rfl }
  map_rel_iff' := by intro a b; cases a <;> cases b <;> first | rfl | contradiction

/-- A fully covered region is the entire original graph, using identity on original vertices. -/
def allRegionIso {n : ℕ} {G : SimpleGraph (Fin n)} {s : Store n} (I : Interpretation G s)
    (t : LabeledCographTree (Live s)) (hcover : ∀ r : Live s, r∈t.leaves) :
    G.induce (I.partition.region t) ≃g G where
  toEquiv :=
    { toFun := Subtype.val
      invFun := fun v => ⟨v,hcover (I.partition.place v)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := by intro a b; rfl

/-- Literal final-array collection plus false-twin assembly yields a graph-isomorphic
bag forest whenever the actual current representative graph has no edges. -/
noncomputable def Interpretation.finishIso {n : ℕ} {G : SimpleGraph (Fin n)} {s : Store n}
    (I : Interpretation G s) (hedge : ∀ a b : Live s, ¬(liveGraph G s).Adj a b) :
    BagForest.graph (finish s).value ≃g G := by
  let roots := (collectLive s.alive (List.finRange n)).value
  have hmem (v : Fin n) : v∈roots ↔ s.alive[v.val]=true := by simp [roots]
  have hnd : roots.Nodup := by
    simpa only [roots,collectLive_value] using (List.nodup_finRange n).filter (fun v => s.alive[v.val])
  cases he : roots with
  | nil =>
    have hempty : IsEmpty (Fin n) := ⟨fun v => by
      have hr := (hmem (I.partition.place v).val).mpr (I.partition.place v).property
      simp [he] at hr⟩
    have hf : (finish s).value=[] := by
      have hroots : (collectLive s.alive (List.finRange n)).value=[] := he
      simp only [finish,hroots]
    rw [hf]
    exact
      { toEquiv :=
          { toFun := Empty.elim
            invFun := fun v => (hempty.false v).elim
            left_inv := by intro v; exact v.elim
            right_inv := by intro v; exact (hempty.false v).elim }
        map_rel_iff' := by intro v; exact v.elim }
  | cons keep rest =>
    have hkeep : s.alive[keep.val]=true := (hmem keep).mp (by simp [he])
    let tree := (disjointTree keep rest).value
    have hlive : ∀ v∈roots, s.alive[v.val]=true := fun v hv => (hmem v).mp hv
    have hcover : ∀ v, v∈tree.leaves ↔ v∈roots := by intro v; simp [tree,he]
    have hn : tree.leaves.Nodup := by simpa [tree,he] using hnd
    have hc : tree.Correct G := by
      apply disjointTree_correct
      intro a ha b hb
      have ha' : s.alive[a.val]=true := (hmem a).mp (by simpa [he] using ha)
      have hb' : s.alive[b.val]=true := (hmem b).mp (by simpa [he] using hb)
      exact hedge ⟨a,ha'⟩ ⟨b,hb'⟩
    let t := tree.mapLabels (liveLift s keep hkeep)
    have htN : t.leaves.Nodup := lifted_nodup s roots keep hkeep tree hlive hcover hn
    have htC : t.Correct (liveGraph G s) := lifted_correct G s roots keep hkeep tree hlive hcover hc
    have htAll : ∀ r : Live s, r∈t.leaves := by
      intro r
      apply (lifted_cover s roots keep hkeep tree hlive hcover r).mpr
      rw [mem_liveModule]
      exact (hmem r.val).mpr r.property
    have hsub : t.substitute I.representation.expr = (substituteArray s.bags tree).expression := by
      rw [substituteArray_expression,LabeledCographTree.mapLabels_substitute]
      apply LabeledCographTree.substitute_congr
      intro v hv
      rw [I.bags_eq]
      exact congrArg (fun a : Fin n => s.bags[a.val])
        (liveLift_val s keep hkeep v (hlive v ((hcover v).mp hv)))
    have hi : (substituteArray s.bags tree).expression.graph ≃g G := by
      rw [← hsub]
      exact (I.partition.substituteIso I.representation t htN htC).trans (allRegionIso I t htAll)
    have hf : (finish s).value=[(substituteArray s.bags tree).expression] := by
      have hroots : (collectLive s.alive (List.finRange n)).value=keep::rest := he
      simp only [finish,hroots]
      rfl
    rw [hf]
    exact (singletonBagIso _).trans hi

/-- The final store interpretation discharges the arithmetic backend's graph-isomorphism
obligation for the actual collected output, including zero vertices. -/
theorem Interpretation.finish_execution_spec {n : ℕ} {G : SimpleGraph (Fin n)} {s : Store n}
    (I : Interpretation G s) (hedge : ∀ a b : Live s, ¬(liveGraph G s).Adj a b) :
    (finish s).accesses ≤ 10*n ∧
    (BagForest.execute (finish s).value).value = (perfectMatchingCount G : ℤ) ∧
    (BagForest.execute (finish s).value).operations ≤ 36*n.choose 2+n ∧
    ExecutionBits.ForestProperty (fun z => z.natAbs.size ≤ (3*n+3)*(n+1).size+2) (finish s).value := by
  exact ⟨finish_accesses s,by simpa only [Fintype.card_fin] using
    ExecutionBits.complete_execution_bit_spec_of_iso (finish s).value G (I.finishIso hedge)⟩

end HiddenCircuits.DH.ModuleExecution
