import HiddenCircuits.DH.Runtime.PruningModel

/-! The fixed-label exhaustive scan always produces checked actions, and its
input-sized iteration reaches an edgeless mask on actual DH input. -/
namespace HiddenCircuits.DH.Runtime.PruningModel
open SimpleGraph

def graph {n : ℕ} (G : SimpleGraph (Fin n)) (alive : Vector Bool n) :
    SimpleGraph {v : Fin n // alive[v.val]=true} := G.induce {v : Fin n | alive[v.val]=true}

lemma valid_of_pendant {n : ℕ} (G : SimpleGraph (Fin n)) (alive : Vector Bool n)
    (u v : {v : Fin n // alive[v.val]=true}) (hp : PendantPair (graph G alive) u v) :
    Valid G alive ⟨u.val,v.val,.pendant⟩ := by
  refine ⟨u.property,v.property,?_,hp.adjacent,?_⟩
  · exact fun he=>hp.adjacent.ne (Subtype.ext he.symm)
  · intro x hx hvx
    exact congrArg Subtype.val (hp.unique ⟨x,hx⟩ hvx)

lemma twin_test_of_pair {n : ℕ} (G : SimpleGraph (Fin n)) (alive : Vector Bool n)
    (u v : {v : Fin n // alive[v.val]=true}) (ht : TwinPair (graph G alive) u v) :
    alive[u.val.val]=true ∧ alive[v.val.val]=true ∧ u.val≠v.val ∧
      ∀x, alive[x.val]=true → x≠u.val → x≠v.val → (G.Adj v.val x ↔ G.Adj u.val x) := by
  refine ⟨u.property,v.property,fun he=>ht.distinct (Subtype.ext he),?_⟩
  intro x hx hxu hxv
  exact ht.external ⟨x,hx⟩ (fun he=>hxu (congrArg Subtype.val he)) (fun he=>hxv (congrArg Subtype.val he))

lemma pair_exists_of_edge {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : DistanceHereditaryGraph G) {a b : V} (hab : G.Adj a b) :
    ∃u v, PendantPair G u v ∨ TwinPair G u v := by
  let C := G.connectedComponentMk a
  have ha : a∈C.supp := by simp [C,ConnectedComponent.mem_supp_iff]
  have hb : b∈C.supp := C.mem_supp_of_adj_mem_supp ha hab
  letI : Nontrivial C.supp := ⟨⟨⟨a,ha⟩,⟨b,hb⟩,fun he=>hab.ne (congrArg Subtype.val he)⟩⟩
  obtain ⟨u,v,hp | ht⟩ := (hG.induce C.supp).exists_pendant_or_twins C.connected_toSimpleGraph
  · refine ⟨u.val,v.val,Or.inl ⟨hp.adjacent,?_⟩⟩
    intro x hvx
    have hx : x∈C.supp := C.mem_supp_of_adj_mem_supp v.property hvx
    exact congrArg Subtype.val (hp.unique ⟨x,hx⟩ hvx)
  · have hm : GraphModule G C.supp := by
      intro u hu v hv x hx
      exact iff_of_false (fun h=>hx (C.mem_supp_of_adj_mem_supp hu h))
        (fun h=>hx (C.mem_supp_of_adj_mem_supp hv h))
    exact ⟨u.val,v.val,Or.inr (ht.of_induce_module hm)⟩

/-- Failure of the exhaustive pair scan on DH input means that no live edge
remains. This is a consequence of the semantic pruning theorem. -/
theorem find_none_edgeless {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : DistanceHereditaryGraph G) (alive : Vector Bool n) (h : find G alive=none) :
    ∀u v : {v : Fin n // alive[v.val]=true}, ¬(graph G alive).Adj u v := by
  intro u v huv
  obtain ⟨a,b,hp | ht⟩ := pair_exists_of_edge (graph G alive) (hG.induce _) huv
  · obtain ⟨act,hact⟩ := tryPair_exists_of_pendant G alive a.val b.val (valid_of_pendant G alive a b hp)
    have he := (find_none G alive).mp h a.val b.val
    rw [hact] at he
    contradiction
  · obtain ⟨act,hact⟩ := tryPair_exists_of_twin G alive a.val b.val (twin_test_of_pair G alive a b ht)
    have he := (find_none G alive).mp h a.val b.val
    rw [hact] at he
    contradiction

def liveCount {n : ℕ} (alive : Vector Bool n) : ℕ :=
  (Finset.univ.filter (fun v : Fin n=>alive[v.val]=true)).card

lemma remove_count {n : ℕ} (alive : Vector Bool n) (a : Action n) (hv : alive[a.removed.val]=true) :
    liveCount (remove alive a)+1=liveCount alive := by
  let S := Finset.univ.filter (fun v : Fin n=>alive[v.val]=true)
  have hm : a.removed∈S := by simp [S,hv]
  have he : Finset.univ.filter (fun v : Fin n=>(remove alive a)[v.val]=true)=S.erase a.removed := by
    ext v
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,remove_alive,Finset.mem_erase]
    tauto
  unfold liveCount
  rw [he]
  exact Finset.card_erase_add_one hm

lemma liveCount_le {n : ℕ} (alive : Vector Bool n) : liveCount alive≤n := by
  have h := Finset.card_le_card (Finset.filter_subset (fun v : Fin n=>alive[v.val]=true) Finset.univ)
  simpa [liveCount] using h

inductive Trace {n : ℕ} (G : SimpleGraph (Fin n)) : Vector Bool n→List (Action n)→Vector Bool n→Prop
  | nil (alive) : Trace G alive [] alive
  | cons {alive final : Vector Bool n} {a : Action n} {as : List (Action n)}
      (valid : Valid G alive a) (rest : Trace G (remove alive a) as final) : Trace G alive (a::as) final

lemma run_trace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (fuel : ℕ) (alive : Vector Bool n) : Trace G alive (run G fuel alive).actions (run G fuel alive).alive := by
  induction fuel generalizing alive with
  | zero => exact .nil alive
  | succ fuel ih =>
    cases he : find G alive with
    | none => simpa only [run,he] using Trace.nil (G:=G) alive
    | some a => simpa only [run,he] using Trace.cons (find_valid G alive he) (ih (remove alive a))

/-- The schedule length is bounded on every graph; actual DH input additionally
finishes with an edgeless live graph after at most the input vertex count. -/
theorem run_edgeless {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : DistanceHereditaryGraph G) (fuel : ℕ) (alive : Vector Bool n) (hf : liveCount alive≤fuel) :
    ∀u v : {v : Fin n // (run G fuel alive).alive[v.val]=true},
      ¬(graph G (run G fuel alive).alive).Adj u v := by
  induction fuel generalizing alive with
  | zero =>
    intro u v huv
    have hm : u.val∈Finset.univ.filter (fun v : Fin n=>alive[v.val]=true) := by
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact u.property
    have hc := Finset.card_pos.mpr ⟨u.val,hm⟩
    change liveCount alive>0 at hc
    omega
  | succ fuel ih =>
    simp only [run]
    split
    · rename_i he
      exact find_none_edgeless G hG alive he
    · rename_i a he
      have hv := (find_valid G alive he).2.1
      have hc := remove_count alive a hv
      exact ih (remove alive a) (by omega)

end HiddenCircuits.DH.Runtime.PruningModel
