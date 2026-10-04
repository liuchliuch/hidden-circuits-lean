import HiddenCircuits.DH.Decomposition
import HiddenCircuits.DH.Preprocessing

/-! A deterministic, exhaustive ordinary-input pruning implementation.
This file makes no linear-time graph-processing claim; that requires the separate trie refinement. -/
namespace HiddenCircuits.DH
universe u
open scoped BigOperators

/-- A deterministic scan returns a witness only after testing its predicate. -/
def findWitness {A : Type*} (P : A → Prop) [DecidablePred P] : List A → Option {a // P a}
  | [] => none
  | a :: as => if h : P a then some ⟨a,h⟩ else findWitness P as

lemma findWitness_none_iff {A : Type*} (P : A → Prop) [DecidablePred P] (as : List A) :
    findWitness P as = none ↔ ∀ a ∈ as, ¬P a := by
  induction as with
  | nil => simp [findWitness]
  | cons a as ih =>
    by_cases h : P a <;> simp [findWitness,h,ih]

variable {R : Type u} [Fintype R] [LinearOrder R] (H : SimpleGraph R) [DecidableRel H.Adj]

instance decidableTwinPair (u v : R) : Decidable (TwinPair H u v) :=
  decidable_of_iff (u ≠ v ∧ ∀ x, x ≠ u → x ≠ v → (H.Adj v x ↔ H.Adj u x))
    ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.distinct,h.external⟩⟩

instance decidablePendantPair (u v : R) : Decidable (PendantPair H u v) :=
  decidable_of_iff (H.Adj v u ∧ ∀ x, H.Adj v x → x = u)
    ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.adjacent,h.unique⟩⟩

/-- A checked deletion action on the ordinary current graph. -/
inductive PruneAction (H : SimpleGraph R) where
  | isolated (u : R) (hu : ∀ r, ¬H.Adj u r)
  | falseTwin (u v : R) (ht : TwinPair H u v) (ha : ¬H.Adj u v)
  | trueTwin (u v : R) (ht : TwinPair H u v) (ha : H.Adj u v)
  | pendant (u v : R) (hp : PendantPair H u v)

namespace PruneAction
variable {H}
def deleted : PruneAction H → R
  | .isolated u _ => u
  | .falseTwin _ v _ _ | .trueTwin _ v _ _ | .pendant _ v _ => v

def extend (a : PruneAction H) (next : PruneSequence (H.induce {r | r ≠ a.deleted})) :
    PruneSequence H :=
  match a with
  | .isolated u hu => .isolated u hu next
  | .falseTwin u v ht ha => .falseTwin u v ht ha next
  | .trueTwin u v ht ha => .trueTwin u v ht ha next
  | .pendant u v hp => .pendant u v hp next
end PruneAction

/-- A finite deterministic vertex enumeration taken directly from the input vertex type. -/
def vertexList : List R := (Finset.univ : Finset R).sort (· ≤ ·)

def pairList : List (R × R) :=
  (vertexList (R := R)).flatMap (fun u => (vertexList (R := R)).map (fun v => (u,v)))

lemma mem_vertexList (u : R) : u ∈ vertexList (R := R) := by simp [vertexList]

lemma mem_pairList (u v : R) : (u,v) ∈ pairList (R := R) := by
  exact List.mem_flatMap.mpr ⟨u,mem_vertexList u,List.mem_map.mpr ⟨v,mem_vertexList v,rfl⟩⟩

/-- Search the current adjacency relation for an isolated vertex, then pendant pair, then twins. -/
def findAction : Option (PruneAction H) :=
  match findWitness (fun u : R => ∀ r, ¬H.Adj u r) (vertexList (R := R)) with
  | some u => some (.isolated u.val u.property)
  | none =>
    match findWitness (fun uv : R × R => PendantPair H uv.1 uv.2) (pairList (R := R)) with
    | some uv => some (.pendant uv.val.1 uv.val.2 uv.property)
    | none =>
      match findWitness (fun uv : R × R => TwinPair H uv.1 uv.2) (pairList (R := R)) with
      | none => none
      | some uv => if ha : H.Adj uv.val.1 uv.val.2 then
          some (.trueTwin uv.val.1 uv.val.2 uv.property ha)
        else some (.falseTwin uv.val.1 uv.val.2 uv.property ha)

/-- The exhaustive scan finds a deletion whenever any of its graph-semantic cases exists. -/
theorem findAction_complete
    (h : (∃ u : R, ∀ r, ¬H.Adj u r) ∨
      (∃ u v : R, PendantPair H u v) ∨ (∃ u v : R, TwinPair H u v)) :
    ∃ a, findAction H = some a := by
  cases h0 : findWitness (fun u : R => ∀ r, ¬H.Adj u r) (vertexList (R := R)) with
  | some u => exact ⟨.isolated u.val u.property,by simp [findAction,h0]⟩
  | none =>
    cases h1 : findWitness (fun uv : R × R => PendantPair H uv.1 uv.2) (pairList (R := R)) with
    | some uv => exact ⟨.pendant uv.val.1 uv.val.2 uv.property,by simp [findAction,h0,h1]⟩
    | none =>
      cases h2 : findWitness (fun uv : R × R => TwinPair H uv.1 uv.2) (pairList (R := R)) with
      | some uv =>
        by_cases ha : H.Adj uv.val.1 uv.val.2
        · exact ⟨.trueTwin uv.val.1 uv.val.2 uv.property ha,by simp [findAction,h0,h1,h2,ha]⟩
        · exact ⟨.falseTwin uv.val.1 uv.val.2 uv.property ha,by simp [findAction,h0,h1,h2,ha]⟩
      | none =>
        exfalso
        rcases h with ⟨u,hu⟩ | ⟨u,v,hp⟩ | ⟨u,v,ht⟩
        · exact (findWitness_none_iff _ _).mp h0 u (mem_vertexList u) hu
        · exact (findWitness_none_iff _ _).mp h1 (u,v) (mem_pairList u v) hp
        · exact (findWitness_none_iff _ _).mp h2 (u,v) (mem_pairList u v) ht

/-- Fuel decreases on every deletion, while the actual graph is restricted to surviving vertices. -/
def searchPruning : (fuel : ℕ) → {R : Type u} → [Fintype R] → [LinearOrder R] →
    (H : SimpleGraph R) → [DecidableRel H.Adj] → Option (PruneSequence H)
  | 0, R, _, _, H, _ =>
    if he : (Finset.univ : Finset R).Nonempty then none
    else some (.done ⟨fun r => he ⟨r,Finset.mem_univ r⟩⟩)
  | n+1, R, _, _, H, _ =>
    if he : (Finset.univ : Finset R).Nonempty then
      match findAction H with
      | none => none
      | some a => (searchPruning n (H.induce {r | r ≠ a.deleted})).map a.extend
    else some (.done ⟨fun r => he ⟨r,Finset.mem_univ r⟩⟩)

/-- The executable ordinary-input matching counter. No pruning witness is an input. -/
def countByPruning : Option ℤ :=
  (searchPruning (Fintype.card R) H).map (fun s => (BagForest.execute s.forest).value)

/-- Every successful return is the exact actual perfect-matching count, on any input graph. -/
theorem countByPruning_sound {z : ℤ} (h : countByPruning H = some z) :
    z = (perfectMatchingCount H : ℤ) := by
  obtain ⟨s,hs,hz⟩ := Option.map_eq_some_iff.mp h
  rw [← hz]
  exact (s.execute_spec).1

/-- Apply the connected semantic reduction theorem to an actual component, including isolated vertices. -/
theorem DistanceHereditaryGraph.exists_deletion_cases (hG : DistanceHereditaryGraph H)
    (hne : (Finset.univ : Finset R).Nonempty) :
    (∃ u : R, ∀ r, ¬H.Adj u r) ∨
      (∃ u v : R, PendantPair H u v) ∨ (∃ u v : R, TwinPair H u v) := by
  classical
  obtain ⟨r,hr⟩ := hne
  let C := H.connectedComponentMk r
  have hrC : r ∈ C.supp := by simp [C,SimpleGraph.ConnectedComponent.mem_supp_iff]
  by_cases hnontriv : C.supp.Nontrivial
  · letI : Nontrivial C.supp := by
      obtain ⟨a,ha,b,hb,hab⟩ := hnontriv
      exact ⟨⟨⟨a,ha⟩,⟨b,hb⟩,fun he => hab (congrArg Subtype.val he)⟩⟩
    obtain ⟨u,v,hp | ht⟩ := (hG.induce C.supp).exists_pendant_or_twins C.connected_toSimpleGraph
    · refine Or.inr (Or.inl ⟨u.val,v.val,hp.adjacent,?_⟩)
      intro x hvx
      have hx : x ∈ C.supp := C.mem_supp_of_adj_mem_supp v.property hvx
      exact congrArg Subtype.val (hp.unique ⟨x,hx⟩ hvx)
    · have hm : GraphModule H C.supp := by
        intro a ha b hb x hx
        constructor
        · intro hax
          exact (hx (C.mem_supp_of_adj_mem_supp ha hax)).elim
        · intro hbx
          exact (hx (C.mem_supp_of_adj_mem_supp hb hbx)).elim
      exact Or.inr (Or.inr ⟨u.val,v.val,ht.of_induce_module hm⟩)
  · have hs : C.supp.Subsingleton := Set.not_nontrivial_iff.mp hnontriv
    refine Or.inl ⟨r,?_⟩
    intro x hrx
    exact hrx.ne (hs hrC (C.mem_supp_of_adj_mem_supp hrC hrx))

/-- Deleting the chosen representative strictly reduces the finite vertex count. -/
lemma card_delete_le (v : R) (n : ℕ) (hn : Fintype.card R ≤ n+1) :
    Fintype.card {r : R // r ≠ v} ≤ n := by
  rw [Fintype.card_subtype_compl (fun r : R => r=v),Fintype.card_subtype_eq]
  omega

/-- The executable ordinary-input search succeeds for every semantic DH graph.
The proof uses the proved graph reduction theorem, never a supplied pruning witness. -/
theorem searchPruning_complete (fuel : ℕ) (hG : DistanceHereditaryGraph H)
    (hn : Fintype.card R ≤ fuel) : ∃ s, searchPruning fuel H = some s := by
  induction fuel generalizing R with
  | zero =>
    have hempty : ¬(Finset.univ : Finset R).Nonempty := by
      intro hne
      obtain ⟨r,_⟩ := hne
      have hp : 0 < Fintype.card R := Fintype.card_pos_iff.mpr ⟨r⟩
      omega
    exact ⟨.done ⟨fun r => hempty ⟨r,Finset.mem_univ r⟩⟩,by simp [searchPruning,hempty]⟩
  | succ n ih =>
    by_cases hne : (Finset.univ : Finset R).Nonempty
    · obtain ⟨a,ha⟩ := findAction_complete H (hG.exists_deletion_cases H hne)
      obtain ⟨s,hs⟩ := ih (H := H.induce {r | r ≠ a.deleted})
        (hG.induce _) (card_delete_le a.deleted n hn)
      exact ⟨a.extend s,by simp [searchPruning,hne,ha,hs]⟩
    · exact ⟨.done ⟨fun r => hne ⟨r,Finset.mem_univ r⟩⟩,by simp [searchPruning,hne]⟩

/-- Exact perfect-matching counting from the ordinary graph alone, with exhaustive preprocessing. -/
theorem countByPruning_complete (hG : DistanceHereditaryGraph H) :
    countByPruning H = some (perfectMatchingCount H : ℤ) := by
  obtain ⟨s,hs⟩ := searchPruning_complete H (Fintype.card R) hG le_rfl
  unfold countByPruning
  rw [hs,Option.map_some,(s.execute_spec).1]

/-- The decomposition produced by the actual ordinary-input search feeds the verified
quadratic-arithmetic, bounded-integer evaluator. Its graph-search cost is separate. -/
theorem ordinary_input_arithmetic_spec (hG : DistanceHereditaryGraph H) :
    ∃ s, searchPruning (Fintype.card R) H = some s ∧
      (BagForest.execute s.forest).value = (perfectMatchingCount H : ℤ) ∧
      (BagForest.execute s.forest).operations ≤ 36*(Fintype.card R).choose 2+Fintype.card R ∧
      ExecutionBits.ForestProperty (fun z => z.natAbs.size ≤
        (3*Fintype.card R+3)*(Fintype.card R+1).size+2) s.forest := by
  obtain ⟨s,hs⟩ := searchPruning_complete H (Fintype.card R) hG le_rfl
  exact ⟨s,hs,s.execute_spec⟩

end HiddenCircuits.DH
