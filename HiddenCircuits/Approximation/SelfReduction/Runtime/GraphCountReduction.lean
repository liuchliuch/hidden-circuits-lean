import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidualMathematics
import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualReduction
import HiddenCircuits.Approximation.SelfReduction.MatchingStates

/-! Dense ordinary graph self-reduction. Only legal edges have active children;
rejection keeps its remaining depth and count zero. The graph class is solely an
analysis invariant and no recognizer or class certificate is runtime input. -/
namespace HiddenCircuits.Approximation.SelfReduction.GraphCount
open Complexity Runtime.GraphResidual
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def State (b : ℕ) := Σd : ℕ,Option {G : MatrixGraph (2*d) // 2*d ≤ b+1}
def rank {b : ℕ} (s : State b) : ℕ := s.1
noncomputable def count {b : ℕ} (s : State b) : ℕ :=
  match s.2 with | none => 0 | some G => perfectMatchingCount G.val.graph
noncomputable def child {b : ℕ} : State b → Fin (b+1) → State b
  | ⟨0,_⟩,_ => ⟨0,none⟩
  | ⟨d+1,none⟩,_ => ⟨d,none⟩
  | ⟨d+1,some G⟩,j =>
      if hj:j.val < 2*(d+1) then
        if ha:G.val.graph.Adj 0 ⟨j.val,hj⟩ then
          ⟨d,some ⟨evenGraph G.val ⟨j.val,hj⟩ ha.ne.symm,by have h:=G.property;omega⟩⟩
        else ⟨d,none⟩
      else ⟨d,none⟩

@[simp] lemma count_rejected (b d : ℕ) : count (b:=b) ⟨d,none⟩=0 := rfl
@[simp] lemma count_active {b d : ℕ} (G : MatrixGraph (2*d)) (hG : 2*d ≤ b+1) :
    count (b:=b) ⟨d,some ⟨G,hG⟩⟩=perfectMatchingCount G.graph := rfl
@[simp] lemma count_empty {b : ℕ} (G : MatrixGraph (2*0)) :
    count (b:=b) ⟨0,some ⟨G,by omega⟩⟩=1 := by
  letI : IsEmpty (Fin (2*0)) := ⟨fun i => by have h:=i.isLt;omega⟩
  exact perfectMatchingCount_empty_vertices G.graph

lemma leaf_count {b : ℕ} (s : State b) (h:rank s=0) : count s ≤ 1 := by
  rcases s with ⟨d,G⟩
  change d=0 at h
  subst d
  cases G with
  | none => exact Nat.zero_le 1
  | some G => rw [count_empty]

lemma child_rank {b : ℕ} (s : State b) (j : Fin (b+1)) (h:0 < rank s) :
    rank (child s j)+1=rank s := by
  rcases s with ⟨d,G⟩
  cases d with
  | zero => exact False.elim (Nat.lt_irrefl 0 h)
  | succ d =>
    cases G with
    | none => rfl
    | some G => simp only [child];split_ifs <;> rfl

lemma child_count {b d : ℕ} (G : MatrixGraph (2*(d+1))) (hG:2*(d+1) ≤ b+1) (j : Fin (b+1)) :
    count (child ⟨d+1,some ⟨G,hG⟩⟩ j)=
      if hj:j.val < 2*(d+1) then matchingChildCount G.graph 0 ⟨j.val,hj⟩ else 0 := by
  simp only [child]
  split_ifs with hj ha
  · simp only [count_active,matchingChildCount_eq_fiber]
    simpa only [Fintype.card_eq_nat_card] using evenGraph_count_fiber G ⟨j.val,hj⟩ ha
  · simp [matchingChildCount,ha]
  · rfl

lemma child_legal {b d : ℕ} (G : MatrixGraph (2*(d+1))) (hG:2*(d+1) ≤ b+1)
    (j : Fin (b+1)) (hj:j.val < 2*(d+1)) (ha:G.graph.Adj 0 ⟨j.val,hj⟩) :
    child ⟨d+1,some ⟨G,hG⟩⟩ j=⟨d,some ⟨evenGraph G ⟨j.val,hj⟩ ha.ne.symm,by omega⟩⟩ := by
  simp only [child,dif_pos hj,dif_pos ha]

lemma positive_child_legal {b d : ℕ} (G : MatrixGraph (2*(d+1))) (hG:2*(d+1) ≤ b+1)
    (j : Fin (b+1)) (h:0 < count (child ⟨d+1,some ⟨G,hG⟩⟩ j)) :
    ∃hj:j.val < 2*(d+1),G.graph.Adj 0 ⟨j.val,hj⟩ := by
  rw [child_count] at h
  split_ifs at h with hj
  · exact ⟨hj,(matchingChildCount_pos G.graph 0 ⟨j.val,hj⟩ h).1⟩
  · omega

lemma recurrence {b : ℕ} (s : State b) (h:0 < rank s) :
    count s=∑j : Fin (b+1),count (child s j) := by
  rcases s with ⟨d,G⟩
  cases d with
  | zero => exact False.elim (Nat.lt_irrefl 0 h)
  | succ d =>
    cases G with
    | none => simp [child]
    | some G =>
      change perfectMatchingCount G.val.graph=∑j : Fin (b+1),count (child ⟨d+1,some ⟨G.val,G.property⟩⟩ j)
      simp only [child_count]
      rw [EndpointResidual.sum_padded (b+1) (2*(d+1)) G.property]
      exact matching_count_sum_all_partners G.val.graph 0

noncomputable def reduction (b : ℕ) : CountReduction (State b) b where
  count:=count
  rank:=rank
  child:=child
  leaf_count:=leaf_count
  child_rank:=child_rank
  recurrence:=recurrence

def stateBytes {b : ℕ} (s : State b) : BitString :=
  match s.2 with | none => [] | some G => GraphInput.encode ⟨2*s.1,G.val⟩
@[simp] lemma stateBytes_rejected (b d : ℕ) : stateBytes (b:=b) ⟨d,none⟩=[] := rfl
@[simp] lemma stateBytes_active {b d : ℕ} (G : MatrixGraph (2*d)) (hG:2*d ≤ b+1) :
    stateBytes (b:=b) ⟨d,some ⟨G,hG⟩⟩=GraphInput.encode ⟨2*d,G⟩ := rfl
lemma stateBytes_count {b : ℕ} (s : State b) : GraphInput.perfectMatchingProblem (stateBytes s)=count s := by
  rcases s with ⟨d,G⟩
  cases G with
  | none => rfl
  | some G => simp [stateBytes,GraphInput.perfectMatchingProblem,GraphInput.decode_encode,count]

def promised {b : ℕ} (s : State b) : Prop :=
  match s.2 with | none => True | some G => Quasimonotone G.val.graph
lemma child_promised {b : ℕ} (s : State b) (hs:promised s) (j:Fin (b+1)) : promised (child s j) := by
  rcases s with ⟨d,G⟩
  cases d with
  | zero => trivial
  | succ d =>
    cases G with
    | none => trivial
    | some G =>
      simp only [child]
      split_ifs with hj ha
      · exact evenGraph_quasimonotone G.val ⟨j.val,hj⟩ ha.ne.symm hs
      · trivial
      · trivial
end HiddenCircuits.Approximation.SelfReduction.GraphCount
