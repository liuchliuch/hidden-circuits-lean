import HiddenCircuits.ExactSampling.DHIndex
import HiddenCircuits.Complexity.BitList

/-! An explicit compact matching representation. Each entry gives the selected
partner of the least remaining vertex in the inherited ordering. Decoding uses
only pair deletions and edge insertion; it does not use matching counts. -/
namespace HiddenCircuits.ExactSampling.DHPaths
open Complexity DH Approximation Approximation.SelfReduction
open Approximation.SelfReduction.Runtime DHWeights DHIndex

/-- A count-free decoder to actual original-labeled perfect matchings. -/
noncomputable def decode : (xs : List ℕ) → (n : ℕ) → (G : MatrixGraph n) → Option (PerfectPartner G.graph)
  | [],0,G => some (emptyPartner G)
  | [],_+1,_ => none
  | _::_,0,_ => none
  | j::js,N+1,G =>
    if hj : j<N+1 then
      if ha : G.graph.Adj 0 ⟨j,hj⟩ then
        (decode js _ (GraphResidual.graph G ⟨j,hj⟩)).map
          (fun p => ((edgeDeletionEquiv ha).symm (partnerIso (GraphResidual.graphIso G ⟨j,hj⟩) p)).val)
      else none
    else none

 theorem weight_selected {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (x : Fin (count ⟨N+1,G⟩)) :
    weight G (splitIndex G hG x).1=count ⟨_,GraphResidual.graph G (splitIndex G hG x).1⟩ := by
  unfold weight
  have he : G.edge 0 (splitIndex G hG x).1=true := selected_edge G hG x
  split_ifs with h
  · rfl
  · exact (h he).elim

 def residualRank {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (x : Fin (count ⟨N+1,G⟩)) :
    Fin (count ⟨_,GraphResidual.graph G (splitIndex G hG x).1⟩) :=
  Fin.cast (weight_selected G hG x) (splitIndex G hG x).2

/-- The physically emitted local-vertex choices of the recursive interval scan. -/
noncomputable def choices : (n : ℕ) → (G : MatrixGraph n) →
    (hG : DistanceHereditaryGraph G.graph) → Fin (count ⟨n,G⟩) → List ℕ
  | 0,_,_,_ => []
  | N+1,G,hG,x =>
    (splitIndex G hG x).1.val :: choices _ (GraphResidual.graph G (splitIndex G hG x).1)
      (residual_hereditary G hG _) (residualRank G hG x)
termination_by n => n
decreasing_by exact residual_smaller G _ (selected_edge G hG x)

 theorem choices_decode : ∀ (n : ℕ) (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (x : Fin (count ⟨n,G⟩)), decode (choices n G hG x) n G=some (indexEquiv n G hG x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [choices,decode,indexEquiv,emptyIndex]
    | succ N =>
      intro G hG x
      let j := (splitIndex G hG x).1
      have ha : G.graph.Adj 0 j := selected_edge G hG x
      have hl := residual_smaller G j ha
      have hh := ih (GraphResidual.retained j).card hl (GraphResidual.graph G j)
        (residual_hereditary G hG j) (residualRank G hG x)
      simp only [choices,decode]
      rw [dif_pos j.isLt,dif_pos ha]
      rw [hh]
      simp only [Option.map_some,Option.some.injEq]
      simp only [indexEquiv,Equiv.trans_apply,Equiv.sigmaCongrRight_apply]
      rw [dif_pos (selected_edge G hG x)]
      rfl

 theorem choices_injective {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph) :
    Function.Injective (choices n G hG) := by
  intro x y h
  have he := congrArg (fun xs => decode xs n G) h
  dsimp only at he
  rw [choices_decode,choices_decode] at he
  exact (indexEquiv n G hG).injective (Option.some.inj he)

 theorem choices_length_le : ∀ (n : ℕ) (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (x : Fin (count ⟨n,G⟩)), (choices n G hG x).length≤n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => intros;simp [choices]
    | succ N =>
      intro G hG x
      have hl := residual_smaller G _ (selected_edge G hG x)
      have hh := ih _ hl (GraphResidual.graph G (splitIndex G hG x).1)
        (residual_hereditary G hG _) (residualRank G hG x)
      simp only [choices,List.length_cons]
      omega

 theorem choices_entries_lt : ∀ (n : ℕ) (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (x : Fin (count ⟨n,G⟩)) (j : ℕ), j∈choices n G hG x → j<n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => intros;simp [choices] at *
    | succ N =>
      intro G hG x j hj
      simp only [choices,List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact (splitIndex G hG x).1.isLt
      · have hl := residual_smaller G _ (selected_edge G hG x)
        exact (ih _ hl (GraphResidual.graph G (splitIndex G hG x).1)
          (residual_hereditary G hG _) (residualRank G hG x) j hj).trans hl

/-- Self-delimiting unary local indices: output length is polynomial in the
original graph size although matching counts can be exponentially large. -/
def encode (xs : List ℕ) : BitString := encodeBitList (xs.map (fun j => List.replicate j true))

 theorem encode_length_bound (xs : List ℕ) (n : ℕ) (hl : xs.length≤n) (he : ∀j∈xs,j<n) :
    (encode xs).length≤2*n*n+2*n := by
  have hs : (xs.map (fun j => (List.replicate j true).length)).sum≤xs.length*n := by
    induction xs with
    | nil => simp
    | cons j xs ih =>
      have hh : ∀k∈xs,k<n := fun k hk => he k (List.mem_cons_of_mem _ hk)
      have hj := he j (by simp)
      have ht := ih (by simp_all;omega) hh
      simp only [List.map_cons,List.sum_cons,List.length_cons,List.length_replicate]
      simp only [List.length_replicate] at ht
      nlinarith
  rw [encode,encodeBitList_length,List.map_map,List.length_map]
  simp only [Function.comp_def,List.length_replicate] at hs ⊢
  nlinarith

 theorem encoded_choices_length {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (x : Fin (count ⟨n,G⟩)) : (encode (choices n G hG x)).length≤2*n*n+2*n :=
  encode_length_bound _ n (choices_length_le n G hG x) (choices_entries_lt n G hG x)

end HiddenCircuits.ExactSampling.DHPaths
