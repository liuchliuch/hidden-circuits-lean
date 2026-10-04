import HiddenCircuits.Approximation.SelfReduction.Branches
import HiddenCircuits.Approximation.SamplerRuntime.EndpointFiber
import HiddenCircuits.GraphReduction.MonotoneEndpointEncoding

/-! Canonical endpoint self-reduction with a fixed original branch cap.
Rejected or padded candidates remain explicit zero states at their true depth;
they are never confused with the active empty endpoint instance of count one. -/
namespace HiddenCircuits.Approximation.SelfReduction.EndpointResidual
open GraphReduction SamplerRuntime.EndpointFiber
open scoped BigOperators

def State (b : ℕ) := Σ d : ℕ, Option {E : MonotoneEndpoints d // d ≤ b+1}
def rank {b : ℕ} (s : State b) : ℕ := s.1
noncomputable def count {b : ℕ} (s : State b) : ℕ :=
  match s.2 with | none => 0 | some E => Fintype.card E.val.Permutations

def child {b : ℕ} : State b  →  Fin (b+1)  →  State b
  | ⟨0,_⟩,_ => ⟨0,none⟩
  | ⟨d+1,none⟩,_ => ⟨d,none⟩
  | ⟨d+1,some E⟩,j =>
      if hj : j.val<d+1 then
        if E.val.lo 0 ≤ j.val ∧ j.val<E.val.hi 0 then
          ⟨d,some ⟨deleteFirst E.val ⟨j.val,hj⟩,by have h := E.property;omega⟩⟩
        else ⟨d,none⟩
      else ⟨d,none⟩

@[simp] theorem count_rejected (b d : ℕ) : count (b:=b) ⟨d,none⟩=0 := rfl
@[simp] theorem count_active {b d : ℕ} (E : MonotoneEndpoints d) (h : d ≤ b+1) :
    count (b:=b) ⟨d,some ⟨E,h⟩⟩=Fintype.card E.Permutations := rfl
@[simp] theorem count_empty {b : ℕ} (E : MonotoneEndpoints 0) :
    count (b:=b) ⟨0,some ⟨E,by omega⟩⟩=1 := SamplerRuntime.EndpointFiber.count_empty E

lemma leaf_count {b : ℕ} (s : State b) (h : rank s=0) : count s ≤ 1 := by
  rcases s with ⟨d,E⟩
  change d=0 at h
  subst d
  cases E with
  | none => simp
  | some E => rw [count_active,SamplerRuntime.EndpointFiber.count_empty]

lemma child_rank {b : ℕ} (s : State b) (j : Fin (b+1)) (h : 0<rank s) :
    rank (child s j)+1=rank s := by
  rcases s with ⟨d,E⟩
  cases d with
  | zero => simp [rank] at h
  | succ d =>
    cases E with
    | none => rfl
    | some E => simp only [child];split_ifs <;> rfl

lemma sum_padded (N m : ℕ) (hm : m ≤ N) (f : Fin m → ℕ) :
    (∑i : Fin N,if h : i.val < m then f ⟨i.val,h⟩ else 0)=∑i : Fin m,f i := by
  induction N with
  | zero =>
    have h : m=0 := by omega
    subst m
    simp
  | succ N ih =>
    by_cases he : m=N+1
    · subst m
      simp only [Fin.isLt,dif_pos]
    · have hm' : m ≤ N := by omega
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last]
      rw [dif_neg (by omega : ¬N < m),Nat.add_zero]
      exact ih hm'

lemma child_count {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1 ≤ b+1) (j : Fin (b+1)) :
    count (child ⟨d+1,some ⟨E,hE⟩⟩ j)=
      if hj : j.val<d+1 then
        if E.lo 0 ≤ j.val ∧ j.val<E.hi 0 then Fintype.card (deleteFirst E ⟨j.val,hj⟩).Permutations else 0
      else 0 := by
  simp only [child]
  split_ifs <;> rfl


/-- The exact active child selected by an in-range allowed column. -/
theorem child_legal {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1 ≤ b+1)
    (j : Fin (b+1)) (hj : j.val<d+1) (ha : E.lo 0 ≤ j.val ∧ j.val<E.hi 0) :
    child ⟨d+1,some ⟨E,hE⟩⟩ j=
      ⟨d,some ⟨deleteFirst E ⟨j.val,hj⟩,by omega⟩⟩ := by
  simp only [child,dif_pos hj,if_pos ha]

/-- A concrete endpoint permutation supplies a positive completion count for
its observed row-zero partner. -/
theorem observed_child_positive {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1 ≤ b+1)
    (P : E.Permutations) :
    let j : Fin (b+1) := ⟨(P.val 0).val,lt_of_lt_of_le (P.val 0).isLt hE⟩
    0<count (child ⟨d+1,some ⟨E,hE⟩⟩ j) := by
  dsimp only
  rw [child_count,dif_pos (P.val 0).isLt,if_pos (P.property 0)]
  apply Fintype.card_pos_iff.mpr
  exact ⟨SamplerRuntime.EndpointFiber.restrict E (P.val 0) ⟨P,rfl⟩⟩

lemma recurrence {b : ℕ} (s : State b) (h : 0<rank s) :
    count s=∑j : Fin (b+1),count (child s j) := by
  rcases s with ⟨d,E⟩
  cases d with
  | zero => simp [rank] at h
  | succ d =>
    cases E with
    | none => simp [child]
    | some E =>
      change Fintype.card E.val.Permutations=∑j : Fin (b+1),count (child ⟨d+1,some ⟨E.val,E.property⟩⟩ j)
      simp only [child_count]
      have hpad := sum_padded (b+1) (d+1) E.property
        (fun j : Fin (d+1) => if E.val.lo 0 ≤ j.val ∧ j.val<E.val.hi 0 then
          Fintype.card (deleteFirst E.val j).Permutations else 0)
      rw [hpad]
      exact SamplerRuntime.EndpointFiber.count_recurrence E.val

noncomputable def reduction (b : ℕ) : CountReduction (State b) b where
  count := count
  rank := rank
  child := child
  leaf_count := leaf_count
  child_rank := child_rank
  recurrence := recurrence


/-- Rejected states have invalid empty bytes, whereas active dimension-zero
states retain the canonical three-field encoding. -/
def stateBytes {b : ℕ} (s : State b) : Complexity.BitString :=
  match s.2 with | none => [] | some E => MonotoneEndpointEncoding.encode ⟨s.1,E.val⟩

@[simp] theorem stateBytes_rejected (b d : ℕ) : stateBytes (b:=b) ⟨d,none⟩=[] := rfl
@[simp] theorem stateBytes_active {b d : ℕ} (E : MonotoneEndpoints d) (hE : d ≤ b+1) :
    stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩=MonotoneEndpointEncoding.encode ⟨d,E⟩ := rfl

theorem stateBytes_count {b : ℕ} (s : State b) : MonotoneEndpointEncoding.count (stateBytes s)=count s := by
  rcases s with ⟨d,E⟩
  cases E with
  | none => simp [stateBytes,MonotoneEndpointEncoding.count,MonotoneEndpointEncoding.decode,Complexity.decodeBitList,Complexity.decodeBitListFuel]
  | some E => exact MonotoneEndpointEncoding.count_encode ⟨d,E.val⟩

/-- A positive-count child cannot be padding or a forbidden row-zero choice. -/
theorem positive_child_legal {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1 ≤ b+1)
    (j : Fin (b+1)) (hpos : 0<count (child ⟨d+1,some ⟨E,hE⟩⟩ j)) :
    j.val<d+1 ∧ E.lo 0 ≤ j.val ∧ j.val<E.hi 0 := by
  rw [child_count] at hpos
  split_ifs at hpos with hdim hlegal
  · exact ⟨hdim,hlegal⟩
  · omega
  · omega

/-- An actual sample of this partner proves legality without needing an
extra runtime adjacency certificate. -/
theorem observed_partner_legal {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1 ≤ b+1)
    (P : E.Permutations) :
    let j : Fin (b+1) := ⟨(P.val 0).val,lt_of_lt_of_le (P.val 0).isLt hE⟩
    j.val<d+1 ∧ E.lo 0 ≤ j.val ∧ j.val<E.hi 0 := by
  exact ⟨(P.val 0).isLt,P.property 0⟩
end HiddenCircuits.Approximation.SelfReduction.EndpointResidual
