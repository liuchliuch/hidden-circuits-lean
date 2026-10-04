import HiddenCircuits.DH.LexBFSInput
import HiddenCircuits.DH.LexBFSPartition

/-! Linear output materialization and constant-time compact slice intervals. -/
namespace HiddenCircuits.DH.LexBFSPartition

/-- Three direct arrays suffice: output permutation, inverse ranks, and selected-cell lengths.
A slice stores no list of its members. Its start is its own output position. -/
structure CompactOutput (n : ℕ) where
  order : LexBFSInput.Order n
  sliceLength : Vector ℕ n

/-- Convert the compact event list once, including construction of literal inverse ranks. -/
def materialize {n : ℕ} (events : List (LexBFSModel.Event (Fin n)))
    (hp : (events.map LexBFSModel.Event.vertex).Perm (List.finRange n)) : Counted (CompactOutput n) :=
  let o := LexBFSInput.ofList (events.map LexBFSModel.Event.vertex) hp
  have hlen : events.length=n := by simpa using hp.length_eq
  let lengths : Vector ℕ n := ⟨(events.map LexBFSModel.Event.sliceSize).toArray,by simp [hlen]⟩
  ⟨⟨o.order,lengths⟩,o.accesses+3*n⟩

@[simp] theorem materialize_accesses {n : ℕ} (events : List (LexBFSModel.Event (Fin n)))
    (hp : (events.map LexBFSModel.Event.vertex).Perm (List.finRange n)) :
    (materialize events hp).accesses = 9*n := by simp [materialize]; omega

@[simp] theorem materialize_vertices {n : ℕ} (events : List (LexBFSModel.Event (Fin n)))
    (hp : (events.map LexBFSModel.Event.vertex).Perm (List.finRange n)) :
    (materialize events hp).value.order.vertexAt.toList = events.map LexBFSModel.Event.vertex := by
  simp [materialize]

@[simp] theorem materialize_lengths {n : ℕ} (events : List (LexBFSModel.Event (Fin n)))
    (hp : (events.map LexBFSModel.Event.vertex).Perm (List.finRange n)) :
    (materialize events hp).value.sliceLength.toList = events.map LexBFSModel.Event.sliceSize := by
  simp [materialize]

@[simp] theorem materialize_length_at {n : ℕ} (events : List (LexBFSModel.Event (Fin n)))
    (hp : (events.map LexBFSModel.Event.vertex).Perm (List.finRange n)) (i : Fin n) :
    (materialize events hp).value.sliceLength[i.val] =
      (events[i.val]'(by have hh := hp.length_eq; simp only [List.length_map,List.length_finRange] at hh; omega)).sliceSize := by
  simp [materialize]

/-- This lookup performs exactly one size-array read; positions themselves need no memory lookup. -/
def CompactOutput.slice {n : ℕ} (o : CompactOutput n) (i : Fin n) : Counted (ℕ × ℕ) :=
  let k := o.sliceLength[i.val]
  ⟨(i.val,i.val+k),1⟩

@[simp] theorem slice_accesses {n : ℕ} (o : CompactOutput n) (i : Fin n) :
    (o.slice i).accesses = 1 := rfl

/-- Both permutation directions are literal arrays constructed by the inverse-writing loop. -/
theorem materialize_inverse {n : ℕ} (events : List (LexBFSModel.Event (Fin n)))
    (hp : (events.map LexBFSModel.Event.vertex).Perm (List.finRange n)) :
    let o := (materialize events hp).value
    (∀ i : Fin n, o.order.rankOf[(o.order.vertexAt[i.val]).val]=i) ∧
    (∀ v : Fin n, o.order.vertexAt[(o.order.rankOf[v.val]).val]=v) :=
  ⟨(materialize events hp).value.order.rank_vertex,(materialize events hp).value.order.vertex_rank⟩

end HiddenCircuits.DH.LexBFSPartition

namespace HiddenCircuits.DH.LexBFSModel

lemma SliceCorrect.drop {V : Type*} {prefer : V → V → Bool} {past : List V}
    {events : List (Event V)} (h : SliceCorrect prefer past events) (i : ℕ) :
    SliceCorrect prefer (past++(events.take i).map Event.vertex) (events.drop i) := by
  induction i generalizing past events with
  | zero => simpa using h
  | succ i ih =>
    cases events with
    | nil => trivial
    | cons e es =>
      have ht := ih h.2.2.2
      simpa [List.take_succ_cons,List.drop_succ_cons,List.append_assoc] using ht

/-- Exact bounded interval interpretation at any output index. -/
theorem SliceCorrect.at {V : Type*} {prefer : V → V → Bool} {events : List (Event V)}
    (h : SliceCorrect prefer [] events) (i : ℕ) (hi : i<events.length) :
    0 < events[i].sliceSize ∧ i+events[i].sliceSize ≤ events.length ∧
      ∀ v, v ∈ ((events.map Event.vertex).drop i).take events[i].sliceSize ↔
        v ∈ (events.map Event.vertex).drop i ∧
          SameProfile prefer ((events.take i).map Event.vertex) events[i].vertex v := by
  have ht := h.drop i
  simp only [List.nil_append] at ht
  rw [List.drop_eq_getElem_cons hi] at ht
  refine ⟨ht.1,?_,?_⟩
  · have hb := ht.2.1
    have hl : (events[i]::events.drop (i+1)).length=events.length-i := by
      rw [← List.drop_eq_getElem_cons hi,List.length_drop]
    rw [hl] at hb
    omega
  · intro v
    have hm := ht.2.2.1 v
    simpa only [← List.drop_eq_getElem_cons hi,List.map_drop] using hm

end HiddenCircuits.DH.LexBFSModel

namespace HiddenCircuits.DH.LexBFSPartition

/-- The actual compact array interval is nonempty, lies inside the output array,
and denotes exactly the equal-profile class selected at that position. -/
theorem materialize_slice_correct {n : ℕ} (events : List (LexBFSModel.Event (Fin n)))
    (hp : (events.map LexBFSModel.Event.vertex).Perm (List.finRange n))
    (prefer : Fin n → Fin n → Bool) (hs : LexBFSModel.SliceCorrect prefer [] events) (i : Fin n) :
    let o := (materialize events hp).value
    let range := (o.slice i).value
    range.1 = i.val ∧ range.1 < range.2 ∧ range.2 ≤ n ∧
      ∀ v, v ∈ (o.order.vertexAt.toList.drop range.1).take (range.2-range.1) ↔
        v ∈ o.order.vertexAt.toList.drop i.val ∧
          LexBFSModel.SameProfile prefer ((events.take i.val).map LexBFSModel.Event.vertex)
            (events[i.val]'(by have hh := hp.length_eq; simp only [List.length_map,List.length_finRange] at hh; omega)).vertex v := by
  have hlen : events.length=n := by simpa using hp.length_eq
  have hi : i.val<events.length := by omega
  have hh := hs.at i.val hi
  simp only [CompactOutput.slice,materialize_length_at,materialize_vertices]
  refine ⟨trivial,by omega,by omega,?_⟩
  simpa using hh.2.2

end HiddenCircuits.DH.LexBFSPartition
