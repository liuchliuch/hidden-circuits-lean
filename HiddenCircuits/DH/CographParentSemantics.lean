import HiddenCircuits.DH.CographImmediate
import HiddenCircuits.DH.SliceHeads

/-! Exact correspondence between stack parents and graph-profile slice parents. -/
namespace HiddenCircuits.DH
open SimpleGraph LexBFSModel SliceHeads
variable {V : Type*} {G : SimpleGraph V}

def NoIntermediateEvents (G : SimpleGraph V) (past : List (Event V))
    (root : Event V) (middle : List (Event V)) (child : Event V) : Prop :=
  ∀before e after, middle=before++e::after →
    child.vertex∉profileSlice G ((past++root::before).map Event.vertex) e.vertex

lemma NoIntermediateSlice.events {past middle : List (Event V)} {r x : Event V}
    (h : NoIntermediateSlice G (past.map Event.vertex) r.vertex (middle.map Event.vertex) x.vertex) :
    NoIntermediateEvents G past r middle x := by
  intro before e after he
  have he' : middle.map Event.vertex = before.map Event.vertex++e.vertex::after.map Event.vertex := by
    simp [he]
  simpa only [List.map_append,List.map_cons] using h _ _ _ he'

/-- For actual sweep events, the endpoint-stack's parent test is exactly graph
profile containment with no containing intermediate slice. -/
theorem sweep_parent_iff [DecidableRel G.Adj] (s : Bool) (tie : List V)
    (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (past : List (Event V)) (root : Event V) (middle : List (Event V))
    (child : Event V) (after : List (Event V))
    (he : sweep (fun a b => decide (G.Adj a b)) s tie = past++root::middle++child::after) :
    let p : Frame V := ⟨root.vertex,past.length,past.length+root.sliceSize⟩
    let c : Frame V := ⟨child.vertex,past.length+1+middle.length,past.length+1+middle.length+child.sliceSize⟩
    IsParent (framesFrom 0 past++p::framesFrom (past.length+1) middle) c (some p) ↔
      child.vertex∈profileSlice G (past.map Event.vertex) root.vertex ∧
        NoIntermediateEvents G past root middle child := by
  dsimp only
  have hnot : (⟨root.vertex,past.length,past.length+root.sliceSize⟩ : Frame V)∉
      framesFrom (past.length+1) middle := by
    intro hm
    have hlo := framesFrom_start_le (past.length+1) middle hm
    simp only at hlo
    omega
  rw [IsParent.eq_some_iff hnot]
  apply and_congr
  · exact sweep_interval_contains_iff s tie htie hall past root middle child after he
  · constructor
    · intro h before e rest hm hcontains
      let f : Frame V := ⟨e.vertex,past.length+1+before.length,past.length+1+before.length+e.sliceSize⟩
      have hf : f∈framesFrom (past.length+1) middle :=
        (mem_framesFrom _ _ _).mpr ⟨before,e,rest,hm,rfl⟩
      have hbound := h f hf
      have he' : sweep (fun a b => decide (G.Adj a b)) s tie =
          (past++root::before)++e::rest++child::after := by simp [he,hm,List.append_assoc]
      have hi := (sweep_interval_contains_iff s tie htie hall (past++root::before) e rest child after he').mpr hcontains
      have hlen : middle.length=before.length+1+rest.length := by simp [hm]; omega
      simp only [List.length_append,List.length_cons] at hi
      change past.length+1+before.length+e.sliceSize ≤ past.length+1+middle.length at hbound
      omega
    · intro h f hf
      obtain ⟨before,e,rest,hm,rfl⟩ := (mem_framesFrom _ _ _).mp hf
      have he' : sweep (fun a b => decide (G.Adj a b)) s tie =
          (past++root::before)++e::rest++child::after := by simp [he,hm,List.append_assoc]
      have hn := h before e rest hm
      have hi := sweep_interval_contains_iff s tie htie hall (past++root::before) e rest child after he'
      have hlen : middle.length=before.length+1+rest.length := by simp [hm]; omega
      have hle := Nat.le_of_not_gt (mt hi.mp hn)
      simp only [List.length_append,List.length_cons] at hle
      change past.length+1+before.length+e.sliceSize ≤ past.length+1+middle.length
      omega

end HiddenCircuits.DH
