import HiddenCircuits.Circuit.Runtime.RestoringEdgeEmitter

namespace HiddenCircuits.Circuit.Runtime.RestoringEdgeEmitter
open HiddenCircuits.Complexity

lemma encode_append (xs ys : List BitString) : encodeBitList (xs++ys)=encodeBitList xs++encodeBitList ys := by
  simp only [encodeBitList_eq_flatMap,List.flatMap_append]

lemma route_bytes {n : ℕ} (w : List (Fin (n-1))) :
    encodeBitList ((routeProgram w).gates.map gateBits)=w.flatMap (fun i => GateEmitter.swapBits i.val) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [routeProgram,ConstraintProgram.compose,List.map_append,encode_append,List.flatMap_cons]
    rw [←GateEmitter.swapBits_eq,ih]

lemma descending_route {n : ℕ} (lo d : ℕ) (h : lo+d+1<n) :
    descendingBits lo d=(routeIndices (k:=n) (lo+1) d (by omega)).flatMap (fun i => GateEmitter.swapBits i.val) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [descendingBits,routeIndices,List.flatMap_cons]
    rw [ih (by omega)]
    congr 2 <;> omega

lemma ascending_snoc (lo d : ℕ) :
    ascendingBits lo (d+1)=ascendingBits lo d++GateEmitter.swapBits (lo+d) := by
  induction d generalizing lo with
  | zero => simp [ascendingBits]
  | succ d ih =>
    rw [ascendingBits,ih,ascendingBits,List.append_assoc]
    simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

lemma ascending_route {n : ℕ} (lo d : ℕ) (h : lo+d+1<n) :
    ascendingBits (lo+1) d=((routeIndices (k:=n) (lo+1) d (by omega)).reverse).flatMap (fun i => GateEmitter.swapBits i.val) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [routeIndices,List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [ascending_snoc,ih (by omega)]

/-- The ordered source endpoints supplied to the local compiler. -/
def orderedEdge {n : ℕ} (lo d : ℕ) (h : lo+d+1<n) : SourceEdge n :=
  ⟨⟨lo,by omega⟩,⟨lo+d+1,h⟩,by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega⟩

lemma ordered_route {n : ℕ} (lo d : ℕ) (h : lo+d+1<n) :
    edgeRouteIndices (1 : Equiv.Perm (Fin n)) (orderedEdge lo d h)=
      routeIndices (lo+1) d (by omega) := by
  have ho : (1 : Equiv.Perm (Fin n)) (orderedEdge lo d h).left <
      (1 : Equiv.Perm (Fin n)) (orderedEdge lo d h).right := by change lo<lo+d+1;omega
  unfold edgeRouteIndices
  rw [dif_pos ho]
  simp only [Equiv.Perm.one_apply,orderedEdge,routeBetween]
  have he : lo+d+1-(lo+1)=d := by omega
  congr 1 <;> omega

lemma ordered_position {n : ℕ} (lo d : ℕ) (h : lo+d+1<n) :
    (edgeRoutePosition (1 : Equiv.Perm (Fin n)) (orderedEdge lo d h)).val=lo := by
  have ho : (1 : Equiv.Perm (Fin n)) (orderedEdge lo d h).left <
      (1 : Equiv.Perm (Fin n)) (orderedEdge lo d h).right := by change lo<lo+d+1;omega
  unfold edgeRoutePosition
  rw [dif_pos ho]
  rfl

/-- Exact bytes of the existing restoringEdgeProgram, not merely an equivalent
matrix or an abstract gate-count specification. -/
theorem bits_eq_restoringEdge {n : ℕ} (lo d : ℕ) (h : lo+d+1<n) :
    bits lo d=encodeBitList ((restoringEdgeProgram (orderedEdge lo d h)).gates.map gateBits) := by
  simp only [restoringEdgeProgram,edgeProgram,ConstraintProgram.compose,List.map_append,encode_append,ordered_route]
  rw [route_bytes,route_bytes]
  rw [←descending_route lo d h,←ascending_route lo d h]
  change descendingBits lo d++GateEmitter.chunk .forbid lo++ascendingBits (lo+1) d =
    (descendingBits lo d++encodeBitList [gateBits (.forbid (adjacentPlacement (edgeRoutePosition 1 (orderedEdge lo d h))))])++
      ascendingBits (lo+1) d
  congr 2
  rw [←GateEmitter.chunk_gate]
  simp only [gateTag,gatePosition,adjacentPlacement,ordered_position]

/-- Precisely two d-swap routes are used, so the exact scalar normalization is
8^(-2d), and every one of the eighteen d macro gates plus the forbid is present. -/
theorem ordered_normalization {n : ℕ} (lo d : ℕ) (h : lo+d+1<n) :
    (restoringEdgeProgram (orderedEdge lo d h)).scalar=(1/8:ℚ)^(2*d) ∧
      (restoringEdgeProgram (orderedEdge lo d h)).gates.length=18*d+1 := by
  rw [restoringEdgeProgram_scalar,restoringEdgeProgram_length,ordered_route,routeIndices_length]
  exact ⟨rfl,rfl⟩

/-- Operational endpoint directly in the source circuit's canonical gate bytes. -/
theorem restoringEdge_executes {n : ℕ} (g : BitString → ℕ) (lo d : ℕ) (h : lo+d+1<n) (out : BitString) :
    ∃ cost, program.Executes g (store lo d 0 0 out [] [] [])
      (store lo d 0 0 ((encodeBitList ((restoringEdgeProgram (orderedEdge lo d h)).gates.map gateBits)).reverse++out) [] [] []) cost ∧
      cost≤timeBound.eval (lo+d) := by
  rw [←bits_eq_restoringEdge lo d h]
  exact program_executes g lo d out

end HiddenCircuits.Circuit.Runtime.RestoringEdgeEmitter
