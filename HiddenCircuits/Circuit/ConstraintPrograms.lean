import HiddenCircuits.Circuit.SwapMacro
import HiddenCircuits.Circuit.PlacementComposition
import HiddenCircuits.Circuit.AdjacentRouting

namespace HiddenCircuits.Circuit

/-- Place every primitive gate in a larger explicitly specified adjacent interval. -/
def ConstraintGate.place {n r : ℕ} (p : Placement n r) : ConstraintGate r → ConstraintGate n
  | .one q g => .one (p.compose q) g
  | .forbid q => .forbid (p.compose q)
  | .controlledSign q => .controlledSign (p.compose q)

 theorem ConstraintGate.place_matrix {n r : ℕ} (p : Placement n r) (g : ConstraintGate r) :
    (g.place p).matrix=p.lift g.matrix := by
  cases g <;> exact (p.lift_compose _ _).symm

 theorem placed_constraintCircuit {n r : ℕ} (p : Placement n r) (w : List (ConstraintGate r)) :
    constraintCircuitMatrix (w.map (ConstraintGate.place p))=p.lift (constraintCircuitMatrix w) := by
  induction w with
  | nil => exact p.lift_one.symm
  | cons g w ih =>
    change (g.place p).matrix * constraintCircuitMatrix (w.map (ConstraintGate.place p)) = p.lift (g.matrix*constraintCircuitMatrix w)
    rw [ConstraintGate.place_matrix,ih,p.lift_mul]

/-- Ordinary logical program composition multiplies its explicit scalar factors. -/
def ConstraintProgram.compose {n : ℕ} (p q : ConstraintProgram n) : ConstraintProgram n :=
  ⟨p.scalar*q.scalar,p.gates++q.gates⟩

def ConstraintProgram.identity (n : ℕ) : ConstraintProgram n := ⟨1,[]⟩

 theorem ConstraintProgram.compose_matrix {n : ℕ} (p q : ConstraintProgram n) :
    (p.compose q).matrix=p.matrix*q.matrix := by
  simp only [ConstraintProgram.compose,ConstraintProgram.matrix,constraintCircuitMatrix,
    List.map_append,List.prod_append,smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [mul_comm p.scalar q.scalar]

@[simp] theorem ConstraintProgram.identity_matrix (n : ℕ) : (ConstraintProgram.identity n).matrix=1 := by
  simp [ConstraintProgram.identity,ConstraintProgram.matrix,constraintCircuitMatrix]

def ConstraintProgram.lift {n r : ℕ} (p : Placement n r) (w : ConstraintProgram r) : ConstraintProgram n :=
  ⟨w.scalar,w.gates.map (ConstraintGate.place p)⟩

 theorem ConstraintProgram.lift_matrix {n r : ℕ} (p : Placement n r) (w : ConstraintProgram r) :
    (w.lift p).matrix=p.lift w.matrix := by
  rw [ConstraintProgram.lift,ConstraintProgram.matrix,placed_constraintCircuit,← p.lift_smul]
  rfl

/-- The actual two-bit interval of an adjacent-swap index. -/
def adjacentPlacement {n : ℕ} (i : Fin (n-1)) : Placement n 2 :=
  ⟨i.val,n-i.val-2,by have hi:=i.isLt; omega⟩

/-- Nine literal H/CZ gates and the explicit1/8 normalization implement an adjacent exchange. -/
def adjacentSwapProgram {n : ℕ} (i : Fin (n-1)) : ConstraintProgram n :=
  swapLocalProgram.lift (adjacentPlacement i)

 theorem adjacentSwapProgram_matrix_local {n : ℕ} (i : Fin (n-1)) :
    (adjacentSwapProgram i).matrix=(adjacentPlacement i).lift (wireMatrix (Equiv.swap (0:Fin 2) 1)) := by
  rw [adjacentSwapProgram,ConstraintProgram.lift_matrix,swapLocalProgram_matrix]

@[simp] theorem adjacentSwapProgram_scalar {n : ℕ} (i : Fin (n-1)) :
    (adjacentSwapProgram i).scalar=(1/8:ℚ) := rfl

@[simp] theorem adjacentSwapProgram_length {n : ℕ} (i : Fin (n-1)) :
    (adjacentSwapProgram i).gates.length=9 := by
  simp [adjacentSwapProgram,ConstraintProgram.lift,swapLocalProgram,swapLocalCircuit_length]

/-- The actual flattened logical-gate program for an explicit routing list. -/
def routeProgram {n : ℕ} : List (Fin (n-1)) → ConstraintProgram n
  | [] => .identity n
  | i::w => (adjacentSwapProgram i).compose (routeProgram w)

 theorem routeProgram_length {n : ℕ} (w : List (Fin (n-1))) :
    (routeProgram w).gates.length=9*w.length := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [routeProgram,ConstraintProgram.compose,List.length_append,adjacentSwapProgram_length,ih,List.length_cons]
    omega

 theorem routeProgram_scalar {n : ℕ} (w : List (Fin (n-1))) :
    (routeProgram w).scalar=(1/8:ℚ)^w.length := by
  induction w with
  | nil => simp [routeProgram,ConstraintProgram.identity]
  | cons i w ih =>
    simp only [routeProgram,ConstraintProgram.compose,adjacentSwapProgram_scalar,ih,List.length_cons,pow_succ']

/-- Exact elementary logical-gate count of the source paper's one-way edge route. -/
theorem routeBetween_program_length {n : ℕ} (a b : Fin n) (h : a<b) :
    (routeProgram (routeBetween a b h)).gates.length=9*(b.val-a.val-1) ∧
      (routeProgram (routeBetween a b h)).gates.length≤9*(n-1) := by
  rw [routeProgram_length]
  exact ⟨congrArg (9*·) (routeBetween_spec a b h).1,
    Nat.mul_le_mul_left 9 (routeBetween_spec a b h).2.1⟩

end HiddenCircuits.Circuit
