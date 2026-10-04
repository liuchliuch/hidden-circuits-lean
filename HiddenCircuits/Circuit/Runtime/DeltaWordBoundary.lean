import HiddenCircuits.Complexity.DeltaEncoding

/-! Literal Delta-only boundary transport. Its matrix proof uses the Delta
semantics directly; descriptors are used only to reuse the physical byte emitter. -/
namespace HiddenCircuits.Circuit.Runtime.DeltaBoundary
open HiddenCircuits.Complexity
open scoped Kronecker BigOperators

def place {n r : ℕ} (p : Placement n r) : DeltaGate r → DeltaGate n
  | .one q g => .one (p.compose q) g
  | .constraint q => .constraint (p.compose q)

lemma place_matrix {n r : ℕ} (p : Placement n r) (g : DeltaGate r) :
    (place p g).matrix=p.lift g.matrix := by
  cases g <;> exact (p.lift_compose _ _).symm

lemma placed_circuit_matrix {n r : ℕ} (p : Placement n r) (w : List (DeltaGate r)) :
    deltaCircuitMatrix (w.map (place p))=p.lift (deltaCircuitMatrix w) := by
  induction w with
  | nil => exact p.lift_one.symm
  | cons g w ih =>
    change (place p g).matrix * deltaCircuitMatrix (w.map (place p)) = p.lift (g.matrix*deltaCircuitMatrix w)
    rw [place_matrix,ih,p.lift_mul]

@[simp] lemma descriptor_place {n r : ℕ} (p : Placement n r) (g : DeltaGate r) :
    DeltaGate.descriptor (place p g)=(DeltaGate.descriptor g).place p := by
  cases g <;> rfl

/-- One literal X gate on exactly the wires selected by the boundary bits. -/
def boundaryProgram : (n : ℕ) → CodeBits n → List (DeltaGate n)
  | 0,_ => []
  | n+1,x => (if x.1=0 then [] else [.one (headPlacement n) .swap]) ++
      (boundaryProgram n x.2).map (place (tailPlacement n))

lemma boundaryProgram_length (n : ℕ) (x : CodeBits n) :
    (boundaryProgram n x).length ≤ n := by
  induction n with
  | zero => simp [boundaryProgram]
  | succ n ih =>
    rcases x with ⟨i,x⟩
    have ht:=ih x
    simp only [boundaryProgram,List.length_append,List.length_map]
    split_ifs <;> simp only [List.length_nil,List.length_cons] <;> omega

lemma boundaryProgram_matrix (n : ℕ) (x : CodeBits n) :
    deltaCircuitMatrix (boundaryProgram n x)=Circuit.boundaryMatrix n x := by
  induction n with
  | zero => simp [boundaryProgram,deltaCircuitMatrix,Circuit.boundaryMatrix]
  | succ n ih =>
    rcases x with ⟨i,x⟩
    rw [boundaryProgram,deltaCircuitMatrix_append,placed_circuit_matrix,ih,tailPlacement_lift]
    by_cases hi:i=0
    · simp [hi,deltaCircuitMatrix,Circuit.boundaryMatrix]
    · simp only [hi,↓reduceIte,deltaCircuitMatrix,List.map_cons,List.map_nil,List.prod_cons,
        List.prod_nil,mul_one,DeltaGate.matrix,headPlacement_lift,Circuit.boundaryMatrix]
      rw [←Matrix.mul_kronecker_mul,mul_one,one_mul]

/-- The Delta gate list has exactly the bytes expected by the established mask
preprocessor, without asserting that Delta and N have the same matrix. -/
lemma boundaryProgram_descriptor (n : ℕ) (x : CodeBits n) :
    (boundaryProgram n x).map DeltaGate.descriptor=(Circuit.boundaryProgram n x).gates := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨i,x⟩
    simp only [boundaryProgram,List.map_append,List.map_map,Function.comp_def,descriptor_place,
      Circuit.boundaryProgram,ConstraintProgram.compose,ConstraintProgram.lift]
    have ht : List.map (fun a => ConstraintGate.place (tailPlacement n) (DeltaGate.descriptor a))
        (boundaryProgram n x) = ((Circuit.boundaryProgram n x).gates).map (ConstraintGate.place (tailPlacement n)) := by
      simpa only [List.map_map,Function.comp_def] using
        congrArg (List.map (ConstraintGate.place (tailPlacement n))) (ih x)
    rw [ht]
    split_ifs <;> rfl

def zeroBoundaryCircuit {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) : List (DeltaGate n) :=
  boundaryProgram n x ++ w ++ boundaryProgram n y

lemma zeroBoundaryCircuit_length {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) :
    (zeroBoundaryCircuit w x y).length ≤ 2*n+w.length := by
  have hx:=boundaryProgram_length n x
  have hy:=boundaryProgram_length n y
  simp only [zeroBoundaryCircuit,List.length_append]
  omega

lemma zeroBoundaryCircuit_correct {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) :
    deltaCircuitMatrix (zeroBoundaryCircuit w x y) (zeroBits n) (zeroBits n)=deltaCircuitMatrix w x y := by
  rw [zeroBoundaryCircuit,deltaCircuitMatrix_append,deltaCircuitMatrix_append,
    boundaryProgram_matrix,boundaryProgram_matrix]
  simp only [Matrix.mul_apply,Circuit.boundaryMatrix_row,Circuit.boundaryMatrix_column]
  simp

lemma zeroBoundaryCircuit_descriptor {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) :
    (zeroBoundaryCircuit w x y).map DeltaGate.descriptor=
      Circuit.zeroBoundaryCircuit (w.map DeltaGate.descriptor) x y := by
  simp only [zeroBoundaryCircuit,List.map_append,boundaryProgram_descriptor,Circuit.zeroBoundaryCircuit]

lemma no_gate (a : DeltaGate 0) : False := by
  cases a with
  | one p _ => have h:=p.size;omega
  | constraint p => have h:=p.size;omega

lemma gates_nil (w : List (DeltaGate 0)) : w=[] := by
  cases w with
  | nil => rfl
  | cons a _ => exact (no_gate a).elim

lemma matrix_entry_zero_wires (w : List (DeltaGate 0)) (x y : CodeBits 0) :
    deltaCircuitMatrix w x y=1 := by
  rw [gates_nil w]
  cases x;cases y
  simp [deltaCircuitMatrix]

end HiddenCircuits.Circuit.Runtime.DeltaBoundary
