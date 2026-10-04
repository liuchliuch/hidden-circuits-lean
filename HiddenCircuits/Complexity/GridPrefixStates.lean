import HiddenCircuits.Complexity.GridPrefixBounds
import HiddenCircuits.Complexity.GridRuntime.Frame

/-! Literal row-major prefixes of the interpolation grid and exact accumulator states. -/
namespace HiddenCircuits.Complexity
open scoped BigOperators

/-- Arithmetic row-major enumeration, including the two boundary nodes. -/
def gridFinIndices (dx dy : ℕ) : List (Fin (dx+1) × Fin (dy+1)) :=
  List.ofFn (finProdFinEquiv.symm : Fin ((dx+1)*(dy+1)) → Fin (dx+1) × Fin (dy+1))

def gridPrefix (dx dy i j : ℕ) : List (Fin (dx+1) × Fin (dy+1)) :=
  (gridFinIndices dx dy).take (i*(dy+1)+j)

@[simp] theorem gridFinIndices_length (dx dy : ℕ) : (gridFinIndices dx dy).length=(dx+1)*(dy+1) := by
  simp [gridFinIndices]
  ring

theorem gridPrefix_length (dx dy i j : ℕ) : (gridPrefix dx dy i j).length≤(dx+1)*(dy+1) := by
  simp only [gridPrefix,List.length_take,gridFinIndices_length]
  exact min_le_right _ _

@[simp] theorem gridPrefix_zero (dx dy : ℕ) : gridPrefix dx dy 0 0=[] := by simp [gridPrefix]

theorem gridPrefix_row (dx dy i : ℕ) : gridPrefix dx dy i (dy+1)=gridPrefix dx dy (i+1) 0 := by
  unfold gridPrefix
  congr 1
  ring

@[simp] theorem gridPrefix_final (dx dy : ℕ) : gridPrefix dx dy (dx+1) 0=gridFinIndices dx dy := by
  unfold gridPrefix
  simpa only [gridFinIndices_length,Nat.add_zero] using (List.take_length (l:=gridFinIndices dx dy))

theorem gridFinIndices_get (dx dy : ℕ) (i : Fin (dx+1)) (j : Fin (dy+1))
    (h : i.val*(dy+1)+j.val<(gridFinIndices dx dy).length) :
    (gridFinIndices dx dy)[i.val*(dy+1)+j.val]=(i,j) := by
  simp only [gridFinIndices,List.getElem_ofFn]
  have he : (⟨i.val*(dy+1)+j.val,by simpa using h⟩ : Fin ((dx+1)*(dy+1)))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [he]
  exact finProdFinEquiv.symm_apply_apply _

theorem gridPrefix_succ (dx dy : ℕ) (i : Fin (dx+1)) (j : Fin (dy+1)) :
    gridPrefix dx dy i.val (j.val+1)=gridPrefix dx dy i.val j.val++[(i,j)] := by
  have h : i.val*(dy+1)+j.val<(gridFinIndices dx dy).length := by
    rw [gridFinIndices_length]
    have hm := Nat.mul_le_mul_right (dy+1) (show i.val+1≤dx+1 by omega)
    nlinarith [j.isLt]
  unfold gridPrefix
  rw [←Nat.add_assoc,List.take_succ_eq_append_getElem h,gridFinIndices_get]

def gridPrefixSum (dx dy : ℕ) (values : Fin (dx+1) → Fin (dy+1) → ℤ) (i j : ℕ) : ℤ :=
  gridPartialSum dx dy values (gridPrefix dx dy i j)

@[simp] theorem gridPrefixSum_zero (dx dy : ℕ) (values : Fin (dx+1) → Fin (dy+1) → ℤ) :
    gridPrefixSum dx dy values 0 0=0 := by simp [gridPrefixSum,gridPartialSum]

theorem gridPrefixSum_succ (dx dy : ℕ) (values : Fin (dx+1) → Fin (dy+1) → ℤ)
    (i : Fin (dx+1)) (j : Fin (dy+1)) :
    gridPrefixSum dx dy values i.val (j.val+1)=
      gridPrefixSum dx dy values i.val j.val+gridTerm dx dy i j (values i j) := by
  simp [gridPrefixSum,gridPrefix_succ,gridPartialSum,List.map_append,List.sum_append]

theorem gridPrefixSum_row (dx dy : ℕ) (values : Fin (dx+1) → Fin (dy+1) → ℤ) (i : ℕ) :
    gridPrefixSum dx dy values i (dy+1)=gridPrefixSum dx dy values (i+1) 0 := by
  rw [gridPrefixSum,gridPrefixSum,gridPrefix_row]

theorem gridPrefixSum_final (dx dy : ℕ) (values : Fin (dx+1) → Fin (dy+1) → ℤ) :
    gridPrefixSum dx dy values (dx+1) 0=gridNumerator dx dy values := by
  rw [gridPrefixSum,gridPrefix_final,gridPartialSum,gridFinIndices,List.map_ofFn,List.sum_ofFn]
  rw [gridNumerator_eq_sum_gridTerm]
  let f : Fin (dx+1) × Fin (dy+1) → ℤ := fun ij => gridTerm dx dy ij.1 ij.2 (values ij.1 ij.2)
  have he := Fintype.sum_equiv (finProdFinEquiv.symm : Fin ((dx+1)*(dy+1)) ≃ Fin (dx+1) × Fin (dy+1))
    (fun z => f (finProdFinEquiv.symm z)) f (fun _ => rfl)
  simpa only [f,Function.comp_def,Fintype.sum_prod_type] using he

theorem gridPrefixSum_envelope (dx dy B : ℕ) (values : Fin (dx+1) → Fin (dy+1) → ℤ)
    (hv : ∀ i j, (values i j).natAbs≤2^B) (i j : ℕ) :
    (gridPrefixSum dx dy values i j).natAbs≤2^(numeratorExponent dx dy B) :=
  gridPartialSum_envelope dx dy B values hv _ (gridPrefix_length dx dy i j)

/-- Connect exact row-major integer sums to the actual finite grid interpreter.
Only the concrete per-cell code remains to be supplied by the caller. -/
theorem gridProgram_accumulator {k : ℕ} (B : OracleBlock (k+8)) (g : BitString → ℕ)
    (dx dy C : ℕ) (values : Fin (dx+1) → Fin (dy+1) → ℤ)
    (encodeFrame : ℤ → GridRuntime.Frame k)
    (hB : ∀ (i : Fin (dx+1)) (j : Fin (dy+1)) inner outer, ∃ c,
      B.Executes g (GridRuntime.store dx dy i.val j.val inner outer
        (encodeFrame (gridPrefixSum dx dy values i.val j.val)))
        (GridRuntime.store dx dy i.val j.val inner outer
          (encodeFrame (gridPrefixSum dx dy values i.val j.val+gridTerm dx dy i j (values i j)))) c ∧ c≤C) :
    ∃ c, (GridRuntime.program B).Executes g (GridRuntime.initialStore dx dy (encodeFrame 0))
      (GridRuntime.initialStore dx dy (encodeFrame (gridNumerator dx dy values))) c ∧
      c≤GridRuntime.programCost dx dy C := by
  have hb : GridRuntime.BodySpec B g dx dy C (fun i j => encodeFrame (gridPrefixSum dx dy values i j)) := by
    intro i j hi hj inner outer
    obtain ⟨c,hc,hcb⟩ := hB ⟨i,by omega⟩ ⟨j,by omega⟩ inner outer
    dsimp only
    rw [gridPrefixSum_succ dx dy values ⟨i,by omega⟩ ⟨j,by omega⟩]
    exact ⟨c,hc,hcb⟩
  have hr : ∀ i, i≤dx → encodeFrame (gridPrefixSum dx dy values i (dy+1))=
      encodeFrame (gridPrefixSum dx dy values (i+1) 0) := by
    intro i hi
    rw [gridPrefixSum_row]
  simpa only [gridPrefixSum_zero,gridPrefixSum_final] using
    GridRuntime.program_executes B g dx dy C _ hb hr
end HiddenCircuits.Complexity
