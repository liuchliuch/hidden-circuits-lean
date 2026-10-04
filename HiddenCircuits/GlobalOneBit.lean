import HiddenCircuits.RawCode
import HiddenCircuits.OneBitGates

namespace HiddenCircuits

@[simp] theorem Letter.inLeft_zero {a : ℕ} (l : Letter a) : l.inLeft 0 = l := by
  cases l
  rfl

@[simp] theorem globalFilterWord_one : globalFilterWord 1 = filterWord := by
  have hm : (Letter.inLeft 0 : Letter 4 → Letter 4)=id := funext Letter.inLeft_zero
  simp only [globalFilterWord,blockWidth,List.map_nil,List.append_nil,hm,List.map_id]

@[simp] theorem globalFilter_one (q : ℕ) : globalFilter 1 q = localFilter q := by
  simp only [globalFilter,globalFilterWord_one,pow_one,localFilter]

/-- The k=1 instance of the actual global projection is the original local filter. -/
theorem globalProjection_one : globalProjection 1 = localFilter 2 := by
  change (globalFilter 1 2)^2 = localFilter 2
  rw [globalFilter_one,pow_two,localFilter_idempotent]

 theorem rawCode_one (x : Fin 2) : rawCode 1 (x,PUnit.unit) = localRawCode x := by
  apply Subtype.ext
  ext t
  change t ∈ (State.join (localRawCode x) (balancedJoin 0 PUnit.unit)).val ↔ t ∈ (localRawCode x).val
  exact State.join_mem_left (localRawCode x) (balancedJoin 0 PUnit.unit) t

 theorem localRawCode_eq_oneBitCode (x : Fin 2) : localRawCode x = oneBitCode x := by
  fin_cases x <;> decide +kernel

/-- Explicit four-track view of the same actual one-block global projection. -/
def globalProjectionOne : Matrix (State 4 2) (State 4 2) ℚ :=
  fun S T => globalProjection 1 S T

 theorem globalProjectionOne_eq : globalProjectionOne = localFilter 2 := globalProjection_one

/-- The isolated one-bit certificates act through the same actual global encoding projection. -/
theorem global_oneBit_encoded (w : List (Letter 4)) (x y : Fin 2) :
    (globalProjectionOne * wordMatrix 2 w * globalProjectionOne)
      (rawCode 1 (x,PUnit.unit)) (rawCode 1 (y,PUnit.unit)) = oneBitEncoded w x y := by
  rw [globalProjectionOne_eq,rawCode_one,rawCode_one,localRawCode_eq_oneBitCode,localRawCode_eq_oneBitCode]
  rfl

end HiddenCircuits
