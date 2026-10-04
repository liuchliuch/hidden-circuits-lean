import HiddenCircuits.Circuit.Runtime.UniformGateEmitter

/-! Byte-for-byte linkage of the literal uniform scan to preparation/reset gates. -/
namespace HiddenCircuits.Circuit.Runtime
open HiddenCircuits.Complexity

def tagOfOne (g : OneGate) : GateTag := gateTag (.one (headPlacement 0) g)

lemma gateTag_one {n : ℕ} (p : Placement n 1) (g : OneGate) : gateTag (.one p g)=tagOfOne g := by
  cases g <;> rfl

lemma uniform_chunks_eq (g : OneGate) (n : ℕ) :
    UniformGateEmitter.chunks (tagOfOne g) 0 n=encodeBitList ((uniformOneProgram g n).gates.map gateBits) := by
  rw [←GateEmitter.chunks_eq,uniformOneProgram_gates]
  unfold UniformGateEmitter.chunks
  rw [←List.range_eq_range',←List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map,List.ofFn_eq_map,Function.comp_def,gateTag_one,gatePosition,wirePlacement]

/-- The real fixed scan emits exactly the claimed circuit's serialized gates. -/
theorem uniformGate_executes (g : BitString → ℕ) (one : OneGate) (n : ℕ) (stream : BitString) :
    ∃ c, (UniformGateEmitter.program (tagOfOne one)).Executes g (UniformGateEmitter.store n 0 0 stream)
      (UniformGateEmitter.store n 0 0 ((encodeBitList ((uniformOneProgram one n).gates.map gateBits)).reverse++stream)) c ∧
      c≤14*n^2+79*n+8 := by
  rw [←uniform_chunks_eq]
  exact UniformGateEmitter.program_executes g _ n stream

end HiddenCircuits.Circuit.Runtime
