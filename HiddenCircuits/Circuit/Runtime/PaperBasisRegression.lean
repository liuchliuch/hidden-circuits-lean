import HiddenCircuits.Circuit.Runtime.SampleScalar
import HiddenCircuits.Circuit.Runtime.DeltaValueBounds
import HiddenCircuits.Complexity.NativeValidation.SemanticsSoundness

/-! Kernel-checked regressions for the paper's raw encoded T = 8X primitive.
The normalized X remains a distinct gate, with its original encoding and scalar. -/
namespace HiddenCircuits.Circuit.Runtime.PaperBasisRegression
open Complexity

def onePlacement : Placement 1 1 := ⟨0,0,rfl⟩
def oneInput (g : OneGate) : DeltaInput :=
  ⟨1,[.one onePlacement g],oneBitEquiv 0,oneBitEquiv 1⟩

theorem encodedSwap_entry : (oneInput .encodedSwap).value=8 := by decide +kernel

theorem swap_entry : (oneInput .swap).value=1 := by decide +kernel

theorem encodedSwap_physical : oneGateWord .encodedSwap=⟨1,filterT⟩ := rfl
theorem swap_physical : oneGateWord .swap=⟨1/8,filterT⟩ := rfl
theorem encodedSwap_scalar : SampleScalar.oneExponent .encodedSwap=0 ∧
    SampleScalar.oneSign .encodedSwap=0 := by decide +kernel
theorem encodedSwap_tag : GateTag.encodedSwap.bits=[true,false,false,true] := rfl
theorem encodedSwap_decode : decodeTag [true,false,false,true]=some .encodedSwap := rfl
theorem encodedSwap_width : GateTag.encodedSwap.width=1 := rfl

theorem existing_tags_unchanged :
    [GateTag.reset, .copy, .scale, .signScale, .swap, .hadamard, .mix, .forbid, .controlledSign].map GateTag.bits=
    [[false,false,false,false],[false,false,false,true],[false,false,true,false],
     [false,false,true,true],[false,true,false,false],[false,true,false,true],
     [false,true,true,false],[false,true,true,true],[true,false,false,false]] := rfl

theorem encodedSwap_native_roundtrip :
    DeltaInput.decode (oneInput .encodedSwap).encode=some (oneInput .encodedSwap) :=
  DeltaInput.decode_encode _
theorem encodedSwap_constraint_roundtrip :
    ConstraintInput.decode (oneInput .encodedSwap).descriptor.encode=
      some (oneInput .encodedSwap).descriptor := ConstraintInput.decode_encode _
theorem encodedSwap_delta_accepts :
    NativeValidation.Semantics.test true (oneInput .encodedSwap).encode=true := by decide +kernel
theorem encodedSwap_constraint_accepts :
    NativeValidation.Semantics.test false (oneInput .encodedSwap).encode=true := by decide +kernel
theorem encodedSwap_cleared_bound : ∀x y : Fin 2, (DeltaValues.one .encodedSwap x y).natAbs≤16 :=
  DeltaValues.one_abs _

end HiddenCircuits.Circuit.Runtime.PaperBasisRegression
