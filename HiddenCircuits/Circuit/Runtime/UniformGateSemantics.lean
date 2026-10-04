import HiddenCircuits.Circuit.Runtime.GateEncoding

/-! The literal preparation/reset gate order is an increasing unary wire scan. -/
namespace HiddenCircuits.Circuit.Runtime

def wirePlacement {n : ℕ} (i : Fin n) : Placement n 1 := ⟨i.val,n-i.val-1,by have :=i.isLt;omega⟩

lemma tail_wirePlacement (n : ℕ) (i : Fin n) :
    (tailPlacement n).compose (wirePlacement i)=wirePlacement i.succ := by
  rcases i with ⟨i,hi⟩
  simp only [Placement.compose,tailPlacement,wirePlacement,Fin.val_succ]
  congr 1 <;> omega

/-- The recursive placed program emits exactly one primitive gate at each wire,
in increasing position order, including the empty zero-wire case. -/
theorem uniformOneProgram_gates (g : OneGate) (n : ℕ) :
    (uniformOneProgram g n).gates=List.ofFn (fun i : Fin n => ConstraintGate.one (wirePlacement i) g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [uniformOneProgram,ConstraintProgram.compose,ConstraintProgram.lift,List.singleton_append,
      ih,List.map_ofFn,List.ofFn_succ]
    congr 1
    apply congrArg List.ofFn
    funext i
    change ConstraintGate.one ((tailPlacement n).compose (wirePlacement i)) g = _
    rw [tail_wirePlacement]

end HiddenCircuits.Circuit.Runtime
