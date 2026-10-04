import HiddenCircuits.Circuit.Runtime.SourceScanPorts

/-! Count both physical swap routes and clear the temporary ordered endpoints. -/
namespace HiddenCircuits.Circuit.Runtime.SourceScan
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

noncomputable def normalize : OracleBlock 35 :=
  seq (copyOn 14 12 16 (by decide) (by decide) (by decide))
    (seq (copyOn 14 12 16 (by decide) (by decide) (by decide))
      (seq (clear 13) (clear 14)))

lemma normalize_executes (g : BitString → ℕ) (k i j : ℕ) (inner outer : BitString) (v : Values) :
    normalize.Executes g (store k i j inner outer v)
      (store k i j inner outer {v with swaps:=v.swaps+2*v.distance,lo:=0,distance:=0})
      (11*v.distance+v.lo+12) := by
  have h₀ : (copyOn (14 : Fin 36) 12 16 (by decide) (by decide) (by decide)).Executes g
      (store k i j inner outer v) (store k i j inner outer {v with swaps:=v.swaps+v.distance}) (5*v.distance+2) := by
    convert copyOn_executes g (14 : Fin 36) 12 16 (by decide) (by decide) (by decide)
      (store k i j inner outer v) rfl using 1
    · funext q;fin_cases q <;> simp [store,GridRuntime.store,frame,←List.replicate_add,Nat.add_comm]
    · simp [store,GridRuntime.store,frame]
  have h₁ : (copyOn (14 : Fin 36) 12 16 (by decide) (by decide) (by decide)).Executes g
      (store k i j inner outer {v with swaps:=v.swaps+v.distance})
      (store k i j inner outer {v with swaps:=v.swaps+2*v.distance}) (5*v.distance+2) := by
    convert copyOn_executes g (14 : Fin 36) 12 16 (by decide) (by decide) (by decide)
      (store k i j inner outer {v with swaps:=v.swaps+v.distance}) rfl using 1
    · funext q;fin_cases q <;> simp [store,GridRuntime.store,frame,←List.replicate_add,two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · simp [store,GridRuntime.store,frame]
  have h₂ : (clear (13 : Fin 36)).Executes g
      (store k i j inner outer {v with swaps:=v.swaps+2*v.distance})
      (store k i j inner outer {v with swaps:=v.swaps+2*v.distance,lo:=0}) (v.lo+1) := by
    convert clear_executes g (13 : Fin 36) (store k i j inner outer {v with swaps:=v.swaps+2*v.distance}) using 1
    · simpa only [show ([] : BitString)=List.replicate 0 true from rfl,update_lo]
    · simp [store,GridRuntime.store,frame]
  have h₃ : (clear (14 : Fin 36)).Executes g
      (store k i j inner outer {v with swaps:=v.swaps+2*v.distance,lo:=0})
      (store k i j inner outer {v with swaps:=v.swaps+2*v.distance,lo:=0,distance:=0}) (v.distance+1) := by
    convert clear_executes g (14 : Fin 36) (store k i j inner outer {v with swaps:=v.swaps+2*v.distance,lo:=0}) using 1
    · simpa only [show ([] : BitString)=List.replicate 0 true from rfl,update_distance]
    · simp [store,GridRuntime.store,frame]
  convert seq_executes _ _ g h₀ (seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃)) using 1 <;> omega

lemma normalize_queryFree : normalize.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))

end HiddenCircuits.Circuit.Runtime.SourceScan
