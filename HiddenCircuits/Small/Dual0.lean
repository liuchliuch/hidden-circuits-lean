import HiddenCircuits.Small.Compounds0
import HiddenCircuits.Small.Compounds4
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def B0_0 : Matrix (Fin 1) (Fin 1) ℚ := ![![2]]


theorem dualRise0_0 : compress enum0 (dualRise 4 0 0) = B0_0 := by
  ext s t
  change rise 4 (4-0) 0 ((states0 t).complement) ((states0 s).complement) = _
  rw [states0_complement, states0_complement]
  change (compress enum4 (rise 4 4 0)) (complementIndex0 t) (complementIndex0 s) = _
  rw [rise4_0]
  fin_cases s <;> fin_cases t <;> decide +kernel

def E0_0 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem dualDrop0_0 : compress enum0 (dualDrop 4 0 0) = E0_0 := by
  ext s t
  change drop 4 (4-0) 0 ((states0 t).complement) ((states0 s).complement) = _
  rw [states0_complement, states0_complement]
  change (compress enum4 (drop 4 4 0)) (complementIndex0 t) (complementIndex0 s) = _
  rw [drop4_0]
  fin_cases s <;> fin_cases t <;> decide +kernel

def B0_1 : Matrix (Fin 1) (Fin 1) ℚ := ![![2]]


theorem dualRise0_1 : compress enum0 (dualRise 4 0 1) = B0_1 := by
  ext s t
  change rise 4 (4-0) 1 ((states0 t).complement) ((states0 s).complement) = _
  rw [states0_complement, states0_complement]
  change (compress enum4 (rise 4 4 1)) (complementIndex0 t) (complementIndex0 s) = _
  rw [rise4_1]
  fin_cases s <;> fin_cases t <;> decide +kernel

def E0_1 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem dualDrop0_1 : compress enum0 (dualDrop 4 0 1) = E0_1 := by
  ext s t
  change drop 4 (4-0) 1 ((states0 t).complement) ((states0 s).complement) = _
  rw [states0_complement, states0_complement]
  change (compress enum4 (drop 4 4 1)) (complementIndex0 t) (complementIndex0 s) = _
  rw [drop4_1]
  fin_cases s <;> fin_cases t <;> decide +kernel

def B0_2 : Matrix (Fin 1) (Fin 1) ℚ := ![![2]]


theorem dualRise0_2 : compress enum0 (dualRise 4 0 2) = B0_2 := by
  ext s t
  change rise 4 (4-0) 2 ((states0 t).complement) ((states0 s).complement) = _
  rw [states0_complement, states0_complement]
  change (compress enum4 (rise 4 4 2)) (complementIndex0 t) (complementIndex0 s) = _
  rw [rise4_2]
  fin_cases s <;> fin_cases t <;> decide +kernel

def E0_2 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem dualDrop0_2 : compress enum0 (dualDrop 4 0 2) = E0_2 := by
  ext s t
  change drop 4 (4-0) 2 ((states0 t).complement) ((states0 s).complement) = _
  rw [states0_complement, states0_complement]
  change (compress enum4 (drop 4 4 2)) (complementIndex0 t) (complementIndex0 s) = _
  rw [drop4_2]
  fin_cases s <;> fin_cases t <;> decide +kernel


end HiddenCircuits.Small
