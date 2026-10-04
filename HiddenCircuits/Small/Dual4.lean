import HiddenCircuits.Small.Compounds4
import HiddenCircuits.Small.Compounds0
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def B4_0 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem dualRise4_0 : compress enum4 (dualRise 4 4 0) = B4_0 := by
  ext s t
  change rise 4 (4-4) 0 ((states4 t).complement) ((states4 s).complement) = _
  rw [states4_complement, states4_complement]
  change (compress enum0 (rise 4 0 0)) (complementIndex4 t) (complementIndex4 s) = _
  rw [rise0_0]
  fin_cases s <;> fin_cases t <;> decide +kernel

def E4_0 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem dualDrop4_0 : compress enum4 (dualDrop 4 4 0) = E4_0 := by
  ext s t
  change drop 4 (4-4) 0 ((states4 t).complement) ((states4 s).complement) = _
  rw [states4_complement, states4_complement]
  change (compress enum0 (drop 4 0 0)) (complementIndex4 t) (complementIndex4 s) = _
  rw [drop0_0]
  fin_cases s <;> fin_cases t <;> decide +kernel

def B4_1 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem dualRise4_1 : compress enum4 (dualRise 4 4 1) = B4_1 := by
  ext s t
  change rise 4 (4-4) 1 ((states4 t).complement) ((states4 s).complement) = _
  rw [states4_complement, states4_complement]
  change (compress enum0 (rise 4 0 1)) (complementIndex4 t) (complementIndex4 s) = _
  rw [rise0_1]
  fin_cases s <;> fin_cases t <;> decide +kernel

def E4_1 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem dualDrop4_1 : compress enum4 (dualDrop 4 4 1) = E4_1 := by
  ext s t
  change drop 4 (4-4) 1 ((states4 t).complement) ((states4 s).complement) = _
  rw [states4_complement, states4_complement]
  change (compress enum0 (drop 4 0 1)) (complementIndex4 t) (complementIndex4 s) = _
  rw [drop0_1]
  fin_cases s <;> fin_cases t <;> decide +kernel

def B4_2 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem dualRise4_2 : compress enum4 (dualRise 4 4 2) = B4_2 := by
  ext s t
  change rise 4 (4-4) 2 ((states4 t).complement) ((states4 s).complement) = _
  rw [states4_complement, states4_complement]
  change (compress enum0 (rise 4 0 2)) (complementIndex4 t) (complementIndex4 s) = _
  rw [rise0_2]
  fin_cases s <;> fin_cases t <;> decide +kernel

def E4_2 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem dualDrop4_2 : compress enum4 (dualDrop 4 4 2) = E4_2 := by
  ext s t
  change drop 4 (4-4) 2 ((states4 t).complement) ((states4 s).complement) = _
  rw [states4_complement, states4_complement]
  change (compress enum0 (drop 4 0 2)) (complementIndex4 t) (complementIndex4 s) = _
  rw [drop0_2]
  fin_cases s <;> fin_cases t <;> decide +kernel


end HiddenCircuits.Small
