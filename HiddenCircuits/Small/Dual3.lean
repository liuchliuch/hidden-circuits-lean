import HiddenCircuits.Small.Compounds3
import HiddenCircuits.Small.Compounds1
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def B3_0 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 1]]


theorem dualRise3_0 : compress enum3 (dualRise 4 3 0) = B3_0 := by
  ext s t
  change rise 4 (4-3) 0 ((states3 t).complement) ((states3 s).complement) = _
  rw [states3_complement, states3_complement]
  change (compress enum1 (rise 4 1 0)) (complementIndex3 t) (complementIndex3 s) = _
  rw [rise1_0]
  fin_cases s <;> fin_cases t <;> decide +kernel

def E3_0 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 1], ![0, 0, 0, 0]]


theorem dualDrop3_0 : compress enum3 (dualDrop 4 3 0) = E3_0 := by
  ext s t
  change drop 4 (4-3) 0 ((states3 t).complement) ((states3 s).complement) = _
  rw [states3_complement, states3_complement]
  change (compress enum1 (drop 4 1 0)) (complementIndex3 t) (complementIndex3 s) = _
  rw [drop1_0]
  fin_cases s <;> fin_cases t <;> decide +kernel

def B3_1 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 1, 0], ![0, 0, 0, 1]]


theorem dualRise3_1 : compress enum3 (dualRise 4 3 1) = B3_1 := by
  ext s t
  change rise 4 (4-3) 1 ((states3 t).complement) ((states3 s).complement) = _
  rw [states3_complement, states3_complement]
  change (compress enum1 (rise 4 1 1)) (complementIndex3 t) (complementIndex3 s) = _
  rw [rise1_1]
  fin_cases s <;> fin_cases t <;> decide +kernel

def E3_1 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![0, 1, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 1]]


theorem dualDrop3_1 : compress enum3 (dualDrop 4 3 1) = E3_1 := by
  ext s t
  change drop 4 (4-3) 1 ((states3 t).complement) ((states3 s).complement) = _
  rw [states3_complement, states3_complement]
  change (compress enum1 (drop 4 1 1)) (complementIndex3 t) (complementIndex3 s) = _
  rw [drop1_1]
  fin_cases s <;> fin_cases t <;> decide +kernel

def B3_2 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![1, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]


theorem dualRise3_2 : compress enum3 (dualRise 4 3 2) = B3_2 := by
  ext s t
  change rise 4 (4-3) 2 ((states3 t).complement) ((states3 s).complement) = _
  rw [states3_complement, states3_complement]
  change (compress enum1 (rise 4 1 2)) (complementIndex3 t) (complementIndex3 s) = _
  rw [rise1_2]
  fin_cases s <;> fin_cases t <;> decide +kernel

def E3_2 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]


theorem dualDrop3_2 : compress enum3 (dualDrop 4 3 2) = E3_2 := by
  ext s t
  change drop 4 (4-3) 2 ((states3 t).complement) ((states3 s).complement) = _
  rw [states3_complement, states3_complement]
  change (compress enum1 (drop 4 1 2)) (complementIndex3 t) (complementIndex3 s) = _
  rw [drop1_2]
  fin_cases s <;> fin_cases t <;> decide +kernel


end HiddenCircuits.Small
