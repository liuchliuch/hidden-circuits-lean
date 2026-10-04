import HiddenCircuits.Small.Compounds1
import HiddenCircuits.Small.Compounds3
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def B1_0 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, -2, -4], ![1, 1, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]]


theorem dualRise1_0 : compress enum1 (dualRise 4 1 0) = B1_0 := by
  ext s t
  change rise 4 (4-1) 0 ((states1 t).complement) ((states1 s).complement) = _
  rw [states1_complement, states1_complement]
  change (compress enum3 (rise 4 3 0)) (complementIndex1 t) (complementIndex1 s) = _
  rw [rise3_0]
  fin_cases s <;> fin_cases t <;> decide +kernel

def E1_0 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 1, 2, 4], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem dualDrop1_0 : compress enum1 (dualDrop 4 1 0) = E1_0 := by
  ext s t
  change drop 4 (4-1) 0 ((states1 t).complement) ((states1 s).complement) = _
  rw [states1_complement, states1_complement]
  change (compress enum3 (drop 4 3 0)) (complementIndex1 t) (complementIndex1 s) = _
  rw [drop3_0]
  fin_cases s <;> fin_cases t <;> decide +kernel

def B1_1 : Matrix (Fin 4) (Fin 4) ℚ := ![![2, 0, 0, 0], ![0, 0, 0, -2], ![0, 1, 1, 0], ![0, 0, 0, 2]]


theorem dualRise1_1 : compress enum1 (dualRise 4 1 1) = B1_1 := by
  ext s t
  change rise 4 (4-1) 1 ((states1 t).complement) ((states1 s).complement) = _
  rw [states1_complement, states1_complement]
  change (compress enum3 (rise 4 3 1)) (complementIndex1 t) (complementIndex1 s) = _
  rw [rise3_1]
  fin_cases s <;> fin_cases t <;> decide +kernel

def E1_1 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 1, 1, 2], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem dualDrop1_1 : compress enum1 (dualDrop 4 1 1) = E1_1 := by
  ext s t
  change drop 4 (4-1) 1 ((states1 t).complement) ((states1 s).complement) = _
  rw [states1_complement, states1_complement]
  change (compress enum3 (drop 4 3 1)) (complementIndex1 t) (complementIndex1 s) = _
  rw [drop3_1]
  fin_cases s <;> fin_cases t <;> decide +kernel

def B1_2 : Matrix (Fin 4) (Fin 4) ℚ := ![![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 1]]


theorem dualRise1_2 : compress enum1 (dualRise 4 1 2) = B1_2 := by
  ext s t
  change rise 4 (4-1) 2 ((states1 t).complement) ((states1 s).complement) = _
  rw [states1_complement, states1_complement]
  change (compress enum3 (rise 4 3 2)) (complementIndex1 t) (complementIndex1 s) = _
  rw [rise3_2]
  fin_cases s <;> fin_cases t <;> decide +kernel

def E1_2 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 1], ![0, 0, 0, 0]]


theorem dualDrop1_2 : compress enum1 (dualDrop 4 1 2) = E1_2 := by
  ext s t
  change drop 4 (4-1) 2 ((states1 t).complement) ((states1 s).complement) = _
  rw [states1_complement, states1_complement]
  change (compress enum3 (drop 4 3 2)) (complementIndex1 t) (complementIndex1 s) = _
  rw [drop3_2]
  fin_cases s <;> fin_cases t <;> decide +kernel


end HiddenCircuits.Small
