import HiddenCircuits.Small.Compounds2
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def B2_0 : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, -2], ![0, 1, 0, 1, 0, 0], ![0, 0, 1, 0, 1, 0], ![0, 0, 0, 0, 0, 2]]


theorem dualRise2_0 : compress enum2 (dualRise 4 2 0) = B2_0 := by
  ext s t
  change rise 4 (4-2) 0 ((states2 t).complement) ((states2 s).complement) = _
  rw [states2_complement, states2_complement]
  change (compress enum2 (rise 4 2 0)) (complementIndex2 t) (complementIndex2 s) = _
  rw [rise2_0]
  fin_cases s <;> fin_cases t <;> decide +kernel

def E2_0 : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 0, 0, 0, 0, -2], ![0, 1, 0, 1, 0, 0], ![0, 0, 1, 0, 1, 2], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]


theorem dualDrop2_0 : compress enum2 (dualDrop 4 2 0) = E2_0 := by
  ext s t
  change drop 4 (4-2) 0 ((states2 t).complement) ((states2 s).complement) = _
  rw [states2_complement, states2_complement]
  change (compress enum2 (drop 4 2 0)) (complementIndex2 t) (complementIndex2 s) = _
  rw [drop2_0]
  fin_cases s <;> fin_cases t <;> decide +kernel

def B2_1 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, -2, 0, 0, 0], ![1, 1, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1]]


theorem dualRise2_1 : compress enum2 (dualRise 4 2 1) = B2_1 := by
  ext s t
  change rise 4 (4-2) 1 ((states2 t).complement) ((states2 s).complement) = _
  rw [states2_complement, states2_complement]
  change (compress enum2 (rise 4 2 1)) (complementIndex2 t) (complementIndex2 s) = _
  rw [rise2_1]
  fin_cases s <;> fin_cases t <;> decide +kernel

def E2_1 : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 1, 2, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0]]


theorem dualDrop2_1 : compress enum2 (dualDrop 4 2 1) = E2_1 := by
  ext s t
  change drop 4 (4-2) 1 ((states2 t).complement) ((states2 s).complement) = _
  rw [states2_complement, states2_complement]
  change (compress enum2 (drop 4 2 1)) (complementIndex2 t) (complementIndex2 s) = _
  rw [drop2_1]
  fin_cases s <;> fin_cases t <;> decide +kernel

def B2_2 : Matrix (Fin 6) (Fin 6) ℚ := ![![2, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 1]]


theorem dualRise2_2 : compress enum2 (dualRise 4 2 2) = B2_2 := by
  ext s t
  change rise 4 (4-2) 2 ((states2 t).complement) ((states2 s).complement) = _
  rw [states2_complement, states2_complement]
  change (compress enum2 (rise 4 2 2)) (complementIndex2 t) (complementIndex2 s) = _
  rw [rise2_2]
  fin_cases s <;> fin_cases t <;> decide +kernel

def E2_2 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1]]


theorem dualDrop2_2 : compress enum2 (dualDrop 4 2 2) = E2_2 := by
  ext s t
  change drop 4 (4-2) 2 ((states2 t).complement) ((states2 s).complement) = _
  rw [states2_complement, states2_complement]
  change (compress enum2 (drop 4 2 2)) (complementIndex2 t) (complementIndex2 s) = _
  rw [drop2_2]
  fin_cases s <;> fin_cases t <;> decide +kernel


end HiddenCircuits.Small
