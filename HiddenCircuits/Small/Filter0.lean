import HiddenCircuits.Small.Dual0
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def Suffix0_19 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem suffix0_19 : ([R0_2]).prod = Suffix0_19 := by
  decide +kernel

def Suffix0_18 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem suffix0_18 : ([D0_2, R0_2]).prod = Suffix0_18 := by
  rw [List.prod_cons, suffix0_19]
  decide +kernel

def Suffix0_17 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_17 : ([E0_2, D0_2, R0_2]).prod = Suffix0_17 := by
  rw [List.prod_cons, suffix0_18]
  decide +kernel

def Suffix0_16 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_16 : ([R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_16 := by
  rw [List.prod_cons, suffix0_17]
  decide +kernel

def Suffix0_15 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_15 : ([R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_15 := by
  rw [List.prod_cons, suffix0_16]
  decide +kernel

def Suffix0_14 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_14 : ([R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_14 := by
  rw [List.prod_cons, suffix0_15]
  decide +kernel

def Suffix0_13 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_13 : ([B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_13 := by
  rw [List.prod_cons, suffix0_14]
  decide +kernel

def Suffix0_12 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_12 : ([R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_12 := by
  rw [List.prod_cons, suffix0_13]
  decide +kernel

def Suffix0_11 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_11 : ([D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_11 := by
  rw [List.prod_cons, suffix0_12]
  decide +kernel

def Suffix0_10 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_10 : ([R0_1, D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_10 := by
  rw [List.prod_cons, suffix0_11]
  decide +kernel

def Suffix0_9 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_9 : ([R0_2, R0_1, D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_9 := by
  rw [List.prod_cons, suffix0_10]
  decide +kernel

def Suffix0_8 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_8 : ([D0_2, R0_2, R0_1, D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_8 := by
  rw [List.prod_cons, suffix0_9]
  decide +kernel

def Suffix0_7 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_7 : ([E0_2, D0_2, R0_2, R0_1, D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_7 := by
  rw [List.prod_cons, suffix0_8]
  decide +kernel

def Suffix0_6 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_6 : ([R0_0, E0_2, D0_2, R0_2, R0_1, D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_6 := by
  rw [List.prod_cons, suffix0_7]
  decide +kernel

def Suffix0_5 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_5 : ([R0_1, R0_0, E0_2, D0_2, R0_2, R0_1, D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_5 := by
  rw [List.prod_cons, suffix0_6]
  decide +kernel

def Suffix0_4 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_4 : ([R0_2, R0_1, R0_0, E0_2, D0_2, R0_2, R0_1, D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_4 := by
  rw [List.prod_cons, suffix0_5]
  decide +kernel

def Suffix0_3 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_3 : ([B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2, R0_1, D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_3 := by
  rw [List.prod_cons, suffix0_4]
  decide +kernel

def Suffix0_2 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_2 : ([R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2, R0_1, D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_2 := by
  rw [List.prod_cons, suffix0_3]
  decide +kernel

def Suffix0_1 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_1 : ([D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2, R0_1, D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_1 := by
  rw [List.prod_cons, suffix0_2]
  decide +kernel

def Suffix0_0 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem suffix0_0 : ([R0_1, D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2, R0_1, D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Suffix0_0 := by
  rw [List.prod_cons, suffix0_1]
  decide +kernel

def Theta0 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem localFilter0 : compress enum0 (localFilter 0) = Theta0 := by
  rw [localFilter, compress_smul, compress_word]
  simp only [filterWord, filterT, filterZ, filterJ, List.map_append, List.map_cons, List.map_nil, Letter.matrix, dualRise0_1, drop0_2, dualDrop0_2, rise0_0, rise0_1, rise0_2]
  change (1 / 64 : ℚ) • ([R0_1, D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2, R0_1, D0_2, R0_2, B0_1, R0_2, R0_1, R0_0, E0_2, D0_2, R0_2]).prod = Theta0
  rw [suffix0_0]
  decide +kernel


end HiddenCircuits.Small
