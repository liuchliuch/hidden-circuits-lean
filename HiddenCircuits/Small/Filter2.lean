import HiddenCircuits.Small.Dual2
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def Suffix2_19 : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 2]]


theorem suffix2_19 : ([R2_2]).prod = Suffix2_19 := by
  decide +kernel

def Suffix2_18 : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0]]


theorem suffix2_18 : ([D2_2, R2_2]).prod = Suffix2_18 := by
  rw [List.prod_cons, suffix2_19]
  decide +kernel

def Suffix2_17 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]


theorem suffix2_17 : ([E2_2, D2_2, R2_2]).prod = Suffix2_17 := by
  rw [List.prod_cons, suffix2_18]
  decide +kernel

def Suffix2_16 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, -4, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]


theorem suffix2_16 : ([R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_16 := by
  rw [List.prod_cons, suffix2_17]
  decide +kernel

def Suffix2_15 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, -4, 0, 0], ![0, 0, 0, -4, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]


theorem suffix2_15 : ([R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_15 := by
  rw [List.prod_cons, suffix2_16]
  decide +kernel

def Suffix2_14 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, -4, 0, 0], ![0, 0, 0, -4, 0, 0], ![0, 0, 0, -4, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]


theorem suffix2_14 : ([R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_14 := by
  rw [List.prod_cons, suffix2_15]
  decide +kernel

def Suffix2_13 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, 8, 0, 0], ![0, 0, 0, -8, 0, 0], ![0, 0, 0, -8, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0]]


theorem suffix2_13 : ([B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_13 := by
  rw [List.prod_cons, suffix2_14]
  decide +kernel

def Suffix2_12 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, 8, 0, 0], ![0, 0, 0, -8, 0, 0], ![0, 0, 0, -8, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 8, 0, 0, 0, 0]]


theorem suffix2_12 : ([R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_12 := by
  rw [List.prod_cons, suffix2_13]
  decide +kernel

def Suffix2_11 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, 8, 0, 0], ![0, 0, 0, -8, 0, 0], ![0, 0, 0, -8, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]


theorem suffix2_11 : ([D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_11 := by
  rw [List.prod_cons, suffix2_12]
  decide +kernel

def Suffix2_10 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, 8, 0, 0], ![0, 0, 0, 8, 0, 0], ![0, 0, 0, -8, 0, 0], ![0, 8, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0]]


theorem suffix2_10 : ([R2_1, D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_10 := by
  rw [List.prod_cons, suffix2_11]
  decide +kernel

def Suffix2_9 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, 8, 0, 0], ![0, 0, 0, 8, 0, 0], ![0, 0, 0, 8, 0, 0], ![0, 8, 0, 0, 0, 0], ![0, 8, 0, 0, 0, 0], ![0, 8, 0, 0, 0, 0]]


theorem suffix2_9 : ([R2_2, R2_1, D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_9 := by
  rw [List.prod_cons, suffix2_10]
  decide +kernel

def Suffix2_8 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, 8, 0, 0], ![0, 0, 0, 8, 0, 0], ![0, 0, 0, 8, 0, 0], ![0, 8, 0, 0, 0, 0], ![0, 8, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]


theorem suffix2_8 : ([D2_2, R2_2, R2_1, D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_8 := by
  rw [List.prod_cons, suffix2_9]
  decide +kernel

def Suffix2_7 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 16, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 16, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]


theorem suffix2_7 : ([E2_2, D2_2, R2_2, R2_1, D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_7 := by
  rw [List.prod_cons, suffix2_8]
  decide +kernel

def Suffix2_6 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, -32, 0, 0, 0, 0], ![0, 0, 0, 16, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 16, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]


theorem suffix2_6 : ([R2_0, E2_2, D2_2, R2_2, R2_1, D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_6 := by
  rw [List.prod_cons, suffix2_7]
  decide +kernel

def Suffix2_5 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, -32, 0, 0, 0, 0], ![0, -32, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 32, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]


theorem suffix2_5 : ([R2_1, R2_0, E2_2, D2_2, R2_2, R2_1, D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_5 := by
  rw [List.prod_cons, suffix2_6]
  decide +kernel

def Suffix2_4 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, -32, 0, 0, 0, 0], ![0, -32, 0, 0, 0, 0], ![0, -32, 0, 0, 0, 0], ![0, 0, 0, 32, 0, 0], ![0, 0, 0, 32, 0, 0], ![0, 0, 0, 0, 0, 0]]


theorem suffix2_4 : ([R2_2, R2_1, R2_0, E2_2, D2_2, R2_2, R2_1, D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_4 := by
  rw [List.prod_cons, suffix2_5]
  decide +kernel

def Suffix2_3 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 64, 0, 0, 0, 0], ![0, -64, 0, 0, 0, 0], ![0, -64, 0, 0, 0, 0], ![0, 0, 0, 32, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 32, 0, 0]]


theorem suffix2_3 : ([B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2, R2_1, D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_3 := by
  rw [List.prod_cons, suffix2_4]
  decide +kernel

def Suffix2_2 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 64, 0, 0, 0, 0], ![0, -64, 0, 0, 0, 0], ![0, -64, 0, 0, 0, 0], ![0, 0, 0, 32, 0, 0], ![0, 0, 0, 32, 0, 0], ![0, 0, 0, 64, 0, 0]]


theorem suffix2_2 : ([R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2, R2_1, D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_2 := by
  rw [List.prod_cons, suffix2_3]
  decide +kernel

def Suffix2_1 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 64, 0, 0, 0, 0], ![0, -64, 0, 0, 0, 0], ![0, -64, 0, 0, 0, 0], ![0, 0, 0, 32, 0, 0], ![0, 0, 0, 32, 0, 0], ![0, 0, 0, 0, 0, 0]]


theorem suffix2_1 : ([D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2, R2_1, D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_1 := by
  rw [List.prod_cons, suffix2_2]
  decide +kernel

def Suffix2_0 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 64, 0, 0, 0, 0], ![0, 64, 0, 0, 0, 0], ![0, -64, 0, 0, 0, 0], ![0, 0, 0, 64, 0, 0], ![0, 0, 0, 32, 0, 0], ![0, 0, 0, 32, 0, 0]]


theorem suffix2_0 : ([R2_1, D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2, R2_1, D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Suffix2_0 := by
  rw [List.prod_cons, suffix2_1]
  decide +kernel

def Theta2 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, (1/2), 0, 0], ![0, 0, 0, (1/2), 0, 0]]


theorem localFilter2 : compress enum2 (localFilter 2) = Theta2 := by
  rw [localFilter, compress_smul, compress_word]
  simp only [filterWord, filterT, filterZ, filterJ, List.map_append, List.map_cons, List.map_nil, Letter.matrix, dualRise2_1, drop2_2, dualDrop2_2, rise2_0, rise2_1, rise2_2]
  change (1 / 64 : ℚ) • ([R2_1, D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2, R2_1, D2_2, R2_2, B2_1, R2_2, R2_1, R2_0, E2_2, D2_2, R2_2]).prod = Theta2
  rw [suffix2_0]
  decide +kernel


end HiddenCircuits.Small
