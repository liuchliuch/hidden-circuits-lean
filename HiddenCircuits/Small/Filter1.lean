import HiddenCircuits.Small.Dual1
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def Suffix1_19 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 0]]


theorem suffix1_19 : ([R1_2]).prod = Suffix1_19 := by
  decide +kernel

def Suffix1_18 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 0]]


theorem suffix1_18 : ([D1_2, R1_2]).prod = Suffix1_18 := by
  rw [List.prod_cons, suffix1_19]
  decide +kernel

def Suffix1_17 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 0]]


theorem suffix1_17 : ([E1_2, D1_2, R1_2]).prod = Suffix1_17 := by
  rw [List.prod_cons, suffix1_18]
  decide +kernel

def Suffix1_16 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 0]]


theorem suffix1_16 : ([R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_16 := by
  rw [List.prod_cons, suffix1_17]
  decide +kernel

def Suffix1_15 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_15 : ([R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_15 := by
  rw [List.prod_cons, suffix1_16]
  decide +kernel

def Suffix1_14 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_14 : ([R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_14 := by
  rw [List.prod_cons, suffix1_15]
  decide +kernel

def Suffix1_13 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_13 : ([B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_13 := by
  rw [List.prod_cons, suffix1_14]
  decide +kernel

def Suffix1_12 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_12 : ([R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_12 := by
  rw [List.prod_cons, suffix1_13]
  decide +kernel

def Suffix1_11 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_11 : ([D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_11 := by
  rw [List.prod_cons, suffix1_12]
  decide +kernel

def Suffix1_10 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_10 : ([R1_1, D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_10 := by
  rw [List.prod_cons, suffix1_11]
  decide +kernel

def Suffix1_9 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_9 : ([R1_2, R1_1, D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_9 := by
  rw [List.prod_cons, suffix1_10]
  decide +kernel

def Suffix1_8 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_8 : ([D1_2, R1_2, R1_1, D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_8 := by
  rw [List.prod_cons, suffix1_9]
  decide +kernel

def Suffix1_7 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_7 : ([E1_2, D1_2, R1_2, R1_1, D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_7 := by
  rw [List.prod_cons, suffix1_8]
  decide +kernel

def Suffix1_6 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_6 : ([R1_0, E1_2, D1_2, R1_2, R1_1, D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_6 := by
  rw [List.prod_cons, suffix1_7]
  decide +kernel

def Suffix1_5 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_5 : ([R1_1, R1_0, E1_2, D1_2, R1_2, R1_1, D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_5 := by
  rw [List.prod_cons, suffix1_6]
  decide +kernel

def Suffix1_4 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_4 : ([R1_2, R1_1, R1_0, E1_2, D1_2, R1_2, R1_1, D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_4 := by
  rw [List.prod_cons, suffix1_5]
  decide +kernel

def Suffix1_3 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_3 : ([B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2, R1_1, D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_3 := by
  rw [List.prod_cons, suffix1_4]
  decide +kernel

def Suffix1_2 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_2 : ([R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2, R1_1, D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_2 := by
  rw [List.prod_cons, suffix1_3]
  decide +kernel

def Suffix1_1 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_1 : ([D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2, R1_1, D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_1 := by
  rw [List.prod_cons, suffix1_2]
  decide +kernel

def Suffix1_0 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem suffix1_0 : ([R1_1, D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2, R1_1, D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Suffix1_0 := by
  rw [List.prod_cons, suffix1_1]
  decide +kernel

def Theta1 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem localFilter1 : compress enum1 (localFilter 1) = Theta1 := by
  rw [localFilter, compress_smul, compress_word]
  simp only [filterWord, filterT, filterZ, filterJ, List.map_append, List.map_cons, List.map_nil, Letter.matrix, dualRise1_1, drop1_2, dualDrop1_2, rise1_0, rise1_1, rise1_2]
  change (1 / 64 : ℚ) • ([R1_1, D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2, R1_1, D1_2, R1_2, B1_1, R1_2, R1_1, R1_0, E1_2, D1_2, R1_2]).prod = Theta1
  rw [suffix1_0]
  decide +kernel


end HiddenCircuits.Small
