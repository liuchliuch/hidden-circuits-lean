import HiddenCircuits.Small.Dual2


namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000


def MixSuffix5 : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 2]]


theorem mixSuffix5 : ([R2_2]).prod = MixSuffix5 := by
  decide +kernel

def MixSuffix4 : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 2, 0, -4], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0]]


theorem mixSuffix4 : ([R2_1, R2_2]).prod = MixSuffix4 := by
  rw [List.prod_cons, mixSuffix5]
  decide +kernel

def MixSuffix3 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, -2, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 0, 2, 0, -4], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0]]


theorem mixSuffix3 : ([B2_1, R2_1, R2_2]).prod = MixSuffix3 := by
  rw [List.prod_cons, mixSuffix4]
  decide +kernel

def MixSuffix2 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, -2, 0, 4, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, -4, 0, 0], ![2, 0, 0, 2, 0, -4], ![0, 2, 0, 0, 0, 0], ![0, 0, 0, 4, 0, 0]]


theorem mixSuffix2 : ([B2_0, B2_1, R2_1, R2_2]).prod = MixSuffix2 := by
  rw [List.prod_cons, mixSuffix3]
  decide +kernel

def MixSuffix1 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, 8, 0, 0], ![0, -2, 0, 4, 0, 0], ![0, 0, 0, -8, 0, 0], ![2, 0, 0, 2, 0, -4], ![0, 0, 0, 0, 0, 0], ![0, 2, 0, 4, 0, 0]]


theorem mixSuffix1 : ([B2_1, B2_0, B2_1, R2_1, R2_2]).prod = MixSuffix1 := by
  rw [List.prod_cons, mixSuffix2]
  decide +kernel

def MixSuffix0 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, -2, 0, 4, 0, 0], ![0, -2, 0, 4, 0, 0], ![0, 0, 0, -8, 0, 0], ![0, 4, 0, 8, 0, 0], ![0, 2, 0, 4, 0, 0], ![0, 2, 0, 4, 0, 0]]


theorem mixSuffix0 : ([D2_1, B2_1, B2_0, B2_1, R2_1, R2_2]).prod = MixSuffix0 := by
  rw [List.prod_cons, mixSuffix1]
  decide +kernel
end HiddenCircuits.Small
