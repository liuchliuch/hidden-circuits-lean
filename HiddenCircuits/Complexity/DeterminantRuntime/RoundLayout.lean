import HiddenCircuits.Complexity.OracleMove

/-! Fixed 31-stack layout for one exact determinant recurrence round. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.Round
open OracleBlock

def state (n : ℕ) (a b c : BitString) (k clock : ℕ)
    (product trace nextCoefficient nextMatrix : BitString) : Store 30 := fun q =>
  if q.val=0 then List.replicate n true else if q.val=1 then a else
  if q.val=2 then b else if q.val=3 then c else if q.val=4 then List.replicate k true else
  if q.val=5 then List.replicate clock true else if q.val=6 then product else
  if q.val=7 then trace else if q.val=8 then nextCoefficient else if q.val=9 then nextMatrix else []

def store (n : ℕ) (a b c : BitString) (k clock : ℕ) : Store 30 :=
  state n a b c k clock [] [] [] []

def productPorts : Fin 25 ↪ Fin 31 where
  toFun := ![0,10,11,12,13,14,15,6,1,2,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def tracePorts : Fin 16 ↪ Fin 31 where
  toFun := ![0,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def coefficientPorts : Fin 13 ↪ Fin 31 where
  toFun := ![4,7,8,10,11,12,13,14,15,16,17,18,19]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def scalarPorts : Fin 25 ↪ Fin 31 where
  toFun := ![0,10,11,12,13,14,15,9,6,8,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

end HiddenCircuits.Complexity.DeterminantRuntime.Round
