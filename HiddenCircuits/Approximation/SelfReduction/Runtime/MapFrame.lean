import HiddenCircuits.Approximation.SelfReduction.Runtime.WordEmit
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorProduct

/-! A frame for repeatedly calling any supplied actual clean finite bit program.
The callback's entire finite work area is separate from list-loop storage. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def mapLeft (k : ℕ) : Fin (k+1) ↪ Fin (k+5) where
  toFun i := i.castAdd 4
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin (k+5) => x.val) h)

def mapRight (k : ℕ) : Fin 4 ↪ Fin (k+5) where
  toFun i := i.natAdd (k+1)
  inj' := by intro i j h; apply Fin.ext; have hh := congrArg (fun x : Fin (k+5) => x.val) h; simp at hh; omega

 theorem mapLeft_ne_right (k : ℕ) (i : Fin (k+1)) (j : Fin 4) : mapLeft k i ≠ mapRight k j := by
  intro h
  have hh := congrArg (fun x : Fin (k+5) => x.val) h
  simp [mapLeft,mapRight] at hh
  omega

 theorem mapRight_ne_left (k : ℕ) (j : Fin 4) (i : Fin (k+1)) : mapRight k j ≠ mapLeft k i :=
  (mapLeft_ne_right k i j).symm

@[simp] theorem mapLeft_zero (k : ℕ) : mapLeft k 0=(0 : Fin (k+5)) := rfl

@[simp] theorem mapLeft_eq_zero (k : ℕ) (i : Fin (k+1)) : mapLeft k i=0 ↔ i=0 := by
  constructor
  · intro h
    apply Fin.ext
    exact congrArg (fun x : Fin (k+5) => x.val) h
  · intro h; subst i; rfl

@[simp] theorem mapRight_ne_zero (k : ℕ) (i : Fin 4) : mapRight k i ≠ 0 := by
  simpa only [mapLeft_zero] using mapRight_ne_left k i 0

def mapStore (k : ℕ) (word source output tmp flag : BitString) : Store (k+4) :=
  Fin.addCases (m := k+1) (n := 4) (Function.update (fun _ : Fin (k+1) => []) 0 word)
    (Fin.cases source (Fin.cases output (Fin.cases tmp (fun _ => flag))))

@[simp] theorem mapStore_left (k : ℕ) (word source output tmp flag : BitString) (i : Fin (k+1)) :
    mapStore k word source output tmp flag (mapLeft k i)=if i=0 then word else [] := by
  simp [mapStore,mapLeft,Function.update_apply]

@[simp] theorem mapStore_right (k : ℕ) (word source output tmp flag : BitString) (i : Fin 4) :
    mapStore k word source output tmp flag (mapRight k i)=
      Fin.cases source (Fin.cases output (Fin.cases tmp (fun _ => flag))) i := by
  simp [mapStore,mapRight]

@[simp 1100] theorem mapStore_source (k : ℕ) (word source output tmp flag : BitString) :
    mapStore k word source output tmp flag (mapRight k 0)=source := by rw [mapStore_right]; rfl

@[simp 1100] theorem mapStore_output (k : ℕ) (word source output tmp flag : BitString) :
    mapStore k word source output tmp flag (mapRight k 1)=output := by rw [mapStore_right]; rfl

@[simp 1100] theorem mapStore_tmp (k : ℕ) (word source output tmp flag : BitString) :
    mapStore k word source output tmp flag (mapRight k 2)=tmp := by rw [mapStore_right]; rfl

@[simp 1100] theorem mapStore_flag (k : ℕ) (word source output tmp flag : BitString) :
    mapStore k word source output tmp flag (mapRight k 3)=flag := by rw [mapStore_right]; rfl

@[simp] theorem mapStore_zero (k : ℕ) (word source output tmp flag : BitString) :
    mapStore k word source output tmp flag 0=word := by
  rw [← mapLeft_zero k, mapStore_left]
  simp

 theorem mapStore_ext {k : ℕ} {s t : Store (k+4)}
    (hl : ∀ i, s (mapLeft k i)=t (mapLeft k i))
    (hr : ∀ i, s (mapRight k i)=t (mapRight k i)) : s=t := by
  funext i
  exact Fin.addCases (m := k+1) (n := 4) hl hr i

@[simp] theorem mapStore_update_zero (k : ℕ) (word source output tmp flag new : BitString) :
    Function.update (mapStore k word source output tmp flag) 0 new=mapStore k new source output tmp flag := by
  apply mapStore_ext
  · intro i
    by_cases hi : i=0 <;> simp [Function.update_apply,hi]
  · intro i
    simp [Function.update_of_ne (mapRight_ne_zero k i)]

@[simp] theorem mapStore_update_source (k : ℕ) (word source output tmp flag new : BitString) :
    Function.update (mapStore k word source output tmp flag) (mapRight k 0) new=
      mapStore k word new output tmp flag := by
  apply mapStore_ext
  · intro i; simp [Function.update_of_ne (mapLeft_ne_right k i 0)]
  · intro i; fin_cases i <;> simp [Function.update_apply,(mapRight k).injective.eq_iff] <;> rfl

@[simp] theorem mapStore_update_output (k : ℕ) (word source output tmp flag new : BitString) :
    Function.update (mapStore k word source output tmp flag) (mapRight k 1) new=
      mapStore k word source new tmp flag := by
  apply mapStore_ext
  · intro i; simp [Function.update_of_ne (mapLeft_ne_right k i 1)]
  · intro i; fin_cases i <;> simp [Function.update_apply,(mapRight k).injective.eq_iff] <;> rfl

@[simp] theorem mapStore_update_flag (k : ℕ) (word source output tmp flag new : BitString) :
    Function.update (mapStore k word source output tmp flag) (mapRight k 3) new=
      mapStore k word source output tmp new := by
  apply mapStore_ext
  · intro i; simp [Function.update_of_ne (mapLeft_ne_right k i 3)]
  · intro i; fin_cases i <;> simp [Function.update_apply,(mapRight k).injective.eq_iff] <;> rfl

end HiddenCircuits.Approximation.SelfReduction.Runtime
