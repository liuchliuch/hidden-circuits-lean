import HiddenCircuits.GraphReduction.UnitIntervalBitRecognition

/-! Recognition needs only the residual alive mask. Failed rounds stutter;
there is no need to accumulate a global order or keep a failure flag. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalResidualRecognition
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- Keep the first passing root's residual. No passing root leaves the state unchanged. -/
def step (alive : List Bool) : List Bool :=
  match UnitIntervalBitRecognition.goodRoot G alive with
  | none => alive
  | some root => UnitIntervalBitRecognition.eraseList alive (UnitIntervalBitRecognition.component G alive root)

def run : ℕ → List Bool → List Bool
  | 0,alive => alive
  | fuel+1,alive => run fuel (step G alive)

lemma goodRoot_empty (alive : List Bool) (h : UnitIntervalBitMasks.count (n:=n) alive = 0) :
    UnitIntervalBitRecognition.goodRoot G alive = none := by
  have hm : UnitIntervalBitMasks.members (n:=n) alive = [] := by
    apply List.length_eq_zero_iff.mp
    simpa only [UnitIntervalBitMasks.count,UnitIntervalBitMasks.members,List.countP_eq_length_filter] using h
  simp [UnitIntervalBitRecognition.goodRoot,hm]

lemma search_empty (fuel : ℕ) (alive : List Bool) (h : UnitIntervalBitMasks.count (n:=n) alive = 0) :
    UnitIntervalBitRecognition.search G fuel alive = some [] := by
  cases fuel <;> simp [UnitIntervalBitRecognition.search,h]
lemma search_stuck (fuel : ℕ) (alive : List Bool) (h : UnitIntervalBitMasks.count (n:=n) alive ≠ 0)
    (hr : UnitIntervalBitRecognition.goodRoot G alive = none) :
    UnitIntervalBitRecognition.search G fuel alive = none := by
  cases fuel <;> simp [UnitIntervalBitRecognition.search,h,hr]

/-- Stuttering residual iteration and the list-producing recognizer have
identical acceptance for every fuel, including premature exhaustion. -/
theorem run_accept_iff (fuel : ℕ) (alive : List Bool) :
    UnitIntervalBitMasks.count (n:=n) (run G fuel alive) = 0 ↔
      (UnitIntervalBitRecognition.search G fuel alive).isSome = true := by
  induction fuel generalizing alive with
  | zero =>
    by_cases h : UnitIntervalBitMasks.count (n:=n) alive = 0
    · simp [run,UnitIntervalBitRecognition.search,h]
    · simp [run,UnitIntervalBitRecognition.search,h]
  | succ fuel ih =>
    rw [run,ih]
    by_cases h : UnitIntervalBitMasks.count (n:=n) alive = 0
    · rw [step,goodRoot_empty G alive h]
      simp [search_empty G fuel alive h,UnitIntervalBitRecognition.search,h]
    · cases hr : UnitIntervalBitRecognition.goodRoot G alive with
      | none =>
        rw [step,hr]
        simp [search_stuck G fuel alive h hr,UnitIntervalBitRecognition.search,h,hr]
      | some root => simp [step,hr,UnitIntervalBitRecognition.search,h]

/-- The residual-only ordinary graph recognizer accepts precisely the real unit
interval class after the original n rounds. -/
theorem accepts_iff :
    UnitIntervalBitMasks.count (n:=n) (run G n (List.replicate n true)) = 0 ↔
      RealUnitInterval.UnitIntervalGraph G := by
  rw [run_accept_iff]
  exact UnitIntervalBitRecognition.recognize_iff G

end HiddenCircuits.GraphReduction.UnitIntervalResidualRecognition
