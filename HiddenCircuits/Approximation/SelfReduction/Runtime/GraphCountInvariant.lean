import HiddenCircuits.Approximation.SelfReduction.UniformParameters

/-! Analysis-only invariant restriction of the actual counting experiment.
The machine never receives a class certificate: the restricted process projects
pointwise to the same underlying state, samples, choices and output estimate. -/
namespace HiddenCircuits.Approximation.SelfReduction
namespace CountReduction
variable {S α : Type*} {b : ℕ}

def restrict (R : CountReduction S b) (P : S → Prop)
    (hP : ∀s,P s → ∀j,P (R.child s j)) : CountReduction {s // P s} b where
  count s := R.count s.val
  rank s := R.rank s.val
  child s j := ⟨R.child s.val j,hP s.val s.property j⟩
  leaf_count s := R.leaf_count s.val
  child_rank s j := R.child_rank s.val j
  recurrence s := R.recurrence s.val

theorem restrict_estimate (R : CountReduction S b) (P : S → Prop)
    (hP : ∀s,P s → ∀j,P (R.child s j))
    (sample : S → α → Option (Fin (b+1))) (T h d : ℕ)
    (s : {s // P s}) (tapes : Fin d → StageTape α T h) :
    countingEstimate (R.restrict P hP) (fun s => sample s.val) T h d s tapes=
      countingEstimate R sample T h d s.val tapes := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih =>
    change countingEstimate (R.restrict P hP) (fun s => sample s.val) T h d
      ((R.restrict P hP).child s (selectedBranch b T h (fun s => sample s.val) s (tapes 0)))
      (fun i => tapes i.succ) / countingFrequency (fun s => sample s.val) T h s (tapes 0)=_
    rw [ih]
    rfl

/-- Near-uniformity is required only on the actual deletion-closed class.
It is not required on arbitrary off-promise graphs and is never a runtime input. -/
theorem oversized_failure_on_invariant [Fintype α] [Nonempty α]
    (R : CountReduction S b) (P : S → Prop)
    (hP : ∀s,P s → ∀j,P (R.child s j))
    (sample : S → α → Option (Fin (b+1))) (d r k T h : ℕ)
    (hT : accuracyBudget b d r ≤ T) (hh : confidenceBudget b d k ≤ h)
    (hbias : ∀s,P s → 0 < R.count s → 0 < R.rank s → ∀j,
      |probability (fun a => sample s a=some j)-R.branchProbability s j| ≤ 1/(2^T:ℚ))
    (s : S) (hs : P s) (hc : 0 < R.count s) (hr : R.rank s=d) :
    probability (fun tape => ¬RelativeEstimate (R.count s) r
      (countingEstimate R sample T h d s tape)) ≤ 1/(2^k:ℚ) := by
  have hh' := counting_oversized_dyadic_failure (R.restrict P hP) (fun s => sample s.val)
    d r k T h hT hh (fun s hc hr j => hbias s.val s.property hc hr j) ⟨s,hs⟩ hc hr
  simpa only [restrict_estimate] using hh'
end CountReduction
end HiddenCircuits.Approximation.SelfReduction
