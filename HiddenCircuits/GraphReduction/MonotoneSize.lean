import HiddenCircuits.GraphReduction.MonotoneGauge

/-! Literal class sizes and the polynomial-size Section 9 graph-query family. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Boundary deletion leaves exactly 2ph original vertices on the even color class. -/
theorem retainedEven_card {p h : ℕ} (hh : 0<h) (S T : State (2*p) p) :
    Fintype.card (RetainedEven p h S T) = 2*p*h := by
  classical
  let e : RetainedEven p h S T ≃ Σ r : Fin (h+1), {x // retainedTrack S T r x} :=
    Equiv.subtypeProdEquivSigmaSubtype (retainedTrack S T)
  rw [Fintype.card_congr e,Fintype.card_sigma]
  have hz : (0 : Fin (h+1)) ≠ Fin.last h := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero,Fin.val_last] at hv
    omega
  have hv (r : Fin (h+1)) : Fintype.card {x // retainedTrack S T r x} +
      (if r=0 then p else 0) + (if r=Fin.last h then p else 0) = 2*p := by
    by_cases hr0 : r=0
    · subst r
      rw [retainedTrack_first_card hh]
      simp [hz]
      omega
    · by_cases hrh : r=Fin.last h
      · subst r
        rw [retainedTrack_last_card hh]
        simp [hz.symm]
        omega
      · rw [retainedTrack_middle_card S T r
          (by intro he; exact hr0 (Fin.ext he))
          (by intro he; exact hrh (Fin.ext he))]
        simp [hr0,hrh]
  have hs := Finset.sum_congr (s₁:=Finset.univ) rfl (fun r _ => hv r)
  simp only [Finset.sum_add_distrib] at hs
  simp at hs
  nlinarith

 theorem oddVertex_card (p h : ℕ) : Fintype.card (OddVertex (2*p) h) = 2*p*h := by
  simp only [OddVertex,Fintype.card_prod,Fintype.card_fin]
  ring

/-- The exact number of vertices of each genuine unweighted query graph. -/
theorem monotoneQuery_card {p h : ℕ} (hh : 0<h) (S T : State (2*p) p) (s : ℕ) :
    Fintype.card (ProbePart (RetainedEven p h S T) (Fin h) s ⊕
      ProbePart (OddVertex (2*p) h) (Fin h) s) = 4*p*h+2*h*s := by
  rw [probeGraph_card,retainedEven_card hh,oddVertex_card,Fintype.card_fin]
  ring

/-- The concrete Section 9 probe polynomial has degree at most 2ph. -/
theorem monotoneProbe_degree {p h : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) :
    (probePolynomial (retainedQueryRelation pairs S T)
      (retainedEvenAttachment S T) oddAttachment).natDegree ≤ 2*p*h := by
  simpa only [retainedEven_card hh] using probePolynomial_degree
    (retainedQueryRelation pairs S T) (retainedEvenAttachment S T) oddAttachment

/-- Exactly 2ph+1 samples, with the same size parameter at every probe pair. -/
theorem monotoneProbe_query_count (p h : ℕ) : Fintype.card (Fin (2*p*h+1)) = 2*p*h+1 :=
  Fintype.card_fin _

/-- The paper's explicit polynomial query bound 4ph(h+1). -/
theorem monotoneProbe_query_size {p h : ℕ} (hh : 0<h) (S T : State (2*p) p)
    (s : Fin (2*p*h+1)) :
    Fintype.card (ProbePart (RetainedEven p h S T) (Fin h) s.val ⊕
      ProbePart (OddVertex (2*p) h) (Fin h) s.val) ≤ 4*p*h*(h+1) := by
  rw [monotoneQuery_card hh]
  have hs : s.val≤2*p*h := by omega
  calc
    4*p*h+2*h*s.val ≤ 4*p*h+2*h*(2*p*h) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hs) _
    _ = _ := by ring

end HiddenCircuits.GraphReduction
