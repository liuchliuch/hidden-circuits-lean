import HiddenCircuits.GraphReduction.Runtime.WordGraph.RecoveryBounds

/-! Reconstructed closed polynomials for the literal graph interpolation grid. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
open Complexity Polynomial
noncomputable def degreeP : Polynomial ℕ := X^3
noncomputable def heightP : Polynomial ℕ := X*(degreeP+1)
noncomputable def innerP : Polynomial ℕ := 2*X*heightP
noncomputable def vertexP : Polynomial ℕ := 4*X*heightP*(heightP+1)
noncomputable def countP : Polynomial ℕ := (degreeP+1)*(innerP+1)
noncomputable def termP : Polynomial ℕ := (vertexP+1)^2+degreeP^2+innerP^2+innerP^2*heightP+2
noncomputable def componentP : Polynomial ℕ := termP+2
noncomputable def accumulatorP : Polynomial ℕ := 1+(termP+1)*countP+termP+2
noncomputable def answerP : Polynomial ℕ := (vertexP+1)^2+2
@[simp] lemma degreeP_eval (L : ℕ) : degreeP.eval L=Recovery.outerBound L := by simp [degreeP,Recovery.outerBound]
@[simp] lemma heightP_eval (L : ℕ) : heightP.eval L=Recovery.heightBound L := by simp [heightP,Recovery.heightBound]
@[simp] lemma innerP_eval (L : ℕ) : innerP.eval L=Recovery.innerBound L := by simp [innerP,Recovery.innerBound]
@[simp] lemma vertexP_eval (L : ℕ) : vertexP.eval L=Recovery.vertexBound L := by simp [vertexP,Recovery.vertexBound]
@[simp] lemma countP_eval (L : ℕ) : countP.eval L=Recovery.queryCountBound L := by simp [countP,Recovery.queryCountBound]
@[simp] lemma termP_eval (L : ℕ) : termP.eval L=Recovery.termExponent L := by simp [termP,Recovery.termExponent]
@[simp] lemma componentP_eval (L : ℕ) : componentP.eval L=Recovery.termExponent L+2 := by simp [componentP]
@[simp] lemma accumulatorP_eval (L : ℕ) : accumulatorP.eval L=
    1+(Recovery.termExponent L+1)*Recovery.queryCountBound L+Recovery.termExponent L+2 := by simp [accumulatorP]
end HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
