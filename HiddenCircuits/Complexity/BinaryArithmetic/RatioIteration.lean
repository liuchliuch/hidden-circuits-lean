import HiddenCircuits.Complexity.BinaryArithmetic.RationalAccumulator
import HiddenCircuits.DH.Runtime.UnaryFor

/-! Fresh reconstruction of the exact indexed-loop/list-fold correspondence. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverAlgebra
open HiddenCircuits.DH.Runtime.UnaryFor

lemma iterate_lookup_aux {α β : Type*} (f : α → β → α) (g : ℕ → β)
    (xs : List β) (i : ℕ) (a : α) (hg : ∀ j (hj : j<xs.length),g (i+j)=xs[j]) :
    iterate (fun j a => f a (g j)) i xs.length a=xs.foldl f a := by
  induction xs generalizing i a with
  | nil => rfl
  | cons x xs ih =>
    have h0 := hg 0 (by simp)
    simp only [Nat.add_zero,List.getElem_cons_zero] at h0
    simp only [List.length_cons,iterate,List.foldl_cons,h0]
    apply ih
    intro j hj
    have h := hg (j+1) (by simp only [List.length_cons];omega)
    simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

lemma iterate_lookup {α β : Type*} (f : α → β → α) (xs : List β) (default : β) (a : α) :
    iterate (fun j a => f a (xs[j]?.getD default)) 0 xs.length a=xs.foldl f a := by
  apply iterate_lookup_aux
  intro j hj
  simp only [Nat.zero_add,List.getElem?_eq_getElem hj,Option.getD_some]
end HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverAlgebra
