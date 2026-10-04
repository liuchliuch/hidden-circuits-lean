import HiddenCircuits.Approximation.FiniteCoins
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Finite traversal between two boundary ports

A finite partial permutation with exactly one missing image and exactly one
missing preimage is a disjoint union of directed cycles and one simple open
path. The open path is constructed from its closed permutation orbit. Its
length is bounded by the number of states, without assuming connectivity.
This is the finite traversal lemma used for discrete mountain-climber ports.
-/
namespace HiddenCircuits.Approximation.CanonicalPaths

variable {α : Type*} [Fintype α]

/-- Closing the one boundary gap turns an injective partial successor into a
permutation. No search or running-time assertion is concealed in this map. -/
def closeRoute (next : α → Option α) (start : α) (a : α) : α :=
  (next a).getD start

theorem closeRoute_eq_start_iff (next : α → Option α) (start finish : α)
    (terminal : ∀ a, next a=none ↔ a=finish)
    (noPredecessor : ∀ a, next a≠some start) (a : α) :
    closeRoute next start a=start ↔ a=finish := by
  cases h : next a with
  | none =>
    have he := (terminal a).mp h
    simp only [closeRoute,h,Option.getD_none,true_iff]
    exact he
  | some b =>
    have hb : b≠start := by intro he; exact noPredecessor a (h.trans (congrArg some he))
    have ha : a≠finish := by intro he; have hh := (terminal a).mpr he; rw [h] at hh; contradiction
    simp [closeRoute,h,hb,ha]

theorem closeRoute_injective (next : α → Option α) (start finish : α)
    (terminal : ∀ a, next a=none ↔ a=finish)
    (noPredecessor : ∀ a, next a≠some start)
    (uniquePredecessor : ∀ a b c, next a=some c → next b=some c → a=b) :
    Function.Injective (closeRoute next start) := by
  intro a b hab
  cases ha : next a with
  | none =>
    have he : a=finish := (terminal a).mp ha
    have hb : closeRoute next start b=start := by simpa [closeRoute,ha] using hab.symm
    exact he.trans ((closeRoute_eq_start_iff next start finish terminal noPredecessor b).mp hb).symm
  | some x =>
    cases hb : next b with
    | none =>
      have he : b=finish := (terminal b).mp hb
      have hh : closeRoute next start a=start := by simpa [closeRoute,hb] using hab
      exact ((closeRoute_eq_start_iff next start finish terminal noPredecessor a).mp hh).trans he.symm
    | some y =>
      have hxy : x=y := by simpa [closeRoute,ha,hb] using hab
      exact uniquePredecessor a b y (ha.trans (congrArg some hxy)) hb

/-- The open route visits no state twice and has fewer edges than there are
states. The sequence records every concrete local successor transition. -/
theorem finite_open_route (next : α → Option α) (start finish : α)
    (terminal : ∀ a, next a=none ↔ a=finish)
    (noPredecessor : ∀ a, next a≠some start)
    (uniquePredecessor : ∀ a b c, next a=some c → next b=some c → a=b) :
    ∃ k < Fintype.card α, ∃ path : Fin (k+1) → α,
      path 0=start ∧ path (Fin.last k)=finish ∧ Function.Injective path ∧
      ∀ i : Fin k, next (path i.castSucc)=some (path i.succ) := by
  classical
  let g := closeRoute next start
  have hg : Function.Injective g :=
    closeRoute_injective next start finish terminal noPredecessor uniquePredecessor
  let p := Function.minimalPeriod g start
  have hp : 0<p := Function.minimalPeriod_pos_of_mem_periodicPts (hg.mem_periodicPts start)
  have hpc : p≤Fintype.card α := Function.minimalPeriod_le_card
  have hperiod : g^[p] start=start := Function.isPeriodicPt_minimalPeriod g start
  let path : Fin (p-1+1) → α := fun i => g^[i.val] start
  have hpinj : Function.Injective path := by
    intro i j hij
    apply Fin.ext
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (by have hi := i.isLt; change i.val<p; omega)
      (by have hj := j.isLt; change j.val<p; omega)).mp hij
  have hend : path (Fin.last (p-1))=finish := by
    apply (closeRoute_eq_start_iff next start finish terminal noPredecessor _).mp
    change g (g^[p-1] start)=start
    rw [← Function.iterate_succ_apply' g (p-1) start]
    have he : (p-1).succ=p := by omega
    simpa only [he] using hperiod
  refine ⟨p-1,by omega,path,?_,hend,hpinj,?_⟩
  · rfl
  · intro i
    have hnot : path i.castSucc≠finish := by
      intro hi
      have he := hpinj (hi.trans hend.symm)
      have hv := congrArg Fin.val he
      have hh := i.isLt
      simp only [Fin.val_castSucc,Fin.val_last] at hv
      omega
    cases hn : next (path i.castSucc) with
    | none => exact False.elim (hnot ((terminal _).mp hn))
    | some b =>
      have hgstep : g (path i.castSucc)=b := by simp [g,closeRoute,hn]
      congr 1
      change b=g^[i.val+1] start
      rw [Function.iterate_succ_apply' g i.val start]
      exact hgstep.symm

end HiddenCircuits.Approximation.CanonicalPaths
