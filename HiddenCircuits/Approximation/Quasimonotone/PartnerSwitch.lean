import HiddenCircuits.Approximation.Quasimonotone.CutMoves
import HiddenCircuits.Approximation.FiniteChains.SwitchKernel
namespace HiddenCircuits.Approximation.QuasimonotoneProof.PartnerSwitch
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
def conjugate (a b : Fin n) (p : Fin n → Fin n) (x : Fin n) : Fin n :=
  Equiv.swap a b (p (Equiv.swap a b x))
theorem conjugate_involutive (a b : Fin n) : Function.Involutive (conjugate a b) := by
  intro p
  funext x
  simp [conjugate]
theorem conjugate_partner_involutive (a b : Fin n) (p : Fin n → Fin n) (hp : Function.Involutive p) :
    Function.Involutive (conjugate a b p) := by
  intro x
  simp only [conjugate,Equiv.swap_apply_self,hp (Equiv.swap a b x)]
def switch (a b : Fin n) (P : PerfectPartner G) : PerfectPartner G :=
  if h : ∀x,G.Adj x (conjugate a b P.val x) then
    ⟨conjugate a b P.val,conjugate_partner_involutive a b P.val P.property.1,h⟩
  else P
theorem switch_involutive (a b : Fin n) : Function.Involutive (switch G a b) := by
  intro P
  by_cases h : ∀x,G.Adj x (conjugate a b P.val x)
  · have hb : ∀x,G.Adj x (conjugate a b (conjugate a b P.val) x) := by
      rw [conjugate_involutive]
      exact P.property.2
    apply Subtype.ext
    simp only [switch,dif_pos h,dif_pos hb]
    exact conjugate_involutive a b P.val
  · simp [switch,h]
theorem switch_eq_of_conjugate (P Q : PerfectPartner G) (a b : Fin n)
    (h : Q.val=fun x => Equiv.swap a b (P.val (Equiv.swap a b x))) : switch G a b P=Q := by
  have hv : ∀x,G.Adj x (conjugate a b P.val x) := by
    rw [show conjugate a b P.val=Q.val from h.symm]
    exact Q.property.2
  apply Subtype.ext
  simp only [switch,dif_pos hv]
  exact h.symm
theorem move_switch {P Q : PerfectPartner G} (h : PartnerMove P Q) :
    ∃ a b,switch G a b P=Q := by
  obtain ⟨a,b,h⟩ := h
  refine ⟨a,b,switch_eq_of_conjugate G P Q a b ?_⟩
  funext x
  have hh := congrFun h x
  simp only [Equiv.swap_apply_def] at hh ⊢
  split_ifs at hh ⊢ <;> exact hh
end HiddenCircuits.Approximation.QuasimonotoneProof.PartnerSwitch
