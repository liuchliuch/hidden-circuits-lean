import HiddenCircuits.GraphReduction.FiberBijection
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm

/-! Exact local probe extensions: an injection of the prescribed original left
vertices into the probe labels, followed by one arbitrary remaining bijection. -/
namespace HiddenCircuits.GraphReduction
variable (X Y P : Type*)

/-- A bijection across one probe pair that uses no original-original edge. -/
def ProbePairBijection := {e : X ⊕ P ≃ Y ⊕ P // ∀ x, ∃ p, e (.inl x) = .inr p}

variable {X Y P}

/-- The target vertices left after the original vertices choose distinct probe labels. -/
def ProbeRemainder (f : X ↪ P) := {v : Y ⊕ P // v ∉ Set.range (fun x => Sum.inr (f x))}

noncomputable def probeTargetEquiv (f : X ↪ P) :
    X ⊕ ProbeRemainder (Y:=Y) f ≃ Y ⊕ P := by
  classical
  let g : X → Y ⊕ P := fun x => .inr (f x)
  have hg : Function.Injective g := Sum.inr_injective.comp f.injective
  exact (Equiv.sumCongr (Equiv.ofInjective g hg) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range g))

@[simp] theorem probeTargetEquiv_inl (f : X ↪ P) (x : X) :
    probeTargetEquiv (Y:=Y) f (.inl x) = .inr (f x) := rfl
@[simp] theorem probeTargetEquiv_inr (f : X ↪ P) (v : ProbeRemainder (Y:=Y) f) :
    probeTargetEquiv f (.inr v) = v.val := rfl

namespace ProbePairBijection
noncomputable def injection (e : ProbePairBijection X Y P) : X ↪ P where
  toFun x := (e.property x).choose
  inj' := by
    intro x y h
    apply Sum.inl_injective
    apply e.val.injective
    exact (e.property x).choose_spec.trans
      ((congrArg Sum.inr h).trans (e.property y).choose_spec.symm)

 theorem injection_spec (e : ProbePairBijection X Y P) (x : X) :
    e.val (.inl x) = .inr (e.injection x) := (e.property x).choose_spec

noncomputable def remainder (e : ProbePairBijection X Y P) :
    P ≃ ProbeRemainder (Y:=Y) e.injection := by
  let f : P → ProbeRemainder (Y:=Y) e.injection := fun p => ⟨e.val (.inr p),by
    rintro ⟨x,hx⟩
    have h := e.val.injective ((e.injection_spec x).trans hx)
    cases h⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro p q h
    exact Sum.inr_injective (e.val.injective (congrArg Subtype.val h))
  · intro v
    obtain ⟨z,hz⟩ := e.val.surjective v.val
    cases z with
    | inl x =>
      exfalso
      exact v.property ⟨x,(e.injection_spec x).symm.trans hz⟩
    | inr p => exact ⟨p,Subtype.ext hz⟩

@[simp] theorem remainder_apply (e : ProbePairBijection X Y P) (p : P) :
    (e.remainder p).val = e.val (.inr p) := rfl

noncomputable def assemble (f : X ↪ P) (g : P ≃ ProbeRemainder (Y:=Y) f) :
    ProbePairBijection X Y P :=
  ⟨(Equiv.sumCongr (Equiv.refl X) g).trans (probeTargetEquiv f),
    fun x => ⟨f x,rfl⟩⟩

 theorem assemble_injective : Function.Injective
    (fun d : Σ f : X ↪ P, P ≃ ProbeRemainder (Y:=Y) f => assemble d.1 d.2) := by
  rintro ⟨f,g⟩ ⟨f',g'⟩ h
  have hf : f=f' := by
    ext x
    have hx := congrArg (fun e : ProbePairBijection X Y P => e.val (.inl x)) h
    exact Sum.inr.inj hx
  subst f'
  congr 1
  apply Equiv.ext
  intro p
  apply Subtype.ext
  exact congrArg (fun e : ProbePairBijection X Y P => e.val (.inr p)) h

 theorem assemble_injection_remainder (e : ProbePairBijection X Y P) :
    assemble e.injection e.remainder = e := by
  apply Subtype.ext
  apply Equiv.ext
  intro v
  cases v with
  | inl x => exact (e.injection_spec x).symm
  | inr p => rfl
end ProbePairBijection

noncomputable def probePairBijectionEquiv :
    ProbePairBijection X Y P ≃ Σ f : X ↪ P, P ≃ ProbeRemainder (Y:=Y) f where
  toFun e := ⟨e.injection,e.remainder⟩
  invFun d := ProbePairBijection.assemble d.1 d.2
  left_inv := ProbePairBijection.assemble_injection_remainder
  right_inv d := by
    apply ProbePairBijection.assemble_injective
    exact ProbePairBijection.assemble_injection_remainder _

end HiddenCircuits.GraphReduction
