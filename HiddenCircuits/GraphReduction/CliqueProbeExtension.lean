import HiddenCircuits.GraphReduction.ColoredPerfectPartner
import Mathlib.Data.Fintype.CardEmbedding

/-! A single clique-probe extension consists of an attachment injection and a
perfect matching on the unused probe vertices. -/
namespace HiddenCircuits.GraphReduction
variable {X P : Type*}

/-- Prescribed originals have no mutual edges; all probe vertices form a clique. -/
def cliqueExtensionGraph (X P : Type*) : SimpleGraph (X ⊕ P) where
  Adj
    | .inl _, .inl _ => False
    | .inr p, .inr q => p≠q
    | _, _ => True
  symm := by intro x y; cases x <;> cases y <;> simp [ne_comm]
  loopless := ⟨by intro x; cases x <;> simp⟩

abbrev CliqueExtension (X P : Type*) := PerfectPartner (cliqueExtensionGraph X P)
def CliqueRemainder (f : X ↪ P) := {p : P // p ∉ Set.range f}

noncomputable def injectionPartition (f : X ↪ P) : X ⊕ CliqueRemainder f ≃ P := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range f))

@[simp] theorem injectionPartition_inl (f : X ↪ P) (x : X) : injectionPartition f (.inl x)=f x := rfl
@[simp] theorem injectionPartition_inr (f : X ↪ P) (q : CliqueRemainder f) :
    injectionPartition f (.inr q)=q.val := rfl

namespace CliqueExtension
 theorem exists_probe (p : CliqueExtension X P) (x : X) : ∃ j, p.val (.inl x)=.inr j := by
  have h := p.property.2 (.inl x)
  cases he : p.val (.inl x) with
  | inl y => rw [he] at h; exact h.elim
  | inr j => exact ⟨j,rfl⟩

noncomputable def injection (p : CliqueExtension X P) : X ↪ P where
  toFun x := (p.exists_probe x).choose
  inj' := by
    intro x y h
    apply Sum.inl_injective
    apply p.property.1.injective
    exact (p.exists_probe x).choose_spec.trans
      ((congrArg Sum.inr h).trans (p.exists_probe y).choose_spec.symm)

 theorem injection_spec (p : CliqueExtension X P) (x : X) :
    p.val (.inl x)=.inr (p.injection x) := (p.exists_probe x).choose_spec

 theorem exists_remaining (p : CliqueExtension X P) (q : CliqueRemainder p.injection) :
    ∃ q' : CliqueRemainder p.injection, p.val (.inr q.val)=.inr q'.val := by
  cases he : p.val (.inr q.val) with
  | inl x =>
    have hi := p.property.1 (.inr q.val)
    rw [he,p.injection_spec] at hi
    exact (q.property ⟨x,Sum.inr.inj hi⟩).elim
  | inr j =>
    refine ⟨⟨j,?_⟩,rfl⟩
    rintro ⟨x,hx⟩
    have hi := p.property.1.injective (he.trans ((congrArg Sum.inr hx).symm.trans (p.injection_spec x).symm))
    cases hi

noncomputable def remainingPartner (p : CliqueExtension X P) (q : CliqueRemainder p.injection) :
    CliqueRemainder p.injection := (p.exists_remaining q).choose

 theorem remainingPartner_spec (p : CliqueExtension X P) (q : CliqueRemainder p.injection) :
    p.val (.inr q.val)=.inr (p.remainingPartner q).val := (p.exists_remaining q).choose_spec

noncomputable def remainder (p : CliqueExtension X P) :
    PerfectPartner (⊤ : SimpleGraph (CliqueRemainder p.injection)) := by
  refine ⟨p.remainingPartner,?_,?_⟩
  · intro q
    apply Subtype.ext
    apply Sum.inr_injective
    have hi := p.property.1 (.inr q.val)
    rw [p.remainingPartner_spec,p.remainingPartner_spec] at hi
    exact hi
  · intro q
    have h := p.property.2 (.inr q.val)
    rw [p.remainingPartner_spec] at h
    change q.val≠(p.remainingPartner q).val at h
    exact fun he => h (congrArg Subtype.val he)

/-- Explicitly pair each original with its selected probe and use the supplied
perfect matching only on the remaining probe vertices. -/
noncomputable def assemble (f : X ↪ P) (p : PerfectPartner (⊤ : SimpleGraph (CliqueRemainder f))) :
    CliqueExtension X P := by
  let Z := X ⊕ (X ⊕ CliqueRemainder f)
  let e : Z ≃ X ⊕ P := Equiv.sumCongr (Equiv.refl X) (injectionPartition f)
  let q : Z → Z
    | .inl x => .inr (.inl x)
    | .inr (.inl x) => .inl x
    | .inr (.inr v) => .inr (.inr (p.val v))
  have hq : Function.Involutive q := by
    rintro (x | (x | v))
    · rfl
    · rfl
    · change Sum.inr (Sum.inr (p.val (p.val v)))=Sum.inr (Sum.inr v)
      rw [p.property.1 v]
  refine ⟨fun v => e (q (e.symm v)),?_,?_⟩
  · intro v
    simp only [e.symm_apply_apply]
    rw [hq (e.symm v),e.apply_symm_apply]
  · intro v
    obtain ⟨v,rfl⟩ := e.surjective v
    change (cliqueExtensionGraph X P).Adj (e v) (e (q (e.symm (e v))))
    rw [e.symm_apply_apply]
    rcases v with x|(x|v)
    · trivial
    · trivial
    · change v.val≠(p.val v).val
      intro h
      exact (p.property.2 v) (Subtype.ext h)

@[simp] theorem assemble_original (f : X ↪ P)
    (p : PerfectPartner (⊤ : SimpleGraph (CliqueRemainder f))) (x : X) :
    (assemble f p).val (.inl x)=.inr (f x) := rfl

@[simp] theorem assemble_attached (f : X ↪ P)
    (p : PerfectPartner (⊤ : SimpleGraph (CliqueRemainder f))) (x : X) :
    (assemble f p).val (.inr (f x))=.inl x := by
  have h := (assemble f p).property.1 (.inl x)
  rw [assemble_original] at h
  exact h

@[simp] theorem assemble_remaining (f : X ↪ P)
    (p : PerfectPartner (⊤ : SimpleGraph (CliqueRemainder f))) (v : CliqueRemainder f) :
    (assemble f p).val (.inr v.val)=.inr (p.val v).val := by
  have hv : (injectionPartition f).symm v.val = .inr v :=
    (injectionPartition f).symm_apply_apply (.inr v)
  simp [assemble,hv]

 theorem assemble_injection_remainder (p : CliqueExtension X P) :
    assemble p.injection p.remainder=p := by
  classical
  apply Subtype.ext
  funext v
  cases v with
  | inl x => exact (p.injection_spec x).symm
  | inr v =>
    by_cases hv : v∈Set.range p.injection
    · obtain ⟨x,rfl⟩ := hv
      rw [assemble_attached]
      have hi := p.property.1 (.inl x)
      rw [p.injection_spec] at hi
      exact hi.symm
    · change (assemble p.injection p.remainder).val (.inr (⟨v,hv⟩ : CliqueRemainder p.injection).val) = _
      rw [assemble_remaining]
      exact (p.remainingPartner_spec ⟨v,hv⟩).symm

 theorem assemble_injective : Function.Injective
    (fun d : Σ f : X ↪ P, PerfectPartner (⊤ : SimpleGraph (CliqueRemainder f)) => assemble d.1 d.2) := by
  rintro ⟨f,p⟩ ⟨g,q⟩ he
  have hf : f=g := by
    ext x
    have hx := congrArg (fun p : CliqueExtension X P => p.val (.inl x)) he
    exact Sum.inr.inj hx
  subst g
  congr 1
  apply Subtype.ext
  funext v
  apply Subtype.ext
  apply Sum.inr_injective
  have hx := congrArg (fun p : CliqueExtension X P => p.val (.inr v.val)) he
  simpa only [assemble_remaining] using hx

end CliqueExtension
/-- A local extension is exactly an attachment injection plus an actual clique matching
on the remaining probe labels. -/
noncomputable def cliqueExtensionEquiv : CliqueExtension X P ≃
    Σ f : X ↪ P, PerfectPartner (⊤ : SimpleGraph (CliqueRemainder f)) where
  toFun p := ⟨p.injection,p.remainder⟩
  invFun d := CliqueExtension.assemble d.1 d.2
  left_inv := CliqueExtension.assemble_injection_remainder
  right_inv d := by
    apply CliqueExtension.assemble_injective
    exact CliqueExtension.assemble_injection_remainder _

end HiddenCircuits.GraphReduction
