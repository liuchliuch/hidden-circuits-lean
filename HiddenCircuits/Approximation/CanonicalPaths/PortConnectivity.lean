import HiddenCircuits.Approximation.CanonicalPaths.FiniteRoute
import HiddenCircuits.PerfectPartners
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Logic.Equiv.Option

/-! Parity proof for two local port pairings. The local graph
edges are actual hypotheses; global boundary connectivity is proved from them. -/
namespace HiddenCircuits.Approximation.CanonicalPaths
variable {α : Type*} [Fintype α]

/-- Two involutions, one fixed-point-free and the other with two boundary fixed
points, force those boundaries into the same component of their local-move graph. -/
theorem boundary_ports_reachable (H : SimpleGraph α) (f g : α → α) (start finish : α)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (hfree : ∀x,f x≠x) (hfixed : ∀x,g x=x ↔ x=start ∨ x=finish)
    (hF : ∀x,H.Adj x (f x)) (hG : ∀x,g x=x ∨ H.Adj x (g x)) :
    H.Reachable start finish := by
  classical
  by_contra hfinish
  let C := {x : α // H.Reachable start x}
  let a : C := ⟨start,SimpleGraph.Reachable.refl _⟩
  let fC : C → C := fun x => ⟨f x.val,x.property.trans ((hF x.val).reachable)⟩
  let gC : C → C := fun x => ⟨g x.val,by
    rcases hG x.val with h|h
    · simpa only [h] using x.property
    · exact x.property.trans h.reachable⟩
  have hfC : Function.Involutive fC := fun x => Subtype.ext (hf x.val)
  have hgC : Function.Involutive gC := fun x => Subtype.ext (hg x.val)
  have hgA : gC a=a := Subtype.ext ((hfixed start).mpr (Or.inl rfl))
  have hgFixed (x : C) (hx : gC x=x) : x=a := by
    have he : g x.val=x.val := congrArg Subtype.val hx
    rcases (hfixed x.val).mp he with h|h
    · exact Subtype.ext h
    · exact False.elim (hfinish (h ▸ x.property))
  let F : PerfectPartner (⊤ : SimpleGraph C) := ⟨fC,hfC,by
    intro x
    change x≠fC x
    intro h
    exact hfree x.val (congrArg Subtype.val h).symm⟩
  have hEvenC : Even (Fintype.card C) := F.toMatching.property.even_card
  let D := {x : C // x≠a}
  let gD : D → D := fun x => ⟨gC x.val,by
    intro h
    have hh := congrArg gC h
    rw [hgC x.val,hgA] at hh
    exact x.property hh⟩
  have hgD : Function.Involutive gD := fun x => Subtype.ext (hgC x.val)
  let K : PerfectPartner (⊤ : SimpleGraph D) := ⟨gD,hgD,by
    intro x
    change x≠gD x
    intro h
    exact x.property (hgFixed x.val (congrArg Subtype.val h).symm)⟩
  have hEvenD : Even (Fintype.card D) := K.toMatching.property.even_card
  have hcard : Fintype.card C=Fintype.card D+1 := by
    have hh := Fintype.card_congr (Equiv.optionSubtypeNe a)
    simpa only [Fintype.card_option] using hh.symm
  obtain ⟨c,hc⟩ := hEvenC
  obtain ⟨d,hd⟩ := hEvenD
  omega

/-- Removing repeated vertices gives a polynomially bounded actual local walk. -/
theorem boundary_ports_bounded_walk (H : SimpleGraph α) (f g : α → α) (start finish : α)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (hfree : ∀x,f x≠x) (hfixed : ∀x,g x=x ↔ x=start ∨ x=finish)
    (hF : ∀x,H.Adj x (f x)) (hG : ∀x,g x=x ∨ H.Adj x (g x)) :
    ∃ w : H.Walk start finish,w.length < Fintype.card α := by
  classical
  obtain ⟨w⟩ := boundary_ports_reachable H f g start finish hf hg hfree hfixed hF hG
  exact ⟨w.toPath.val,w.toPath.property.length_lt⟩

end HiddenCircuits.Approximation.CanonicalPaths
