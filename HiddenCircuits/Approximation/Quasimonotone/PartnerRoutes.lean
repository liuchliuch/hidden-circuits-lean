import HiddenCircuits.Approximation.Quasimonotone.CutMoves
import HiddenCircuits.Approximation.CanonicalPaths.MarkedWalks
namespace HiddenCircuits.Approximation.QuasimonotoneProof
variable {V : Type} {G : SimpleGraph V}
inductive MarkedPartnerRoute (Good : PerfectPartner G → Prop) :
    PerfectPartner G → PerfectPartner G → ℕ → Prop
  | nil (P) : Good P → MarkedPartnerRoute Good P P 0
  | step {P Q R k} : Good P → PartnerMove P Q → MarkedPartnerRoute Good Q R k →
      MarkedPartnerRoute Good P R (k+1)
theorem MarkedPartnerRoute.append {Good : PerfectPartner G → Prop} {P Q R : PerfectPartner G}
    {k l : ℕ} (h : MarkedPartnerRoute Good P Q k) (h' : MarkedPartnerRoute Good Q R l) :
    MarkedPartnerRoute Good P R (k+l) := by
  induction h with
  | nil p => simpa using h'
  | step hp hm hr ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using MarkedPartnerRoute.step hp hm (ih h')
theorem MarkedPartnerRoute.vertices {Good : PerfectPartner G → Prop}
    {P Q : PerfectPartner G} {k : ℕ} (h : MarkedPartnerRoute Good P Q k) :
    ∃ v : Fin (k+1) → PerfectPartner G, v 0=P ∧ v (Fin.last k)=Q ∧
      (∀ i : Fin k,PartnerMove (v i.castSucc) (v i.succ)) ∧ ∀ i,Good (v i) := by
  induction h with
  | nil p hp =>
    refine ⟨fun _ => p,rfl,rfl,?_,?_⟩
    · exact fun i => Fin.elim0 i
    · exact fun _ => hp
  | @step p q r k hp hm hr ih =>
    obtain ⟨v,hv₀,hvlast,hvmove,hvGood⟩ := ih
    refine ⟨Fin.cons p v,rfl,?_,?_,?_⟩
    · simpa using hvlast
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [hv₀] using hm
      · simpa using hvmove j
    · exact Fin.cases hp (fun i => by simpa using hvGood i)
theorem MarkedPartnerRoute.ofLocalRoute {m : ℕ} {R : Fin m → Fin m → Prop}
    {Good : CanonicalPaths.LocalRoutes.State R → Prop} {Good' : PerfectPartner G → Prop}
    (f : CanonicalPaths.LocalRoutes.State R → PerfectPartner G)
    (hg : ∀s,Good s → Good' (f s))
    (hm : ∀s t,CanonicalPaths.LocalRoutes.Move Finset.univ s t → PartnerMove (f s) (f t))
    {s t : CanonicalPaths.LocalRoutes.State R} {k : ℕ}
    (h : CanonicalPaths.LocalRoutes.MarkedRoute Finset.univ Good s t k) :
    MarkedPartnerRoute Good' (f s) (f t) k := by
  induction h with
  | nil p hp => exact MarkedPartnerRoute.nil _ (hg p hp)
  | step hp hmove htail ih => exact MarkedPartnerRoute.step (hg _ hp) (hm _ _ hmove) ih
end HiddenCircuits.Approximation.QuasimonotoneProof
