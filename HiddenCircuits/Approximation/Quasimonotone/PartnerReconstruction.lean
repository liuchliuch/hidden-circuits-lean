import HiddenCircuits.Approximation.Quasimonotone.AlternatingComponents
import HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
namespace HiddenCircuits.Approximation.QuasimonotoneProof
open CanonicalPaths.UnionReconstruction
variable {V : Type*} {G : SimpleGraph V}
abbrev matchingUnion (P Q : PerfectPartner G) := pairGraph (partnerPerm P) (partnerPerm Q)
  (partnerPerm_involutive P) (partnerPerm_involutive Q) (partnerPerm_free P) (partnerPerm_free Q)
abbrev SamePartnerUnion (P Q R S : PerfectPartner G) :=
  SameUnion (partnerPerm P) (partnerPerm Q) (partnerPerm R) (partnerPerm S)
theorem matchingUnion_eq {P Q R S : PerfectPartner G} (h : SamePartnerUnion P Q R S) :
    matchingUnion P Q=matchingUnion R S := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  change (P.val x=y ∨ Q.val x=y) ↔ (R.val x=y ∨ S.val x=y)
  have hh : y∈({P.val x,Q.val x} : Set V) ↔ y∈({R.val x,S.val x} : Set V) := by
    rw [show ({P.val x,Q.val x} : Set V)={R.val x,S.val x} from h x]
  simpa [eq_comm] using hh
theorem matchingUnion_comm (P Q : PerfectPartner G) : matchingUnion P Q=matchingUnion Q P := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  exact or_comm
theorem partner_left_eq_across_edge {P Q R S : PerfectPartner G} (h : SamePartnerUnion P Q R S)
    {x y : V} (hxy : (matchingUnion P Q).Adj x y) (hx : R.val x=P.val x) : R.val y=P.val y := by
  rcases hxy with hxy|hxy
  · change P.val x=y at hxy
    have hr : R.val x=y := hx.trans hxy
    have ha := R.property.1 x
    rw [hr] at ha
    have hb := P.property.1 x
    rw [hxy] at hb
    exact ha.trans hb.symm
  · change Q.val x=y at hxy
    have hs : S.val x=Q.val x := right_eq_of_left_eq h hx
    have hr : S.val x=y := hs.trans hxy
    have ha := S.property.1 x
    rw [hr] at ha
    have hb := Q.property.1 x
    rw [hxy] at hb
    exact left_eq_of_right_eq h (ha.trans hb.symm)
theorem partner_left_eq_of_reachable {P Q R S : PerfectPartner G} (h : SamePartnerUnion P Q R S)
    {x y : V} (hxy : (matchingUnion P Q).Reachable x y) (hx : R.val x=P.val x) : R.val y=P.val y := by
  have aux : ∀ {u v}, (matchingUnion P Q).Walk u v → R.val u=P.val u → R.val v=P.val v := by
    intro u v w
    induction w with
    | nil => exact id
    | cons huv path ih => exact fun hu => ih (partner_left_eq_across_edge h huv hu)
  exact hxy.elim (fun w => aux w hx)
end HiddenCircuits.Approximation.QuasimonotoneProof
