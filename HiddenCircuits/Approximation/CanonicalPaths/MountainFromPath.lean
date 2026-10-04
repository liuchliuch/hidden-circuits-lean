import HiddenCircuits.Approximation.CanonicalPaths.MountainSystem
import HiddenCircuits.Approximation.CanonicalPaths.MountainSide

/-! Fresh construction of all local side data from literal distinct vertex heights. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.MountainSystem
variable {m H : ℕ} (hm : 0 < m) (a : Fin (m+1) → ℕ)
  (hinj : Function.Injective a) (hzero : a 0=0) (htop : a (Fin.last m)=H)
  (hbound : ∀i,a i ≤ H)

include hinj hzero in
private theorem vertex_zero (i : Fin (m+1)) : a i=0 ↔ i.val=0 := by
  constructor
  · intro h
    exact congrArg Fin.val (hinj (h.trans hzero.symm))
  · intro h
    exact (congrArg a (show i=0 from Fin.ext h)).trans hzero

include hinj htop in
private theorem vertex_top (i : Fin (m+1)) : a i=H ↔ i.val=m := by
  constructor
  · intro h
    exact congrArg Fin.val (hinj (h.trans htop.symm))
  · intro h
    exact (congrArg a (show i=Fin.last m from Fin.ext h)).trans htop

/-- Only concrete vertex labels and their local properties are supplied. -/
def ofVertices : Side (Fin m) H where
  height e b := a (MountainSide.node (e,b))
  nondegenerate e := by
    intro h
    have he := hinj h
    have hv := congrArg Fin.val he
    simp [MountainSide.node] at hv
  upper_bound e b := hbound _
  mate := MountainSide.mate
  mate_involutive := MountainSide.mate_involutive
  mate_height p := congrArg a (MountainSide.mate_node p)
  mate_fixed p := by
    rw [MountainSide.mate_fixed_iff]
    exact or_congr (vertex_zero a hinj hzero _).symm (vertex_top a hinj htop _).symm
  bottom := MountainSide.bottomPort hm
  top := MountainSide.topPort hm
  zero_iff p := (vertex_zero a hinj hzero _).trans (MountainSide.node_zero_iff hm p)
  top_iff p := (vertex_top a hinj htop _).trans (MountainSide.node_last_iff hm p)

end HiddenCircuits.Approximation.CanonicalPaths.MountainSystem
