import HiddenCircuits.Approximation.Quasimonotone.CutMoves
namespace HiddenCircuits.Approximation.QuasimonotoneProof
attribute [local instance] Classical.propDecidable
variable {V : Type} {G : SimpleGraph V}
def Preserves (S : Set V) (M : PerfectPartner G) : Prop := ∀ x, x∈S ↔ M.val x∈S
noncomputable def spliceFun (S : Set V) (M B : PerfectPartner G) (x : V) : V :=
  if x∈S then M.val x else B.val x
noncomputable def splice (S : Set V) (M B : PerfectPartner G)
    (hM : Preserves S M) (hB : Preserves S B) : PerfectPartner G := by
  refine ⟨spliceFun S M B,?_,?_⟩
  · intro x
    by_cases hx : x∈S
    · simp [spliceFun,hx,(hM x).mp hx,M.property.1 x]
    · have hb : B.val x∉S := fun h => hx ((hB x).mpr h)
      simp [spliceFun,hx,hb,B.property.1 x]
  · intro x
    by_cases hx : x∈S
    · simpa [spliceFun,hx] using M.property.2 x
    · simpa [spliceFun,hx] using B.property.2 x
@[simp] theorem splice_inside (S : Set V) (M B : PerfectPartner G)
    (hM : Preserves S M) (hB : Preserves S B) {x : V} (hx : x∈S) :
    (splice S M B hM hB).val x=M.val x := by simp [splice,spliceFun,hx]
@[simp] theorem splice_outside (S : Set V) (M B : PerfectPartner G)
    (hM : Preserves S M) (hB : Preserves S B) {x : V} (hx : x∉S) :
    (splice S M B hM hB).val x=B.val x := by simp [splice,spliceFun,hx]
theorem splice_preserves (S : Set V) (M B : PerfectPartner G)
    (hM : Preserves S M) (hB : Preserves S B) : Preserves S (splice S M B hM hB) := by
  intro x
  by_cases hx : x∈S
  · simp only [splice_inside S M B hM hB hx]; exact hM x
  · simp only [splice_outside S M B hM hB hx]; exact hB x
theorem splice_self (S : Set V) (M : PerfectPartner G) (hM : Preserves S M) :
    splice S M M hM hM=M := by
  apply Subtype.ext
  funext x
  by_cases hx : x∈S <;> simp [splice,spliceFun,hx]
theorem splice_eq_of_agree_inside (S : Set V) (M B : PerfectPartner G)
    (hM : Preserves S M) (hB : Preserves S B) (h : ∀x∈S,M.val x=B.val x) :
    splice S M B hM hB=B := by
  apply Subtype.ext
  funext x
  by_cases hx : x∈S
  · rw [splice_inside S M B hM hB hx,h x hx]
  · exact splice_outside S M B hM hB hx
theorem swap_region [DecidableEq V] (S : Set V) {a b : V} (ha : a∈S) (hb : b∈S) (x : V) :
    Equiv.swap a b x∈S ↔ x∈S := by
  by_cases hxa : x=a
  · subst x; simp [ha,hb]
  by_cases hxb : x=b
  · subst x; simp [ha,hb]
  · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
theorem splice_conjugate (S : Set V) (M N B : PerfectPartner G)
    (hM : Preserves S M) (hN : Preserves S N) (hB : Preserves S B)
    (a b : V) (ha : a∈S) (hb : b∈S)
    (h : N.val=fun x => Equiv.swap a b (M.val (Equiv.swap a b x))) :
    (splice S N B hN hB).val=fun x => Equiv.swap a b
      ((splice S M B hM hB).val (Equiv.swap a b x)) := by
  classical
  funext x
  by_cases hx : x∈S
  · rw [splice_inside S N B hN hB hx,
      splice_inside S M B hM hB ((swap_region S ha hb x).mpr hx)]
    exact congrFun h x
  · have hx' : Equiv.swap a b x=x := Equiv.swap_apply_of_ne_of_ne
        (fun hh => hx (hh.symm ▸ ha)) (fun hh => hx (hh.symm ▸ hb))
    have hb' : B.val x∉S := fun hh => hx ((hB x).mpr hh)
    have he : Equiv.swap a b (B.val x)=B.val x := Equiv.swap_apply_of_ne_of_ne
      (fun hh => hb' (hh.symm ▸ ha)) (fun hh => hb' (hh.symm ▸ hb))
    rw [hx',splice_outside S N B hN hB hx,splice_outside S M B hM hB hx,he]
end HiddenCircuits.Approximation.QuasimonotoneProof
