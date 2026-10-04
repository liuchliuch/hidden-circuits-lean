import HiddenCircuits.Approximation.CanonicalPaths.LiftedRoutes
import HiddenCircuits.Approximation.CanonicalPaths.PhaseStages

/-! Component extensions preserve the actual complementary matching encoding,
with exactly the same number of exceptional columns. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
variable {m n : ℕ} {r : Fin m → Fin m → Prop} {R : Fin n → Fin n → Prop}

theorem HasCompanion.lift (columns : Fin m ↪ Fin n) (rows : Fin m → Fin n)
    (p q : State r) (P Q : State R) (f g : State r → State R)
    (hf : ∀z i,(f z).val (columns i)=rows (z.val i))
    (hg : ∀z i,(g z).val (columns i)=rows (z.val i))
    (hP : ∀i,P.val (columns i)=rows (p.val i))
    (hQ : ∀i,Q.val (columns i)=rows (q.val i))
    (hout : ∀z w i,i∉Set.range columns →
      ({(f z).val i,(g w).val i} : Finset (Fin n))={P.val i,Q.val i})
    {z : State r} {d : ℕ} (h : HasCompanion p q z d) : HasCompanion P Q (f z) d := by
  classical
  obtain ⟨w,S,hS,hw⟩ := h
  refine ⟨g w,S.map columns,(Finset.card_map _).trans_le hS,?_⟩
  intro i hi
  by_cases hin : i∈Set.range columns
  · obtain ⟨j,rfl⟩ := hin
    have hj : j∉S := by
      intro hj
      exact hi (Finset.mem_map.mpr ⟨j,hj,rfl⟩)
    rw [hf,hg,hP,hQ]
    have he := congrArg (Finset.image rows) (hw j hj)
    simpa only [Finset.image_insert,Finset.image_singleton] using he
  · exact hout z w i hin

end HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
