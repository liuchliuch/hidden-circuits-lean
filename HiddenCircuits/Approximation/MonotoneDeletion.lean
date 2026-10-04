import HiddenCircuits.Approximation.OrderedIntervals

/-! Injective restrictions sorted by their original row and column indices.
Boundaries count retained columns, and the resulting graph is the induced subgraph. -/
namespace HiddenCircuits.Approximation
open GraphReduction
attribute [local instance] Classical.propDecidable
namespace MonotoneRestriction
variable {X Y X' Y' : Type*} [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
  {R : X → Y → Prop} (O : MonotoneOrdering R)

private theorem rank_injective {A B : Type*} {N : ℕ} (e : Fin N ≃ B)
    (f : A → B) (hf : Function.Injective f) : Function.Injective (fun x => (e.symm (f x)).val) :=
  Fin.val_injective.comp (e.symm.injective.comp hf)

noncomputable def rows (f : X' → X) (hf : Function.Injective f) : Fin (Fintype.card X') ≃ X' :=
  sortByRank (fun x => (O.rows.symm (f x)).val) (rank_injective O.rows f hf)
noncomputable def columns (g : Y' → Y) (hg : Function.Injective g) : Fin (Fintype.card Y') ≃ Y' :=
  sortByRank (fun y => (O.columns.symm (g y)).val) (rank_injective O.columns g hg)
noncomputable def rowIndex (f : X' → X) (hf : Function.Injective f) (i : Fin (Fintype.card X')) : Fin (Fintype.card X) :=
  O.rows.symm (f (rows O f hf i))
noncomputable def columnIndex (g : Y' → Y) (hg : Function.Injective g) (j : Fin (Fintype.card Y')) : Fin (Fintype.card Y) :=
  O.columns.symm (g (columns O g hg j))

theorem rowIndex_strict (f : X' → X) (hf : Function.Injective f) : StrictMono (rowIndex O f hf) :=
  sortByRank_strictMono (fun x => (O.rows.symm (f x)).val) (rank_injective O.rows f hf)
theorem columnIndex_strict (g : Y' → Y) (hg : Function.Injective g) : StrictMono (columnIndex O g hg) :=
  sortByRank_strictMono (fun y => (O.columns.symm (g y)).val) (rank_injective O.columns g hg)

noncomputable def ordering (f : X' → X) (g : Y' → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) : MonotoneOrdering (fun x y => R (f x) (g y)) where
  rows := rows O f hf
  columns := columns O g hg
  lo i := endpointCount (fun y => (O.columns.symm (g y)).val) (O.lo (rowIndex O f hf i))
  hi i := endpointCount (fun y => (O.columns.symm (g y)).val) (O.hi (rowIndex O f hf i))
  lo_mono := (endpointCount_mono _).comp (O.lo_mono.comp (rowIndex_strict O f hf).monotone)
  hi_mono := (endpointCount_mono _).comp (O.hi_mono.comp (rowIndex_strict O f hf).monotone)
  lo_le_hi i := endpointCount_mono _ (O.lo_le_hi (rowIndex O f hf i))
  hi_le i := endpointCount_upper _ _
  neighborhood i j := by
    have h := O.neighborhood (rowIndex O f hf i) (columnIndex O g hg j)
    simp only [rowIndex,columnIndex,Equiv.apply_symm_apply] at h
    have hlo := endpointCount_index (fun j => (columnIndex O g hg j).val)
      (columnIndex_strict O g hg) j (O.lo (rowIndex O f hf i))
    have hhi := endpointCount_index (fun j => (columnIndex O g hg j).val)
      (columnIndex_strict O g hg) j (O.hi (rowIndex O f hf i))
    unfold columnIndex at hlo hhi
    rw [endpointCount_comp (columns O g hg) (fun y => (O.columns.symm (g y)).val)
      (O.lo (rowIndex O f hf i))] at hlo
    rw [endpointCount_comp (columns O g hg) (fun y => (O.columns.symm (g y)).val)
      (O.hi (rowIndex O f hf i))] at hhi
    unfold rowIndex at hlo hhi ⊢
    rw [h]
    omega
end MonotoneRestriction

theorem Quasimonotone.induce {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : Quasimonotone G) (S : Set V) : Quasimonotone (G.induce S) := by
  classical
  letI : Fintype S := @Subtype.fintype V (fun v => v ∈ S) _ _
  intro T
  let A : Set V := Subtype.val '' T
  letI : Fintype A := @Subtype.fintype V (fun v => v ∈ A) _ _
  let f : T → A := fun x => ⟨x.val.val,⟨x.val,x.property,rfl⟩⟩
  let g : {x : S // x ∉ T} → {x : V // x ∉ A} := fun x => ⟨x.val.val,by
    rintro ⟨y,hy,he⟩
    have hh : y=x.val := Subtype.ext he
    exact x.property (hh ▸ hy)⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : A => z.val) h))
  have hg : Function.Injective g := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : {x : V // x ∉ A} => z.val) h))
  obtain ⟨o⟩ := hG A
  exact ⟨MonotoneRestriction.ordering o f g hf hg⟩
end HiddenCircuits.Approximation
