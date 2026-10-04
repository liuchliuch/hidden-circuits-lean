import HiddenCircuits.DH.CographInvariant
import HiddenCircuits.DH.CographProgram

/-! Success and exact graph reconstruction of the actual fuelled cotree program.
The array specification is discharged by the ordinary two-sweep frontend. -/
namespace HiddenCircuits.DH.CographProgram
open SimpleGraph LexBFSModel CographStaircase LabeledCographTree
variable {n : ℕ}

/-- Extensional semantics of the computed head arrays. These propositions are
proof-side properties, never inputs inspected by the executable interpreter. -/
structure DataCorrect (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tie : List (Fin n)) (data : HeadData n) : Prop where
  normal_nodup : ∀r : Fin n, (data.normal[r.val]).Nodup
  complement_nodup : ∀r : Fin n, (data.complement[r.val]).Nodup
  normal_heads : ∀M r,
    PairedModule G (sweep (fun a b => decide (G.Adj a b)) true tie)
      (sweep (fun a b => decide (G.Adj a b)) false
        ((sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex)) M r →
      ∀x, x∈data.normal[r.val] ↔ FirstProfileHead G M r
        (sweep (fun a b => decide (G.Adj a b)) true tie) x
  complement_heads : ∀M r,
    PairedModule G (sweep (fun a b => decide (G.Adj a b)) true tie)
      (sweep (fun a b => decide (G.Adj a b)) false
        ((sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex)) M r →
      ∀x, x∈data.complement[r.val] ↔ FirstProfileHead Gᶜ M r
        (sweep (fun a b => decide (G.Adj a b)) false
          ((sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex)) x
  normal_order : ∀M r,
    PairedModule G (sweep (fun a b => decide (G.Adj a b)) true tie)
      (sweep (fun a b => decide (G.Adj a b)) false
        ((sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex)) M r →
      (data.normal[r.val]).Pairwise (fun x y => pivotProfile G r y ⊂ pivotProfile G r x)
  complement_order : ∀M r,
    PairedModule G (sweep (fun a b => decide (G.Adj a b)) true tie)
      (sweep (fun a b => decide (G.Adj a b)) false
        ((sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex)) M r →
      (data.complement[r.val]).Pairwise (fun x y => pivotProfile Gᶜ r y ⊂ pivotProfile Gᶜ r x)
  choice : ∀r : Fin n, HeadChoice G.Adj data.choice[r.val] data.normal[r.val] data.complement[r.val]

/-- Fuel only bounds totalization. On semantic P4-free modules, each actual child
is a smaller graph module, so the ordinary program succeeds before fuel runs out. -/
theorem run_correct (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : P4Free G)
    (tie : List (Fin n)) (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (data : HeadData n) (hd : DataCorrect G tie data) (fuel : ℕ)
    (M : Set (Fin n)) (r : Fin n)
    (hInv : PairedModule G (sweep (fun a b => decide (G.Adj a b)) true tie)
      (sweep (fun a b => decide (G.Adj a b)) false
        ((sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex)) M r)
    (hf : M.ncard≤fuel) :
    ∃t, (run fuel data r).tree=some t ∧ Correct G t ∧ t.leaves.Nodup ∧ ∀v, v∈t.leaves ↔ v∈M := by
  classical
  induction fuel generalizing M r with
  | zero =>
    have hp : 0<M.ncard := (Set.ncard_pos (Set.toFinite M)).mpr ⟨r,hInv.root_mem⟩
    omega
  | succ fuel ih =>
    let as := data.normal[r.val]
    let bs := data.complement[r.val]
    let s := data.choice[r.val]
    let hs := weave s as bs
    have child_exists : ∀h∈hs, ∃t, (run fuel data (branchHead h)).tree=some t ∧
        Correct G t ∧ t.leaves.Nodup ∧ ∀v, v∈t.leaves ↔ v∈branchCell G M r h := by
      intro h hm
      cases h with
      | inl x =>
        have hx : x∈as := by simpa using
          (mem_weave s as bs (Sum.inl x)).mp hm
        have hfirst := (hd.normal_heads M r hInv x).mp hx
        have hi := hInv.normal_child hG tie htie hall hfirst
        have hlt := relativePivotCell_card_lt (G := G) (x := x) hInv.root_mem
        exact ih (relativePivotCell G M r x) x hi (by omega)
      | inr x =>
        have hx : x∈bs := by simpa using
          (mem_weave s as bs (Sum.inr x)).mp hm
        have hfirst := (hd.complement_heads M r hInv x).mp hx
        have hi := hInv.complement_child hG tie htie hall hfirst
        have hlt := relativePivotCell_card_lt (G := Gᶜ) (x := x) hInv.root_mem
        exact ih (relativePivotCell Gᶜ M r x) x hi (by omega)
    let child : (Fin n ⊕ Fin n) → LabeledCographTree (Fin n) := fun h =>
      if hh : h∈hs then Classical.choose (child_exists h hh) else .leaf (branchHead h)
    have child_spec (h : Fin n ⊕ Fin n) (hh : h∈hs) :
        (run fuel data (branchHead h)).tree=some (child h) ∧ Correct G (child h) ∧
        (child h).leaves.Nodup ∧ ∀v, v∈(child h).leaves ↔ v∈branchCell G M r h := by
      simpa only [child,dif_pos hh] using Classical.choose_spec (child_exists h hh)
    have hcoverN : ∀v∈M, v∈(sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex :=
      fun v _ => (sweep_perm _ true tie).mem_iff.mpr (hall v)
    have hcoverC : ∀v∈M, v∈(sweep (fun a b => decide (G.Adj a b)) false
        ((sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex)).map Event.vertex := by
      intro v hv
      exact (sweep_perm _ false _).mem_iff.mpr (hcoverN v hv)
    have ha : ProfileFamily G M r as := profileFamily_of_first_iff M r _ as (hd.normal_nodup r)
      hcoverN (hd.normal_heads M r hInv)
    have hb : ProfileFamily Gᶜ M r bs := profileFamily_of_first_iff M r _ bs (hd.complement_nodup r)
      hcoverC (hd.complement_heads M r hInv)
    have hheads : ∀h∈hs, branchHead h∈branchCell G M r h := by
      intro h hm
      rcases (mem_weave s as bs h).mp hm with ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩
      · exact ⟨(ha.members x hx).1,mem_pivotCell_self (ha.members x hx).2⟩
      · exact ⟨(hb.members x hx).1,mem_pivotCell_self (hb.members x hx).2⟩
    have hdisjoint := branchCells_weave_disjoint G M r s as bs
      (hd.normal_order M r hInv) (hd.complement_order M r hInv)
    have hcross := ProfileFamily.weave_cross hInv.module ha hb
      (hd.normal_order M r hInv) (hd.complement_order M r hInv) s (hd.choice r)
    let t := assembleCograph r s as bs child
    refine ⟨t,run_step fuel data r child (fun h hh => (child_spec h hh).1),?_,?_,?_⟩
    · exact hG.assembleCograph_correct hInv.module r s as bs child hheads
        (fun h hh => (child_spec h hh).2.1) (fun h hh => (child_spec h hh).2.2.2) hdisjoint hcross
    · exact assembleCograph_nodup r s as bs child (fun h hh => (child_spec h hh).2.2.1)
        (fun h hh => (child_spec h hh).2.2.2) hdisjoint
    · apply assembleCograph_covers hInv.root_mem s as bs child (fun h hh => (child_spec h hh).2.2.2)
      · exact ha.covers
      · intro v hv hrv
        apply hb.covers v hv
        rw [nonneighbors_compl]
        exact hrv

lemma leaves_length_eq_ncard {t : LabeledCographTree (Fin n)}
    (hn : t.leaves.Nodup) (M : Set (Fin n)) (hc : ∀v, v∈t.leaves ↔ v∈M) :
    t.leaves.length=M.ncard := by
  classical
  have he : (t.leaves.toFinset : Set (Fin n))=M := by ext v; simpa using hc v
  rw [←List.toFinset_card_of_nodup hn,←Set.ncard_coe_finset,he]

/-- The final successful program has the claimed linear graph-traversal cost and
literal cotree allocation count in the original module vertices. -/
theorem run_correct_resources (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : P4Free G)
    (tie : List (Fin n)) (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (data : HeadData n) (hd : DataCorrect G tie data) (fuel : ℕ) (M : Set (Fin n)) (r : Fin n)
    (hInv : PairedModule G (sweep (fun a b => decide (G.Adj a b)) true tie)
      (sweep (fun a b => decide (G.Adj a b)) false
        ((sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex)) M r)
    (hf : M.ncard≤fuel) :
    ∃t, (run fuel data r).tree=some t ∧ Correct G t ∧ t.leaves.Nodup ∧
      (∀v, v∈t.leaves ↔ v∈M) ∧ (run fuel data r).accesses≤18*M.ncard ∧
      (run fuel data r).allocations+1=2*M.ncard := by
  obtain ⟨t,ht,hc,hn,hcover⟩ := run_correct G hG tie htie hall data hd fuel M r hInv hf
  have hlen := leaves_length_eq_ncard hn M hcover
  have hres := run_resources fuel data r t ht
  refine ⟨t,ht,hc,hn,hcover,?_,?_⟩ <;> omega

end HiddenCircuits.DH.CographProgram
