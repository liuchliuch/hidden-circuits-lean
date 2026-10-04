import HiddenCircuits.DH.LexBFSBlockView

/-! Local preservation of sparse-row provenance after one exact pointer transfer. -/
namespace HiddenCircuits.DH.LexBFSPartition
open LexBFSLinks
open LexBFSLabeled (Block)

lemma middle_disjoint {α : Type*} (a b c : List α) (hn : (a++b++c).Nodup) :
    List.Disjoint b (a++c) := by
  obtain ⟨hab,hc,habc⟩ := List.nodup_append.mp hn
  obtain ⟨ha,hb,hab⟩ := List.nodup_append.mp hab
  apply List.disjoint_left.mpr
  intro x hx hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hab x hy x hx rfl
  · exact habc x (List.mem_append_right _ hx) x hy rfl

lemma allBlockIds_append {n b : ℕ} (xs ys : List (Block n b)) :
    allBlockIds (xs++ys) = allBlockIds xs++allBlockIds ys := by simp [allBlockIds]

/-- A generic preservation lemma packages the already proved pointer contracts.
Only the affected lists and the actual stamp/companion array writes enter the hypotheses. -/
theorem BlockView.advance {n b : ℕ} {s t : Heap n b} {epoch : ℕ} {first : Bool}
    {pre post : List (Block n b)} {c : Block n b} {f : CellContents n b}
    (h : BlockView s epoch first (pre++c::post) f) (v : Fin n) (d : Fin b)
    (hd : c.companion = none ∨ c.companion = some d)
    (hcd : c.original ≠ d)
    (hv : VertexView t (Function.update (Function.update f c.original (c.residual.erase v))
      d (c.moved++[v])))
    (hcells : CellView t ((emitted first (pre++c.advance v d::post)).map Prod.fst))
    (hids : (allBlockIds (pre++c.advance v d::post)).Nodup)
    (hfr : s.fresh ≤ t.fresh) (hdf : d.val < t.fresh)
    (hst : t.stamp = s.stamp.set c.original.val epoch)
    (hco : t.companion = s.companion.set c.original.val (some d)) :
    BlockView t epoch first (pre++c.advance v d::post)
      (Function.update (Function.update f c.original (c.residual.erase v)) d (c.moved++[v])) := by
  have hget : c.companion.getD d = d := by rcases hd with hd | hd <;> simp [hd]
  have hnewids : blockIds (c.advance v d) = [c.original,d] := by simp [blockIds,Block.advance,hget]
  have hsep : List.Disjoint [c.original,d] (allBlockIds (pre++post)) := by
    have hh := middle_disjoint (allBlockIds pre) (blockIds (c.advance v d)) (allBlockIds post)
      (by simpa [allBlockIds,List.append_assoc] using hids)
    simpa [hnewids,allBlockIds_append] using hh
  have hother (e : Block n b) (he : e ∈ pre++post) (x : Fin b) (hx : x ∈ blockIds e) :
      x ≠ c.original ∧ x ≠ d := by
    have hm : x ∈ allBlockIds (pre++post) := List.mem_flatMap.mpr ⟨e,he,hx⟩
    constructor
    · intro hxc; subst x; exact (List.disjoint_left.mp hsep (by simp)) hm
    · intro hxd; subst x; exact (List.disjoint_left.mp hsep (by simp)) hm
  have hold (e : Block n b) (he : e ∈ pre++post) : e ∈ pre++c::post := by
    simp only [List.mem_append,List.mem_cons] at he ⊢
    tauto
  have hc : c ∈ pre++c::post := by simp
  have hsubset : allBlockIds (pre++c::post) ⊆ allBlockIds (pre++c.advance v d::post) := by
    intro x hx
    simp only [allBlockIds,List.flatMap_append,List.flatMap_cons,List.mem_append] at hx ⊢
    rcases hx with hx | hx | hx
    · exact Or.inl hx
    · right; left
      rw [hnewids]
      rcases (mem_blockIds c x).mp hx with rfl | hx
      · simp
      · have he : x=d := by rcases hd with hd | hd <;> simp_all
        simp [he]
    · exact Or.inr (Or.inr hx)
  constructor
  · exact hv
  · exact hcells
  · intro e he
    simp only [List.mem_append,List.mem_cons] at he
    rcases he with he | rfl | he
    all_goals try {
      have hm : e ∈ pre++post := by simp [he]
      have hne := hother e hm e.original (by simp [blockIds])
      simpa [Function.update,hne.1,hne.2] using h.original e (hold e hm) }
    simp [Block.advance,Function.update,hcd,Ne.symm hcd]
  · intro e he x hx
    simp only [List.mem_append,List.mem_cons] at he
    rcases he with he | rfl | he
    all_goals try {
      have hm : e ∈ pre++post := by simp [he]
      have hne := hother e hm x ((mem_blockIds e x).mpr (Or.inr hx))
      simpa [Function.update,hne.1,hne.2] using h.companion e (hold e hm) x hx }
    have hxd : x=d := by simpa [Block.advance,hget] using hx.symm
    subst x
    simp [Block.advance]
  · intro x hx
    have hxo : x ∉ allBlockIds (pre++c::post) := fun hm => hx (hsubset hm)
    have hxc : x ≠ c.original := by
      intro he; subst x; apply hx
      simp [allBlockIds,blockIds,Block.advance]
    have hxd : x ≠ d := by
      intro he; subst x; apply hx
      simp [allBlockIds,blockIds,Block.advance,hget]
    simpa [Function.update,hxc,hxd] using h.outside x hxo
  · exact hids
  · intro x hx
    simp only [allBlockIds,List.flatMap_append,List.flatMap_cons,List.mem_append] at hx
    rcases hx with hx | hx | hx
    · exact (h.allocated x (by simp [allBlockIds,hx])).trans_le hfr
    · rw [hnewids] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (h.allocated c.original (by simp [allBlockIds,blockIds])).trans_le hfr
      · have he : x=d := List.mem_singleton.mp hx
        simpa [he] using hdf
    · exact (h.allocated x (by simp [allBlockIds,hx])).trans_le hfr
  · intro e he
    simp only [List.mem_append,List.mem_cons] at he
    rcases he with he | rfl | he
    · exact h.valid e (by simp [he])
    · exact c.advance_valid v d
    · exact h.valid e (by simp [he])
  · intro e he heq
    simp only [List.mem_append,List.mem_cons] at he
    rcases he with he | rfl | he
    all_goals try {
      have hm : e ∈ pre++post := by simp [he]
      have hne := hother e hm e.original (by simp [blockIds])
      have hnval : c.original.val ≠ e.original.val := fun he => hne.1 (Fin.ext he).symm
      simpa [hst,hnval] using h.untouched e (hold e hm) heq }
    simp [Block.advance] at heq
  · intro e he x heq
    simp only [List.mem_append,List.mem_cons] at he
    rcases he with he | rfl | he
    all_goals try {
      have hm : e ∈ pre++post := by simp [he]
      have hne := hother e hm e.original (by simp [blockIds])
      have hnval : c.original.val ≠ e.original.val := fun he => hne.1 (Fin.ext he).symm
      simpa [hst,hco,hnval] using h.touched e (hold e hm) x heq }
    have hxd : x=d := by simpa [Block.advance,hget] using heq.symm
    subst x
    simp [Block.advance,hst,hco]
  · intro x
    by_cases hx : x=c.original
    · subst x; simp [hst]
    · have hnval : c.original.val ≠ x.val := fun he => hx (Fin.ext he).symm
      simpa [hst,hnval] using h.stampBound x

end HiddenCircuits.DH.LexBFSPartition
