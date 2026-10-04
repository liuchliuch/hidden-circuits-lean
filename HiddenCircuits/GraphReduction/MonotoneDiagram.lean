import HiddenCircuits.GraphReduction.MonotoneBlocks
import HiddenCircuits.GraphReduction.MonotoneVertices

/-! The actual integer endpoint ranks in the Section 9 permutation representation. -/
namespace HiddenCircuits.GraphReduction

/-- Rank-block and within-block labels on the upper line. -/
def topBlock {n h s : ℕ} : MonotoneVertex n h s → Fin (h+1)
  | .inl (.inl (j,_)) => j
  | .inl (.inr (r,_)) => r.castSucc
  | .inr (.inl (r,_)) => r.castSucc
  | .inr (.inr (r,_)) => r.castSucc

def bottomBlock {n h s : ℕ} : MonotoneVertex n h s → Fin (h+1)
  | .inl (.inl (j,_)) => j
  | .inl (.inr (r,_)) => r.succ
  | .inr (.inl (r,_)) => r.succ
  | .inr (.inr (r,_)) => r.succ

def endpointContent {n h s : ℕ} : MonotoneVertex n h s → BlockContent n s
  | .inl (.inl (_,u)) => .inl (.inl u)
  | .inl (.inr (_,q)) => .inr (.inr q)
  | .inr (.inl (_,v)) => .inl (.inr v)
  | .inr (.inr (_,t)) => .inr (.inl t)

def topDecode {n h s : ℕ} (j : Fin (h+1)) : BlockContent n s → Option (MonotoneVertex n h s)
  | .inl (.inl u) => some (.inl (.inl (j,u)))
  | .inl (.inr v) => if hj : j.val<h then some (.inr (.inl (⟨j.val,hj⟩,v))) else none
  | .inr (.inl t) => if hj : j.val<h then some (.inr (.inr (⟨j.val,hj⟩,t))) else none
  | .inr (.inr q) => if hj : j.val<h then some (.inl (.inr (⟨j.val,hj⟩,q))) else none

def bottomDecode {n h s : ℕ} (j : Fin (h+1)) : BlockContent n s → Option (MonotoneVertex n h s)
  | .inl (.inl u) => some (.inl (.inl (j,u)))
  | .inl (.inr v) => if hj : 0<j.val then some (.inr (.inl (⟨j.val-1,by have := j.isLt; omega⟩,v))) else none
  | .inr (.inl t) => if hj : 0<j.val then some (.inr (.inr (⟨j.val-1,by have := j.isLt; omega⟩,t))) else none
  | .inr (.inr q) => if hj : 0<j.val then some (.inl (.inr (⟨j.val-1,by have := j.isLt; omega⟩,q))) else none

 theorem topDecode_pack {n h s : ℕ} (v : MonotoneVertex n h s) :
    topDecode (topBlock v) (endpointContent v) = some v := by
  rcases v with ((⟨j,u⟩ | ⟨r,q⟩) | (⟨r,v⟩ | ⟨r,t⟩)) <;>
    simp [topDecode,topBlock,endpointContent]
 theorem bottomDecode_pack {n h s : ℕ} (v : MonotoneVertex n h s) :
    bottomDecode (bottomBlock v) (endpointContent v) = some v := by
  rcases v with ((⟨j,u⟩ | ⟨r,q⟩) | (⟨r,v⟩ | ⟨r,t⟩)) <;>
    simp [bottomDecode,bottomBlock,endpointContent]

 theorem topPacking_injective {n h s : ℕ} :
    Function.Injective (fun v : MonotoneVertex n h s => (topBlock v,endpointContent v)) := by
  intro x y h
  apply Option.some.inj
  have hb : topBlock x=topBlock y := congrArg Prod.fst h
  have hc : endpointContent x=endpointContent y := congrArg Prod.snd h
  rw [← topDecode_pack x,← topDecode_pack y,hb,hc]
 theorem bottomPacking_injective {n h s : ℕ} :
    Function.Injective (fun v : MonotoneVertex n h s => (bottomBlock v,endpointContent v)) := by
  intro x y h
  apply Option.some.inj
  have hb : bottomBlock x=bottomBlock y := congrArg Prod.fst h
  have hc : endpointContent x=endpointContent y := congrArg Prod.snd h
  rw [← bottomDecode_pack x,← bottomDecode_pack y,hb,hc]

/-- The final upper block and initial lower block contain only their unperturbed even layer. -/
def upperModeAt {p h : ℕ} (pairs : Fin h → CutPair p) (j : Fin (h+1)) : InterleaveMode (2*p) :=
  if hj : j.val<h then (pairs ⟨j.val,hj⟩).upperMode else .ordinary

def lowerModeAt {p h : ℕ} (pairs : Fin h → CutPair p) (j : Fin (h+1)) : InterleaveMode (2*p) :=
  if hj : 0<j.val then (pairs ⟨j.val-1,by have := j.isLt; omega⟩).lowerMode else .ordinary

@[simp] theorem upperModeAt_castSucc {p h : ℕ} (pairs : Fin h → CutPair p) (r : Fin h) :
    upperModeAt pairs r.castSucc = (pairs r).upperMode := by simp [upperModeAt]
@[simp] theorem lowerModeAt_succ {p h : ℕ} (pairs : Fin h → CutPair p) (r : Fin h) :
    lowerModeAt pairs r.succ = (pairs r).lowerMode := by simp [lowerModeAt]

 theorem upperModeAt_eq {p h : ℕ} (pairs : Fin h → CutPair p) (j : Fin (h+1)) (r : Fin h)
    (h : j.val=r.val) : upperModeAt pairs j=(pairs r).upperMode := by
  have he : j=r.castSucc := Fin.ext h
  rw [he,upperModeAt_castSucc]
 theorem lowerModeAt_eq {p h : ℕ} (pairs : Fin h → CutPair p) (j : Fin (h+1)) (r : Fin h)
    (h : j.val=r.val+1) : lowerModeAt pairs j=(pairs r).lowerMode := by
  have he : j=r.succ := Fin.ext h
  rw [he,lowerModeAt_succ]

/-- The actual finite endpoint positions before encoding them as integer ranks. -/
def upperPosition {p h s : ℕ} (pairs : Fin h → CutPair p) (v : MonotoneVertex (2*p) h s) :
    Fin (h+1) × Fin (endpointBlockWidth (2*p) s) :=
  (topBlock v,upperBlock (upperModeAt pairs (topBlock v)) s (endpointContent v))

def lowerPosition {p h s : ℕ} (pairs : Fin h → CutPair p) (v : MonotoneVertex (2*p) h s) :
    Fin (h+1) × Fin (endpointBlockWidth (2*p) s) :=
  (bottomBlock v,lowerBlock (lowerModeAt pairs (bottomBlock v)) s (endpointContent v))

 theorem upperPosition_injective {p h s : ℕ} (pairs : Fin h → CutPair p) :
    Function.Injective (upperPosition (s:=s) pairs) := by
  intro x y h
  have hb : topBlock x=topBlock y := congrArg Prod.fst h
  have ho := congrArg Prod.snd h
  change upperBlock (upperModeAt pairs (topBlock x)) s (endpointContent x) =
    upperBlock (upperModeAt pairs (topBlock y)) s (endpointContent y) at ho
  rw [hb] at ho
  exact topPacking_injective (Prod.ext hb ((upperBlock _ s).injective ho))
 theorem lowerPosition_injective {p h s : ℕ} (pairs : Fin h → CutPair p) :
    Function.Injective (lowerPosition (s:=s) pairs) := by
  intro x y h
  have hb : bottomBlock x=bottomBlock y := congrArg Prod.fst h
  have ho := congrArg Prod.snd h
  change lowerBlock (lowerModeAt pairs (bottomBlock x)) s (endpointContent x) =
    lowerBlock (lowerModeAt pairs (bottomBlock y)) s (endpointContent y) at ho
  rw [hb] at ho
  exact bottomPacking_injective (Prod.ext hb ((lowerBlock _ s).injective ho))

/-- Explicit integer endpoint ranks implementing all five paired-cut cases and all probes. -/
def fullMonotoneDiagram {p h : ℕ} (pairs : Fin h → CutPair p) (s : ℕ) :
    PermutationDiagram (MonotoneVertex (2*p) h s) where
  upper := ⟨fun v => digitRank (upperPosition pairs v),digitRank_injective.comp (upperPosition_injective pairs)⟩
  lower := ⟨fun v => digitRank (lowerPosition pairs v),digitRank_injective.comp (lowerPosition_injective pairs)⟩

/-- Crossings for an even-layer vertex against a shifted-block vertex reduce exactly
to the two neighboring cuts. -/
theorem crossing_neighbor_blocks {h L : ℕ} (j : Fin (h+1)) (r : Fin h)
    (a b c d : Fin L) :
    ((digitRank (j,a)<digitRank (r.castSucc,b) ∧ digitRank (r.succ,d)<digitRank (j,c)) ∨
      (digitRank (r.castSucc,b)<digitRank (j,a) ∧ digitRank (j,c)<digitRank (r.succ,d))) ↔
      (j.val=r.val ∧ b.val<a.val) ∨ (j.val=r.val+1 ∧ c.val<d.val) := by
  simp only [digitRank_lt_iff,Fin.val_castSucc,Fin.val_succ]
  omega

/-- Vertices shifted together on the two lines can cross only inside one common block. -/
theorem crossing_shifted_blocks {h L : ℕ} (r t : Fin h) (a b c d : Fin L) :
    ((digitRank (r.castSucc,a)<digitRank (t.castSucc,b) ∧ digitRank (t.succ,d)<digitRank (r.succ,c)) ∨
      (digitRank (t.castSucc,b)<digitRank (r.castSucc,a) ∧ digitRank (r.succ,c)<digitRank (t.succ,d))) ↔
      r=t ∧ ((a.val<b.val ∧ d.val<c.val) ∨ (b.val<a.val ∧ c.val<d.val)) := by
  simp only [digitRank_lt_iff,Fin.val_castSucc,Fin.val_succ,Fin.ext_iff]
  omega

 theorem crossing_equal_blocks {B L : ℕ} (j k : Fin B) (a b c d : Fin L) :
    ((digitRank (j,a)<digitRank (k,b) ∧ digitRank (k,d)<digitRank (j,c)) ∨
      (digitRank (k,b)<digitRank (j,a) ∧ digitRank (j,c)<digitRank (k,d))) ↔
      j=k ∧ ((a.val<b.val ∧ d.val<c.val) ∨ (b.val<a.val ∧ c.val<d.val)) := by
  simp only [digitRank_lt_iff,Fin.ext_iff]
  omega

end HiddenCircuits.GraphReduction
