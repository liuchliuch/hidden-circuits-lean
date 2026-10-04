import HiddenCircuits.GraphReduction.PrivateProbeBlocks
import HiddenCircuits.GraphReduction.PrivateProbeVertices

/-! Literal finite endpoint lists for the private probes, including all four adjacent swaps. -/
namespace HiddenCircuits.GraphReduction.PrivateProbe

def topBlock {n h s : ℕ} : Vertex n h s → Fin (h+1)
  | .inl (.inl (j,_)) => j
  | .inl (.inr (r,_)) => r.castSucc
  | .inr (.inl j,_) => j
  | .inr (.inr r,_) => r.castSucc

def bottomBlock {n h s : ℕ} : Vertex n h s → Fin (h+1)
  | .inl (.inl (j,_)) => j
  | .inl (.inr (r,_)) => r.succ
  | .inr (.inl j,_) => j
  | .inr (.inr r,_) => r.succ

def content {n h s : ℕ} : Vertex n h s → BlockContent n s
  | .inl (.inl (_,u)) => .inl (.inl u)
  | .inl (.inr (_,v)) => .inl (.inr v)
  | .inr (.inl _,q) => .inr (.inl q)
  | .inr (.inr _,q) => .inr (.inr q)

def topDecode {n h s : ℕ} (j : Fin (h+1)) : BlockContent n s → Option (Vertex n h s)
  | .inl (.inl u) => some (.inl (.inl (j,u)))
  | .inl (.inr v) => if hj:j.val<h then some (.inl (.inr (⟨j.val,hj⟩,v))) else none
  | .inr (.inl q) => some (.inr (.inl j,q))
  | .inr (.inr q) => if hj:j.val<h then some (.inr (.inr ⟨j.val,hj⟩,q)) else none

def bottomDecode {n h s : ℕ} (j : Fin (h+1)) : BlockContent n s → Option (Vertex n h s)
  | .inl (.inl u) => some (.inl (.inl (j,u)))
  | .inl (.inr v) => if hj:0<j.val then some (.inl (.inr (⟨j.val-1,by have := j.isLt; omega⟩,v))) else none
  | .inr (.inl q) => some (.inr (.inl j,q))
  | .inr (.inr q) => if hj:0<j.val then some (.inr (.inr ⟨j.val-1,by have := j.isLt; omega⟩,q)) else none

 theorem topDecode_pack {n h s : ℕ} (v : Vertex n h s) :
    topDecode (topBlock v) (content v)=some v := by
  rcases v with (⟨j,u⟩|⟨r,v⟩)|(⟨j|r,q⟩) <;> simp [topDecode,topBlock,content]
 theorem bottomDecode_pack {n h s : ℕ} (v : Vertex n h s) :
    bottomDecode (bottomBlock v) (content v)=some v := by
  rcases v with (⟨j,u⟩|⟨r,v⟩)|(⟨j|r,q⟩) <;> simp [bottomDecode,bottomBlock,content]

 theorem topPacking_injective {n h s : ℕ} :
    Function.Injective (fun v : Vertex n h s => (topBlock v,content v)) := by
  intro x y h
  apply Option.some.inj
  have hb : topBlock x=topBlock y := congrArg Prod.fst h
  have hc : content x=content y := congrArg Prod.snd h
  rw [← topDecode_pack x,← topDecode_pack y,hb,hc]
 theorem bottomPacking_injective {n h s : ℕ} :
    Function.Injective (fun v : Vertex n h s => (bottomBlock v,content v)) := by
  intro x y h
  apply Option.some.inj
  have hb : bottomBlock x=bottomBlock y := congrArg Prod.fst h
  have hc : content x=content y := congrArg Prod.snd h
  rw [← bottomDecode_pack x,← bottomDecode_pack y,hb,hc]

def upperPosition {p h s : ℕ} (pairs : Fin h → CutPair p) (v : Vertex (2*p) h s) :
    Fin (h+1) × Fin (endpointBlockWidth (2*p) s) :=
  (topBlock v,top (upperModeAt pairs (topBlock v)) s (content v))

def lowerPosition {p h s : ℕ} (pairs : Fin h → CutPair p) (v : Vertex (2*p) h s) :
    Fin (h+1) × Fin (endpointBlockWidth (2*p) s) :=
  (bottomBlock v,bottom (lowerModeAt pairs (bottomBlock v)) s (content v))

 theorem upperPosition_injective {p h s : ℕ} (pairs : Fin h → CutPair p) :
    Function.Injective (upperPosition (s:=s) pairs) := by
  intro x y h
  have hb : topBlock x=topBlock y := congrArg Prod.fst h
  have ho := congrArg Prod.snd h
  change top (upperModeAt pairs (topBlock x)) s (content x) =
    top (upperModeAt pairs (topBlock y)) s (content y) at ho
  rw [hb] at ho
  exact topPacking_injective (Prod.ext hb ((top _ s).injective ho))
 theorem lowerPosition_injective {p h s : ℕ} (pairs : Fin h → CutPair p) :
    Function.Injective (lowerPosition (s:=s) pairs) := by
  intro x y h
  have hb : bottomBlock x=bottomBlock y := congrArg Prod.fst h
  have ho := congrArg Prod.snd h
  change bottom (lowerModeAt pairs (bottomBlock x)) s (content x) =
    bottom (lowerModeAt pairs (bottomBlock y)) s (content y) at ho
  rw [hb] at ho
  exact bottomPacking_injective (Prod.ext hb ((bottom _ s).injective ho))

/-- Explicit integer endpoints for the actual private-probe construction. -/
def diagram {p h : ℕ} (pairs : Fin h → CutPair p) (s : ℕ) : PermutationDiagram (Vertex (2*p) h s) where
  upper := ⟨fun v => digitRank (upperPosition pairs v),digitRank_injective.comp (upperPosition_injective pairs)⟩
  lower := ⟨fun v => digitRank (lowerPosition pairs v),digitRank_injective.comp (lowerPosition_injective pairs)⟩

 theorem diagram_adj {p h : ℕ} (pairs : Fin h → CutPair p) (s : ℕ) (x y : Vertex (2*p) h s) :
    (diagram pairs s).graph.Adj x y ↔
      (digitRank (upperPosition pairs x)<digitRank (upperPosition pairs y) ∧
        digitRank (lowerPosition pairs y)<digitRank (lowerPosition pairs x)) ∨
      (digitRank (upperPosition pairs y)<digitRank (upperPosition pairs x) ∧
        digitRank (lowerPosition pairs x)<digitRank (lowerPosition pairs y)) := Iff.rfl

end HiddenCircuits.GraphReduction.PrivateProbe
