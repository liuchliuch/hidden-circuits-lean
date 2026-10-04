import HiddenCircuits.GraphReduction.MonotoneVertices
import HiddenCircuits.GraphReduction.CliqueProbeGraph

/-! Literal original clique layers and one private probe clique per layer. -/
namespace HiddenCircuits.GraphReduction.PrivateProbe

abbrev Layer (h : ℕ) := Fin (h+1) ⊕ Fin h
abbrev Original (n h : ℕ) := EvenVertex n h ⊕ OddVertex n h
abbrev Vertex (n h s : ℕ) := Original n h ⊕ (Layer h × Fin s)

def layerTag {n h : ℕ} : Original n h → Layer h
  | .inl (j,_) => .inl j
  | .inr (r,_) => .inr r

def layerNumber {n h : ℕ} : Original n h → ℕ
  | .inl (j,_) => 2*j.val
  | .inr (r,_) => 2*r.val+1

def cliqueGraph {p h : ℕ} (pairs : Fin h → CutPair p) : SimpleGraph (Original (2*p) h) where
  Adj
    | .inl (j,u), .inl (k,v) => j=k ∧ u≠v
    | .inr (r,u), .inr (t,v) => r=t ∧ u≠v
    | .inl x, .inr y => targetRelation pairs x y
    | .inr y, .inl x => targetRelation pairs x y
  symm := by
    intro x y
    rcases x with ⟨j,u⟩|⟨r,u⟩ <;> rcases y with ⟨k,v⟩|⟨t,v⟩
    · exact fun h => ⟨h.1.symm,h.2.symm⟩
    · exact id
    · exact id
    · exact fun h => ⟨h.1.symm,h.2.symm⟩
  loopless := ⟨by intro x; rcases x with ⟨j,u⟩|⟨r,u⟩ <;> simp⟩

def queryGraph {p h : ℕ} (pairs : Fin h → CutPair p) (s : ℕ) : SimpleGraph (Vertex (2*p) h s) :=
  cliqueProbeGraph (cliqueGraph pairs) (fun i v => layerTag v=i) s

abbrev RetainedOriginal (p h : ℕ) (S T : State (2*p) p) := RetainedEven p h S T ⊕ OddVertex (2*p) h

def originalEmbedding {p h : ℕ} (S T : State (2*p) p) : RetainedOriginal p h S T ↪ Original (2*p) h :=
  (⟨Subtype.val,Subtype.val_injective⟩ : RetainedEven p h S T ↪ EvenVertex (2*p) h).sumMap
    (Function.Embedding.refl _)

def retainedCliqueGraph {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) :
    SimpleGraph (RetainedOriginal p h S T) := (cliqueGraph pairs).comap (originalEmbedding S T)

def retainedLayer {p h : ℕ} (S T : State (2*p) p) (v : RetainedOriginal p h S T) : Layer h :=
  layerTag (originalEmbedding S T v)

def retainedQueryGraph {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :=
  cliqueProbeGraph (retainedCliqueGraph pairs S T) (fun i v => retainedLayer S T v=i) s

def retainedEmbedding {p h : ℕ} (S T : State (2*p) p) (s : ℕ) :
    (RetainedOriginal p h S T ⊕ (Layer h × Fin s)) ↪ Vertex (2*p) h s :=
  (originalEmbedding S T).sumMap (Function.Embedding.refl _)

end HiddenCircuits.GraphReduction.PrivateProbe
