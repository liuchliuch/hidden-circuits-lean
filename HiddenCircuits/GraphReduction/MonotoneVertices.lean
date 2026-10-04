import HiddenCircuits.GraphReduction.ProbeGraph
import HiddenCircuits.PairedLayerGraph

/-! Shared literal vertex types and cut relations for the Section 9 constructions. -/
namespace HiddenCircuits.GraphReduction

/-- Full even layers 0,2,...,2h and full odd layers 1,3,...,2h-1. -/
abbrev EvenVertex (n h : ℕ) := Fin (h+1) × Fin n
abbrev OddVertex (n h : ℕ) := Fin h × Fin n

/-- Exactly the boundary-retained even vertices; every odd-layer vertex is retained. -/
def RetainedEven (p h : ℕ) (S T : State (2*p) p) :=
  {v : EvenVertex (2*p) h //
    (v.1.val=0 → v.2 ∈ S.val) ∧ (v.1.val=h → v.2 ∉ T.val)}

noncomputable instance (p h : ℕ) (S T : State (2*p) p) : Fintype (RetainedEven p h S T) := by
  classical
  unfold RetainedEven
  infer_instance
noncomputable instance (p h : ℕ) (S T : State (2*p) p) : DecidableEq (RetainedEven p h S T) :=
  Classical.decEq _

/-- Full endpoint-diagram vertices with Q on the even side and P on the odd side. -/
abbrev MonotoneVertex (n h s : ℕ) :=
  ProbePart (EvenVertex n h) (Fin h) s ⊕ ProbePart (OddVertex n h) (Fin h) s

/-- The genuine target cut relation, with no probes and no complemented cuts. -/
def targetRelation {p h : ℕ} (pairs : Fin h → CutPair p)
    (x : EvenVertex (2*p) h) (y : OddVertex (2*p) h) : Prop :=
  (x.1.val=y.1.val ∧ (pairs y.1).first x.2 y.2=1) ∨
    (x.1.val=y.1.val+1 ∧ (pairs y.1).second y.2 x.2=1)

/-- The original portion of the query graph: first cuts unchanged, second cuts complemented. -/
def queryRelation {p h : ℕ} (pairs : Fin h → CutPair p)
    (x : EvenVertex (2*p) h) (y : OddVertex (2*p) h) : Prop :=
  (x.1.val=y.1.val ∧ (pairs y.1).first x.2 y.2=1) ∨
    (x.1.val=y.1.val+1 ∧ (pairs y.1).second y.2 x.2≠1)

/-- The two actual attachment neighborhoods of probe pair r. -/
def evenAttachment {n h : ℕ} (r : Fin h) (x : EvenVertex n h) : Prop := x.1.val=r.val+1
def oddAttachment {n h : ℕ} (r : Fin h) (y : OddVertex n h) : Prop := y.1=r

/-- Boundary-retained query relation and attachments, on the shared coordinate types. -/
def retainedQueryRelation {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x : RetainedEven p h S T) (y : OddVertex (2*p) h) : Prop := queryRelation pairs x.val y

def retainedTargetRelation {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x : RetainedEven p h S T) (y : OddVertex (2*p) h) : Prop := targetRelation pairs x.val y

def retainedEvenAttachment {p h : ℕ} (S T : State (2*p) p) (r : Fin h)
    (x : RetainedEven p h S T) : Prop := evenAttachment r x.val

/-- The actual retained Section 9 query graph, using exactly the probe worker's graph type. -/
def monotoneQueryGraph {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :=
  probeGraph (retainedQueryRelation pairs S T) (retainedEvenAttachment S T) oddAttachment s

/-- The same graph before deleting the unwanted boundary vertices. -/
def fullMonotoneQueryGraph {p h : ℕ} (pairs : Fin h → CutPair p) (s : ℕ) :=
  probeGraph (queryRelation pairs) evenAttachment oddAttachment s

/-- Boundary deletion is a literal inclusion of vertex labels, preserving all probes. -/
def retainedVertexEmbedding {p h : ℕ} (S T : State (2*p) p) (s : ℕ) :
    (ProbePart (RetainedEven p h S T) (Fin h) s ⊕ ProbePart (OddVertex (2*p) h) (Fin h) s) ↪
      MonotoneVertex (2*p) h s :=
  ((⟨Subtype.val,Subtype.val_injective⟩ : RetainedEven p h S T ↪ EvenVertex (2*p) h).sumMap
    (Function.Embedding.refl _)).sumMap (Function.Embedding.refl _)

end HiddenCircuits.GraphReduction
