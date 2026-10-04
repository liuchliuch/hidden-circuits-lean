import HiddenCircuits.Complexity.GraphEncoding
import HiddenCircuits.GraphIsomorphismCount
import Mathlib.Data.List.NodupEquivFin

/-! Explicit finite label lists and ordinary binary adjacency-matrix emission. -/
namespace HiddenCircuits.GraphReduction

/-- A duplicate-free exhaustive vertex list; its data are an actual executable list. -/
structure Enumeration (V : Type*) where
  labels : List V
  nodup : labels.Nodup
  complete : ∀ v, v∈labels

namespace Enumeration
variable {V W : Type*}

def fin (n : ℕ) : Enumeration (Fin n) :=
  ⟨List.finRange n,List.nodup_finRange n,fun i => by simp⟩

def prod (a : Enumeration V) (b : Enumeration W) : Enumeration (V × W) where
  labels := a.labels.product b.labels
  nodup := a.nodup.product b.nodup
  complete := by rintro ⟨v,w⟩; exact List.mem_product.mpr ⟨a.complete v,b.complete w⟩

def sum (a : Enumeration V) (b : Enumeration W) : Enumeration (V ⊕ W) where
  labels := a.labels.map Sum.inl ++ b.labels.map Sum.inr
  nodup := by
    rw [List.nodup_append']
    refine ⟨a.nodup.map Sum.inl_injective,b.nodup.map Sum.inr_injective,?_⟩
    intro v hv hw
    obtain ⟨x,_,hx⟩ := List.mem_map.mp hv
    obtain ⟨y,_,hy⟩ := List.mem_map.mp hw
    exact Sum.inl_ne_inr (hx.trans hy.symm)
  complete := by
    intro v
    cases v with
    | inl v => simp [a.complete v]
    | inr w => simp [b.complete w]

/-- Boundary deletion computes a filtered list and retains only proof-irrelevant membership evidence. -/
def subtype (a : Enumeration V) (P : V → Prop) [DecidablePred P] : Enumeration {v // P v} where
  labels := (a.labels.filter (fun v => decide (P v))).attach.map
    (fun v : {v // v∈a.labels.filter (fun v => decide (P v))} =>
      (⟨v.val,by simpa only [decide_eq_true_eq] using (List.mem_filter.mp v.property).2⟩ : {v // P v}))
  nodup := by
    apply List.Nodup.map _ ((a.nodup.filter _).attach)
    intro v w he
    exact Subtype.ext (congrArg (fun z : {v // P v} => z.val) he)
  complete := by
    rintro ⟨v,hv⟩
    apply List.mem_map.mpr
    refine ⟨⟨v,?_⟩,by simp,?_⟩
    · simp [a.complete v,hv]
    · rfl

noncomputable def equiv (a : Enumeration V) : Fin a.labels.length ≃ V :=
  Equiv.ofBijective a.labels.get ⟨a.nodup.injective_get,fun v => List.mem_iff_get.mp (a.complete v)⟩

 theorem length_eq_card [Fintype V] (a : Enumeration V) : a.labels.length=Fintype.card V := by
  simpa only [Fintype.card_fin] using Fintype.card_congr a.equiv

/-- The emitted matrix queries adjacency only on actual labels, in ordinary row-major order. -/
def matrixGraph (a : Enumeration V) (G : SimpleGraph V) [DecidableRel G.Adj] :
    Complexity.MatrixGraph a.labels.length where
  edge i j := decide (G.Adj (a.labels.get i) (a.labels.get j))
  symm i j := by simp only [G.adj_comm]
  loopless i := by simp

noncomputable def graphIso (a : Enumeration V) (G : SimpleGraph V) [DecidableRel G.Adj] :
    (a.matrixGraph G).graph ≃g G where
  toEquiv := a.equiv
  map_rel_iff' := by intro i j; simp [Complexity.MatrixGraph.graph,matrixGraph,equiv]

 theorem matchingCount (a : Enumeration V) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    perfectMatchingCount (a.matrixGraph G).graph=perfectMatchingCount G :=
  perfectMatchingCount_congr (a.graphIso G)

def graphInput (a : Enumeration V) (G : SimpleGraph V) [DecidableRel G.Adj] : Complexity.GraphInput :=
  ⟨a.labels.length,a.matrixGraph G⟩

def graphBits (a : Enumeration V) (G : SimpleGraph V) [DecidableRel G.Adj] : Complexity.BitString :=
  (a.graphInput G).encode

@[simp] theorem graphBits_roundtrip (a : Enumeration V) (G : SimpleGraph V) [DecidableRel G.Adj] :
    Complexity.GraphInput.decode (a.graphBits G)=some (a.graphInput G) :=
  Complexity.GraphInput.decode_encode _

 theorem graphBits_length (a : Enumeration V) (G : SimpleGraph V) [DecidableRel G.Adj] :
    (a.graphBits G).length=2*a.labels.length+a.labels.length^2+1 := by
  simpa only [graphBits,graphInput,pow_two] using Complexity.GraphInput.encode_length (a.graphInput G)

end Enumeration
end HiddenCircuits.GraphReduction
