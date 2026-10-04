import HiddenCircuits.ArbitraryJoinMatching
import HiddenCircuits.LayeredPaths

/-! An actual simple graph with independent layers and only the supplied consecutive cuts. -/
namespace HiddenCircuits.Layered
open HiddenCircuits.DH

/-- Full layers, recursively grouped from left to right. -/
def Vertices (p : ℕ) : ℕ → Type
  | 0 => Fin (2*p)
  | l+1 => Fin (2*p) ⊕ Vertices p l

instance verticesFintype (p : ℕ) : (l : ℕ) → Fintype (Vertices p l)
  | 0 => inferInstanceAs (Fintype (Fin (2*p)))
  | l+1 => by
    letI := verticesFintype p l
    exact inferInstanceAs (Fintype (Fin (2*p) ⊕ Vertices p l))
instance verticesDecidableEq (p : ℕ) : (l : ℕ) → DecidableEq (Vertices p l)
  | 0 => inferInstanceAs (DecidableEq (Fin (2*p)))
  | l+1 => by
    letI := verticesDecidableEq p l
    exact inferInstanceAs (DecidableEq (Fin (2*p) ⊕ Vertices p l))

/-- Actual track inclusions of the first and last layers. -/
def first (p : ℕ) : (l : ℕ) → Fin (2*p) → Vertices p l
  | 0, x => x
  | _+1, x => .inl x
def last (p : ℕ) : (l : ℕ) → Fin (2*p) → Vertices p l
  | 0, x => x
  | l+1, x => .inr (last p l x)

 theorem first_injective (p l : ℕ) : Function.Injective (first p l) := by
  cases l with
  | zero => exact Function.injective_id
  | succ l => exact Sum.inl_injective
 theorem last_injective (p l : ℕ) : Function.Injective (last p l) := by
  induction l with
  | zero => exact Function.injective_id
  | succ l ih => exact Sum.inr_injective.comp ih

/-- Position in the list of layers and the genuine track label. -/
def layer (p : ℕ) : (l : ℕ) → Vertices p l → ℕ
  | 0, _ => 0
  | _+1, .inl _ => 0
  | l+1, .inr v => layer p l v + 1
def track (p : ℕ) : (l : ℕ) → Vertices p l → Fin (2*p)
  | 0, x => x
  | _+1, .inl x => x
  | l+1, .inr v => track p l v

@[simp] theorem layer_first (p l : ℕ) (x : Fin (2*p)) : layer p l (first p l x) = 0 := by
  cases l <;> rfl
@[simp] theorem layer_last (p l : ℕ) (x : Fin (2*p)) : layer p l (last p l x) = l := by
  induction l with
  | zero => rfl
  | succ l ih => simpa only [last,layer,ih]

@[simp] theorem vertices_card (p l : ℕ) : Fintype.card (Vertices p l) = (l+1)*(2*p) := by
  induction l with
  | zero => simp [Vertices]
  | succ l ih =>
    change Fintype.card (Fin (2*p) ⊕ Vertices p l) = _
    rw [Fintype.card_sum,Fintype.card_fin,ih]
    ring

/-- Full independent layers, with exactly the given Boolean cut edges. -/
def graph {p : ℕ} : (w : List (UnweightedCut p)) → SimpleGraph (Vertices p w.length)
  | [] => ⊥
  | R::w => joinGraph ⊥ (graph w)
      (fun x v => ∃ y, first p w.length y = v ∧ R x y = true)

/-- Every actual graph edge joins two consecutive layers. -/
theorem graph_adj_consecutive {p : ℕ} (w : List (UnweightedCut p))
    (v u : Vertices p w.length) (h : (graph w).Adj v u) :
    layer p w.length v + 1 = layer p w.length u ∨
      layer p w.length u + 1 = layer p w.length v := by
  induction w with
  | nil => exact h.elim
  | cons R w ih =>
    cases v with
    | inl x =>
      cases u with
      | inl y => exact h.elim
      | inr u =>
        obtain ⟨y,rfl,_⟩ := h
        change 1 = layer p w.length (first p w.length y) + 1 ∨
          (layer p w.length (first p w.length y) + 1) + 1 = 0
        rw [layer_first]
        exact Or.inl rfl
    | inr v =>
      cases u with
      | inl x =>
        obtain ⟨y,rfl,_⟩ := h
        change (layer p w.length (first p w.length y) + 1) + 1 = 0 ∨
          1 = layer p w.length (first p w.length y) + 1
        rw [layer_first]
        exact Or.inr rfl
      | inr u =>
        have hh := ih v u h
        change (layer p w.length v + 1) + 1 = layer p w.length u + 1 ∨
          (layer p w.length u + 1) + 1 = layer p w.length v + 1
        omega

/-- Vertices deleted at the two boundary layers: the complement of S and T itself. -/
def Ghost {p : ℕ} (w : List (UnweightedCut p)) (S T : State (2*p) p)
    (v : Vertices p w.length) : Prop :=
  (∃ x, first p w.length x = v ∧ x ∉ S.val) ∨
    (∃ x, last p w.length x = v ∧ x ∈ T.val)

/-- Actual retained vertices; at positive length the first layer is S and the last is complement T. -/
def Retained {p : ℕ} (w : List (UnweightedCut p)) (S T : State (2*p) p) :=
  {v : Vertices p w.length // ¬ Ghost w S T v}

/-- The requested simple-unweighted layered graph, with the boundary vertices deleted. -/
def retainedGraph {p : ℕ} (w : List (UnweightedCut p)) (S T : State (2*p) p) :
    SimpleGraph (Retained w S T) := (graph w).induce {v | ¬ Ghost w S T v}

noncomputable instance {p : ℕ} (w : List (UnweightedCut p)) (S T : State (2*p) p) :
    Fintype (Retained w S T) := by
  classical
  unfold Retained
  infer_instance

/-- The graph's perfect-matching count is an ordinary count of mathlib subgraphs. -/
noncomputable def matchingCount {p : ℕ} (w : List (UnweightedCut p)) (S T : State (2*p) p) : ℕ :=
  perfectMatchingCount (retainedGraph w S T)

/-- An equivalent full-layer description will leave precisely the deleted vertices unmatched. -/
def BoundaryCondition {p : ℕ} (w : List (UnweightedCut p)) (S T : State (2*p) p)
    (m : EncodedMatching (graph w)) : Prop :=
  ∀ v, m.val v = none ↔ Ghost w S T v

def BoundaryMatching {p : ℕ} (w : List (UnweightedCut p)) (S T : State (2*p) p) :=
  {m : EncodedMatching (graph w) // BoundaryCondition w S T m}

noncomputable instance {p : ℕ} (w : List (UnweightedCut p)) (S T : State (2*p) p) :
    Fintype (BoundaryMatching w S T) := by
  classical
  unfold BoundaryMatching
  infer_instance

end HiddenCircuits.Layered
