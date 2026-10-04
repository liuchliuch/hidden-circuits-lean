import HiddenCircuits.Complexity.SharpP
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Logic.Equiv.Fin.Basic

/-! Concrete binary encodings and exact independent-set certificates. -/
namespace HiddenCircuits.Complexity

/-- An executable Boolean adjacency matrix for an actual simple graph. -/
@[ext] structure MatrixGraph (n : ℕ) where
  edge : Fin n → Fin n → Bool
  symm : ∀ i j, edge i j = edge j i
  loopless : ∀ i, edge i i = false

namespace MatrixGraph
variable {n : ℕ}

def graph (G : MatrixGraph n) : SimpleGraph (Fin n) where
  Adj i j := G.edge i j = true
  symm := by intro i j h; rwa [G.symm j i]
  loopless := ⟨by intro i h; simpa [G.loopless] using h⟩

instance (G : MatrixGraph n) : DecidableRel G.graph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

/-- Row-major adjacency bits, exactly one per ordered vertex pair. -/
def bits (G : MatrixGraph n) : BitString :=
  List.ofFn (fun i : Fin (n*n) =>
    G.edge (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)

@[simp] theorem bits_length (G : MatrixGraph n) : G.bits.length = n*n := by
  simp [bits]

theorem bits_injective : Function.Injective (bits (n := n)) := by
  intro G H h
  have he := List.ofFn_injective h
  apply MatrixGraph.ext
  funext i j
  have hij := congrFun he (finProdFinEquiv (i,j))
  simpa using hij

/-- Decode a fixed-size matrix, rejecting nonsymmetric matrices and self-loops. -/
def ofBits (n : ℕ) (s : BitString) : Option (MatrixGraph n) :=
  if h : s.length = n*n then
    let e : Fin n → Fin n → Bool := fun i j =>
      s.get ⟨(finProdFinEquiv (i,j)).val, by simpa [h] using (finProdFinEquiv (i,j)).isLt⟩
    if hs : ∀ i j, e i j = e j i then
      if hl : ∀ i, e i i = false then some ⟨e,hs,hl⟩ else none
    else none
  else none

theorem get_bits (G : MatrixGraph n) (i j : Fin n)
    (h : (finProdFinEquiv (i,j)).val < G.bits.length) :
    G.bits.get ⟨(finProdFinEquiv (i,j)).val,h⟩ = G.edge i j := by
  simp only [bits, List.get_ofFn]
  change G.edge (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 = G.edge i j
  simp only [Equiv.symm_apply_apply]

@[simp] theorem ofBits_bits (G : MatrixGraph n) : ofBits n G.bits = some G := by
  unfold ofBits
  simp only [bits_length, dite_true]
  simp only [get_bits]
  rw [dif_pos G.symm, dif_pos G.loopless]

/-- The canonical certificate chooses one bit per vertex. -/
def ValidIndependent (G : MatrixGraph n) (w : Fin n → Bool) : Prop :=
  ∀ i j, w i = true → w j = true → G.edge i j = false

instance (G : MatrixGraph n) (w : Fin n → Bool) : Decidable (G.ValidIndependent w) :=
  inferInstanceAs (Decidable (∀ i j, w i = true → w j = true → G.edge i j = false))

theorem validIndependent_iff (G : MatrixGraph n) (w : Fin n → Bool) :
    G.ValidIndependent w ↔ G.graph.IsIndepSet {i | w i = true} := by
  constructor
  · intro h i hi j hj _
    change G.edge i j ≠ true
    rw [h i j hi hj]
    decide
  · intro h i j hi hj
    by_cases hij : i = j
    · subst j; exact G.loopless i
    · have hn := h hi hj hij
      change G.edge i j ≠ true at hn
      exact Bool.eq_false_iff.mpr hn

abbrev IndependentCertificate (G : MatrixGraph n) :=
  {w : Fin n → Bool // G.ValidIndependent w}

/-- The counted objects are mathlib's actual independent vertex sets. -/
abbrev IndependentSet (G : MatrixGraph n) :=
  {s : Set (Fin n) // G.graph.IsIndepSet s}

noncomputable def independentEquiv (G : MatrixGraph n) :
    G.IndependentCertificate ≃ G.IndependentSet := by
  classical
  refine {
    toFun := fun w => ⟨{i | w.val i = true}, (G.validIndependent_iff w.val).mp w.property⟩
    invFun := fun s => ⟨fun i => decide (i ∈ s.val), ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · apply (G.validIndependent_iff _).mpr
    simpa using s.property
  · intro w
    apply Subtype.ext
    funext i
    simp
  · intro s
    apply Subtype.ext
    ext i
    simp

noncomputable instance (G : MatrixGraph n) : Fintype G.IndependentCertificate := by
  classical
  unfold IndependentCertificate
  infer_instance

noncomputable instance (G : MatrixGraph n) : Fintype G.IndependentSet := by
  classical
  unfold IndependentSet
  infer_instance

noncomputable def independentCount (G : MatrixGraph n) : ℕ := Fintype.card G.IndependentSet

theorem independentCount_eq_certificates (G : MatrixGraph n) :
    G.independentCount = Fintype.card G.IndependentCertificate :=
  Fintype.card_congr G.independentEquiv.symm

theorem independentCount_le (G : MatrixGraph n) : G.independentCount ≤ 2^n := by
  rw [independentCount_eq_certificates]
  calc
    Fintype.card G.IndependentCertificate ≤ Fintype.card (Fin n → Bool) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = 2^n := by simp

end MatrixGraph

/-- Variable-size graph inputs. Vertex names are `0,...,n-1`. -/
abbrev GraphInput := (n : ℕ) × MatrixGraph n

namespace GraphInput

def encode (G : GraphInput) : BitString :=
  pairBits (List.replicate G.1 true) G.2.bits

def decode (s : BitString) : Option GraphInput :=
  match unpairBits s with
  | none => none
  | some (header,payload) =>
    if header = List.replicate header.length true then
      (MatrixGraph.ofBits header.length payload).map (fun G => ⟨header.length,G⟩)
    else none

@[simp] theorem decode_encode (G : GraphInput) : decode (encode G) = some G := by
  rcases G with ⟨n,G⟩
  simp only [decode,encode,unpair_pairBits]
  simp_rw [List.length_replicate]
  simp
  rw [show (List.replicate n true).length = n by simp]
  exact ⟨G, G.ofBits_bits, HEq.rfl⟩

/-- A complete executable binary encoder/decoder, not merely a size measure. -/
def encoding : Computability.FinEncoding GraphInput where
  Γ := Bool
  ΓFin := inferInstance
  encode := encode
  decode := decode
  decode_encode := decode_encode

theorem encode_injective : Function.Injective encode := encoding.encode_injective

@[simp] theorem encode_length (G : GraphInput) :
    (encode G).length = 2*G.1 + G.1*G.1 + 1 := by
  simp [encode]

theorem vertices_le_length (G : GraphInput) : G.1 ≤ (encode G).length := by
  rw [encode_length]
  omega

/-- Invalid binary inputs have answer zero; valid inputs count actual independent sets. -/
noncomputable def independentSetProblem (s : BitString) : ℕ :=
  match decode s with
  | none => 0
  | some G => G.2.independentCount

@[simp] theorem independentSetProblem_encode (G : GraphInput) :
    independentSetProblem (encode G) = G.2.independentCount := by
  simp [independentSetProblem]

end GraphInput
end HiddenCircuits.Complexity
