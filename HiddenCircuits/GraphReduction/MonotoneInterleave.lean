import HiddenCircuits.GraphReduction.PermutationMonotone
import HiddenCircuits.PairedLayerGraph

/-! Integer ranks for the interleaved endpoint blocks and their four actual adjacent swaps. -/
namespace HiddenCircuits.GraphReduction

/-- Ordinary interleaving, or one of its literal adjacent cross-layer swaps. -/
inductive InterleaveMode (n : ℕ) where
  | ordinary
  | rise (i : Fin (n-1))
  | drop (i : Fin (n-1))

namespace InterleaveMode

/-- Ranks of the even-layer labels in the interleaved block. -/
def evenOffset {n : ℕ} : InterleaveMode n → Fin n → ℕ
  | .ordinary, u => 2*(n-1-u.val)+1
  | .rise i, u => if u.val=i.val+1 then 2*(n-1-i.val) else 2*(n-1-u.val)+1
  | .drop i, u => if u.val=i.val then 2*(n-1-i.val) else 2*(n-1-u.val)+1

/-- Ranks of the odd-layer labels in the same interleaved block. -/
def oddOffset {n : ℕ} : InterleaveMode n → Fin n → ℕ
  | .ordinary, v => 2*(n-1-v.val)
  | .rise i, v => if v.val=i.val then 2*(n-1-(i.val+1))+1 else 2*(n-1-v.val)
  | .drop i, v => if v.val=i.val then 2*(n-1-i.val)+1 else 2*(n-1-v.val)

/-- The zero-one cut that this endpoint interleaving realizes. -/
def matrix {n : ℕ} : InterleaveMode n → Matrix (Fin n) (Fin n) ℚ
  | .ordinary => upper n
  | .rise i => addedCut i
  | .drop i => deletedCut i

 theorem evenOffset_lt {n : ℕ} (m : InterleaveMode n) (u : Fin n) : m.evenOffset u < 2*n := by
  cases m <;> simp only [evenOffset] <;> (try split_ifs) <;> omega
 theorem oddOffset_lt {n : ℕ} (m : InterleaveMode n) (v : Fin n) : m.oddOffset v < 2*n := by
  cases m <;> simp only [oddOffset] <;> (try split_ifs) <;> omega

/-- Every swap preserves the decreasing track order within each original layer. -/
theorem evenOffset_lt_iff {n : ℕ} (m : InterleaveMode n) (u v : Fin n) :
    m.evenOffset u < m.evenOffset v ↔ v.val < u.val := by
  cases m <;> simp only [evenOffset] <;> (try split_ifs) <;> omega
 theorem oddOffset_lt_iff {n : ℕ} (m : InterleaveMode n) (u v : Fin n) :
    m.oddOffset u < m.oddOffset v ↔ v.val < u.val := by
  cases m <;> simp only [oddOffset] <;> (try split_ifs) <;> omega

 theorem evenOffset_injective {n : ℕ} (m : InterleaveMode n) : Function.Injective m.evenOffset := by
  intro u v h
  apply Fin.ext
  have h₁ := m.evenOffset_lt_iff u v
  have h₂ := m.evenOffset_lt_iff v u
  omega
 theorem oddOffset_injective {n : ℕ} (m : InterleaveMode n) : Function.Injective m.oddOffset := by
  intro u v h
  apply Fin.ext
  have h₁ := m.oddOffset_lt_iff u v
  have h₂ := m.oddOffset_lt_iff v u
  omega

/-- Opposite layers still have pairwise distinct endpoint ranks after the adjacent swap. -/
theorem evenOffset_ne_oddOffset {n : ℕ} (m : InterleaveMode n) (u v : Fin n) :
    m.evenOffset u ≠ m.oddOffset v := by
  cases m <;> simp only [evenOffset,oddOffset] <;> (try split_ifs) <;> omega

/-- The exact allowed-edge predicate of an interleaved cut. -/
def Allowed {n : ℕ} : InterleaveMode n → Fin n → Fin n → Prop
  | .ordinary, u,v => u.val ≤ v.val
  | .rise i, u,v => (u.val=i.val+1 ∧ v.val=i.val) ∨ u.val ≤ v.val
  | .drop i, u,v => u.val ≤ v.val ∧ ¬(u.val=i.val ∧ v.val=i.val)

 theorem odd_lt_even_allowed {n : ℕ} (m : InterleaveMode n) (u v : Fin n) :
    m.oddOffset v < m.evenOffset u ↔ m.Allowed u v := by
  have hu := u.isLt
  have hv := v.isLt
  cases m <;> simp only [oddOffset,evenOffset,Allowed] <;> (try split_ifs) <;> omega

 theorem matrix_one_iff {n : ℕ} (m : InterleaveMode n) (u v : Fin n) :
    m.matrix u v=1 ↔ m.Allowed u v := by
  cases m <;> simp only [matrix,Allowed,upper,addedCut,deletedCut,Fin.le_def] <;>
    (try split_ifs) <;> simp_all

/-- All comparisons in the actual interleaved block, including the unique perturbed pair. -/
theorem odd_lt_even_matrix {n : ℕ} (m : InterleaveMode n) (u v : Fin n) :
    m.oddOffset v < m.evenOffset u ↔ m.matrix u v=1 := by
  rw [m.odd_lt_even_allowed,m.matrix_one_iff]

 theorem even_lt_odd_matrix {n : ℕ} (m : InterleaveMode n) (u v : Fin n) :
    m.evenOffset u < m.oddOffset v ↔ m.matrix u v≠1 := by
  have hn := m.evenOffset_ne_oddOffset u v
  change _ ↔ ¬ (m.matrix u v = 1)
  rw [← m.odd_lt_even_matrix u v]
  omega
end InterleaveMode
end HiddenCircuits.GraphReduction

namespace HiddenCircuits.CutPair
open GraphReduction

/-- The upper block carries exactly a possible first-cut perturbation. -/
def upperMode {p : ℕ} : CutPair p → InterleaveMode (2*p)
  | .leftRise i => .rise i
  | .leftDrop i => .drop i
  | _ => .ordinary
/-- The lower block carries exactly a possible second-cut transpose perturbation. -/
def lowerMode {p : ℕ} : CutPair p → InterleaveMode (2*p)
  | .rightRise i => .rise i
  | .rightDrop i => .drop i
  | _ => .ordinary

@[simp] theorem upperMode_matrix {p : ℕ} (P : CutPair p) : P.upperMode.matrix=P.first := by
  cases P <;> rfl
@[simp] theorem lowerMode_matrix {p : ℕ} (P : CutPair p) : P.lowerMode.matrix=P.second.transpose := by
  cases P <;> rfl

 theorem upper_interleave_cut {p : ℕ} (P : CutPair p) (u v : Fin (2*p)) :
    P.upperMode.oddOffset v < P.upperMode.evenOffset u ↔ P.first u v=1 := by
  rw [InterleaveMode.odd_lt_even_matrix,CutPair.upperMode_matrix]

 theorem lower_interleave_cut {p : ℕ} (P : CutPair p) (u v : Fin (2*p)) :
    P.lowerMode.evenOffset v < P.lowerMode.oddOffset u ↔ P.second u v≠1 := by
  rw [InterleaveMode.even_lt_odd_matrix,CutPair.lowerMode_matrix]
  rfl

end HiddenCircuits.CutPair
