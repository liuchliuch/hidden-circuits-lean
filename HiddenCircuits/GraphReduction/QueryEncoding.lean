import HiddenCircuits.GraphReduction.FiniteEnumeration
import HiddenCircuits.GraphReduction.CliqueProbeDecidable
import HiddenCircuits.GraphReduction.MonotoneReduction
import HiddenCircuits.GraphReduction.UnitIntervalReduction
import HiddenCircuits.GraphReduction.PrivateProbeReduction

/-! Actual binary adjacency-matrix queries, emitted from explicit retained vertex lists. -/
namespace HiddenCircuits.GraphReduction

/-- Full rectangular labels are enumerated by actual nested finite loops. -/
def evenEnumeration (n h : ℕ) : Enumeration (EvenVertex n h) :=
  (Enumeration.fin (h+1)).prod (Enumeration.fin n)
def oddEnumeration (n h : ℕ) : Enumeration (OddVertex n h) :=
  (Enumeration.fin h).prod (Enumeration.fin n)

/-- Exactly the source/target deletions are performed by the executable filter. -/
def retainedEvenEnumeration {p h : ℕ} (S T : State (2*p) p) : Enumeration (RetainedEven p h S T) :=
  (evenEnumeration (2*p) h).subtype
    (fun v => (v.1.val=0 → v.2∈S.val) ∧ (v.1.val=h → v.2∉T.val))

def probeEnumeration (h s : ℕ) : Enumeration (Fin h × Fin s) :=
  (Enumeration.fin h).prod (Enumeration.fin s)

def monotoneEnumeration {p h : ℕ} (S T : State (2*p) p) (s : ℕ) :
    Enumeration (ProbePart (RetainedEven p h S T) (Fin h) s ⊕
      ProbePart (OddVertex (2*p) h) (Fin h) s) :=
  ((retainedEvenEnumeration S T).sum (probeEnumeration h s)).sum
    ((oddEnumeration (2*p) h).sum (probeEnumeration h s))

def unitEnumeration {p h : ℕ} (S T : State (2*p) p) (s : ℕ) :
    Enumeration (UnitOriginalVertex p h S T ⊕ (Fin (h+1) × Fin s)) :=
  ((retainedEvenEnumeration S T).sum (oddEnumeration (2*p) h)).sum (probeEnumeration (h+1) s)

def privateEnumeration {p h : ℕ} (S T : State (2*p) p) (s : ℕ) :
    Enumeration (PrivateProbe.RetainedOriginal p h S T ⊕ (PrivateProbe.Layer h × Fin s)) :=
  ((retainedEvenEnumeration S T).sum (oddEnumeration (2*p) h)).sum
    (((Enumeration.fin (h+1)).sum (Enumeration.fin h)).prod (Enumeration.fin s))

/-- These are ordinary finite Boolean adjacency-matrix graph inputs, not representation certificates. -/
def monotoneGraphInput {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    Complexity.GraphInput := (monotoneEnumeration S T s).graphInput (monotoneQueryGraph pairs S T s)
def unitGraphInput {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    Complexity.GraphInput := (unitEnumeration S T s).graphInput (unitIntervalQueryGraph pairs S T s)
def privateGraphInput {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    Complexity.GraphInput := (privateEnumeration S T s).graphInput (PrivateProbe.retainedQueryGraph pairs S T s)

 theorem monotoneGraphInput_count {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    perfectMatchingCount (monotoneGraphInput pairs S T s).2.graph=
      perfectMatchingCount (monotoneQueryGraph pairs S T s) := Enumeration.matchingCount _ _
 theorem unitGraphInput_count {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    perfectMatchingCount (unitGraphInput pairs S T s).2.graph=
      perfectMatchingCount (unitIntervalQueryGraph pairs S T s) := Enumeration.matchingCount _ _
 theorem privateGraphInput_count {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    perfectMatchingCount (privateGraphInput pairs S T s).2.graph=
      perfectMatchingCount (PrivateProbe.retainedQueryGraph pairs S T s) := Enumeration.matchingCount _ _

/-- Exact binary encoding length of any emitted matrix graph. -/
theorem graphInput_bits_bound (G : Complexity.GraphInput) (B : ℕ) (h : G.1 ≤ B) :
    G.encode.length ≤ 2*B+B^2+1 := by
  rw [Complexity.GraphInput.encode_length]
  have hh := Nat.mul_le_mul h h
  nlinarith

 theorem monotoneGraphInput_bits {p h : ℕ} (hh : 0 < h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : Fin (2*p*h+1)) :
    (monotoneGraphInput pairs S T s.val).encode.length ≤
      2*(4*p*h*(h+1))+(4*p*h*(h+1))^2+1 := by
  apply graphInput_bits_bound
  change (monotoneEnumeration S T s.val).labels.length ≤ _
  rw [Enumeration.length_eq_card]
  exact monotoneProbe_query_size hh S T s

 theorem unitGraphInput_bits {p h : ℕ} (hh : 0 < h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : Fin (2*p*h+1)) :
    (unitGraphInput pairs S T (2*s.val)).encode.length ≤
      2*(4*p*h*(h+2))+(4*p*h*(h+2))^2+1 := by
  apply graphInput_bits_bound
  change (unitEnumeration S T (2*s.val)).labels.length ≤ _
  rw [Enumeration.length_eq_card]
  exact unitIntervalProbe_query_size hh S T s

 theorem privateGraphInput_bits {p h : ℕ} (hh : 0 < h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : Fin (2*p*h+1)) :
    (privateGraphInput pairs S T (2*s.val)).encode.length ≤
      2*(8*p*h*(h+1))+(8*p*h*(h+1))^2+1 := by
  apply graphInput_bits_bound
  change (privateEnumeration S T (2*s.val)).labels.length ≤ _
  rw [Enumeration.length_eq_card]
  exact PrivateProbe.sampleQuery_size_bound hh S T s

end HiddenCircuits.GraphReduction
