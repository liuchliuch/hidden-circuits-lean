import HiddenCircuits.BinomialInterpolation

namespace HiddenCircuits
noncomputable section
open scoped BigOperators
open Polynomial

/-- Exactly the five kinds of zero-one cut pairs admitted by PairEval. -/
inductive CutPair (p : ℕ) where
  | background
  | leftRise (i : Fin (2*p-1))
  | leftDrop (i : Fin (2*p-1))
  | rightRise (i : Fin (2*p-1))
  | rightDrop (i : Fin (2*p-1))
  deriving DecidableEq

/-- The actual first cut matrix in an allowed pair. -/
def CutPair.first {p : ℕ} : CutPair p → Matrix (Fin (2*p)) (Fin (2*p)) ℚ
  | .leftRise i => addedCut i
  | .leftDrop i => deletedCut i
  | _ => upper (2*p)

/-- The actual second cut matrix in an allowed pair. -/
def CutPair.second {p : ℕ} : CutPair p → Matrix (Fin (2*p)) (Fin (2*p)) ℚ
  | .rightRise i => (addedCut i).transpose
  | .rightDrop i => (deletedCut i).transpose
  | _ => (upper (2*p)).transpose

def CutPair.matrix {p : ℕ} (P : CutPair p) : Matrix (State (2*p) p) (State (2*p) p) ℚ :=
  pairedTransfer P.first P.second

/-- An ordinary finite list of paired layer transfers. -/
def pairWordMatrix {p : ℕ} (w : List (CutPair p)) : Matrix (State (2*p) p) (State (2*p) p) ℚ :=
  (w.map CutPair.matrix).prod

@[simp] theorem pairWordMatrix_append {p : ℕ} (u v : List (CutPair p)) :
    pairWordMatrix (u++v)=pairWordMatrix u * pairWordMatrix v := by
  simp [pairWordMatrix]

@[simp] theorem pairWordMatrix_replicate (p t : ℕ) :
    pairWordMatrix (List.replicate t (CutPair.background (p:=p)))=(pairedBackground p)^t := by
  simp [pairWordMatrix,CutPair.matrix,CutPair.first,CutPair.second,pairedBackground]

/-- The concrete sample word from the four rows of the paper's paired-transfer table. -/
def sampleLetter {p : ℕ} (l : Letter (2*p)) (t : ℕ) : List (CutPair p) :=
  match l.kind with
  | .R => .leftRise l.index :: List.replicate t .background
  | .D => .leftDrop l.index :: List.replicate t .background
  | .B => List.replicate t .background ++ [.rightRise l.index]
  | .E => List.replicate t .background ++ [.rightDrop l.index]

def sampleWord {p : ℕ} (w : List (Letter (2*p))) (t : ℕ) : List (CutPair p) :=
  w.flatMap (fun l => sampleLetter l t)

@[simp] theorem sampleLetter_length {p : ℕ} (l : Letter (2*p)) (t : ℕ) :
    (sampleLetter l t).length=t+1 := by
  cases l with
  | mk kind i => cases kind <;> simp [sampleLetter]

/-- Exact PairEval query length, with one shared parameter across every letter. -/
theorem sampleWord_length {p : ℕ} (w : List (Letter (2*p))) (t : ℕ) :
    (sampleWord w t).length=w.length*(t+1) := by
  induction w with
  | nil => simp [sampleWord]
  | cons l w ih =>
    change (sampleLetter l t ++ sampleWord w t).length=(w.length+1)*(t+1)
    rw [List.length_append,sampleLetter_length,ih]
    simp [Nat.add_mul,Nat.add_comm]

/-- A single degree-p² matrix polynomial parameterizes the background powers. -/
def backgroundPolynomial (p : ℕ) := unipotentPolynomial (pairedBackground p-1) (p^2)

@[simp] theorem backgroundPolynomial_nat (p t : ℕ) :
    evaluateMatrix (t:ℚ) (backgroundPolynomial p)=(pairedBackground p)^t := by
  unfold backgroundPolynomial
  simpa using unipotentPolynomial_nat _ _ (pairedBackground_nilpotent p) t

@[simp] theorem backgroundPolynomial_neg_one (p : ℕ) :
    evaluateMatrix (-1) (backgroundPolynomial p)=pairedInverse p := by
  rw [backgroundPolynomial,unipotentPolynomial_neg_one,← pairedInverse_series]

/-- Actual polynomial of a sampled elementary letter, in its correct noncommuting order. -/
def letterPairPolynomial {p : ℕ} (l : Letter (2*p)) : Matrix (State (2*p) p) (State (2*p) p) ℚ[X] :=
  match l.kind with
  | .R => constantMatrix (CutPair.matrix (.leftRise l.index)) * backgroundPolynomial p
  | .D => constantMatrix (CutPair.matrix (.leftDrop l.index)) * backgroundPolynomial p
  | .B => backgroundPolynomial p * constantMatrix (CutPair.matrix (.rightRise l.index))
  | .E => backgroundPolynomial p * constantMatrix (CutPair.matrix (.rightDrop l.index))

 theorem letterPairPolynomial_nat {p : ℕ} (l : Letter (2*p)) (t : ℕ) :
    evaluateMatrix (t:ℚ) (letterPairPolynomial l)=pairWordMatrix (sampleLetter l t) := by
  cases l with
  | mk kind i =>
    cases kind <;>
      simp [letterPairPolynomial,sampleLetter,pairWordMatrix,List.map_append,List.prod_append,
        CutPair.matrix,CutPair.first,CutPair.second,pairedBackground]

/-- Negative interpolation of every actual sample letter is its requested normalized operation. -/
theorem letterPairPolynomial_neg_one {p : ℕ} (l : Letter (2*p)) :
    evaluateMatrix (-1) (letterPairPolynomial l)=l.matrix p := by
  cases l with
  | mk kind i =>
    cases kind with
    | R => simpa [letterPairPolynomial,CutPair.matrix,CutPair.first,CutPair.second,Letter.matrix,rise]
        using paired_normalize_left (addedCut i)
    | D => simpa [letterPairPolynomial,CutPair.matrix,CutPair.first,CutPair.second,Letter.matrix,drop]
        using paired_normalize_left (deletedCut i)
    | B => simpa [letterPairPolynomial,CutPair.matrix,CutPair.first,CutPair.second,Letter.matrix,rise,← halfDual_rise]
        using paired_normalize_right (addedCut i)
    | E => simpa [letterPairPolynomial,CutPair.matrix,CutPair.first,CutPair.second,Letter.matrix,drop,← halfDual_drop]
        using paired_normalize_right (deletedCut i)

/-- There is one parameter for the entire input word, not one parameter per position. -/
def wordPairPolynomial {p : ℕ} (w : List (Letter (2*p))) : Matrix (State (2*p) p) (State (2*p) p) ℚ[X] :=
  (w.map letterPairPolynomial).prod

 theorem wordPairPolynomial_nat {p : ℕ} (w : List (Letter (2*p))) (t : ℕ) :
    evaluateMatrix (t:ℚ) (wordPairPolynomial w)=pairWordMatrix (sampleWord w t) := by
  induction w with
  | nil => simp [wordPairPolynomial,sampleWord,pairWordMatrix]
  | cons l w ih =>
    change evaluateMatrix (t:ℚ) (letterPairPolynomial l * wordPairPolynomial w) = _
    rw [evaluateMatrix_mul,letterPairPolynomial_nat,ih]
    simp only [sampleWord,List.flatMap_cons,pairWordMatrix_append]

 theorem wordPairPolynomial_neg_one {p : ℕ} (w : List (Letter (2*p))) :
    evaluateMatrix (-1) (wordPairPolynomial w)=wordMatrix p w := by
  induction w with
  | nil => simp [wordPairPolynomial]
  | cons l w ih =>
    change evaluateMatrix (-1) (letterPairPolynomial l * wordPairPolynomial w) = _
    rw [evaluateMatrix_mul,letterPairPolynomial_neg_one,ih,wordMatrix_cons]

end
end HiddenCircuits
