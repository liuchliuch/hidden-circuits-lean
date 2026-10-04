import HiddenCircuits.GraphReduction.UnitCoordinateExtractionModel

/-! A bounded sum potential proves a fixed, input-derived number of actual
inflationary relaxation scans suffices; no stopping certificate is an input. -/
namespace HiddenCircuits.GraphReduction.UnitCoordinateExtraction
open scoped BigOperators

def potential {n : ℕ} (x : Coordinates n) : ℕ:=∑i,x i
lemma potential_mono {n : ℕ} {x y : Coordinates n} (h:x ≤ y) : potential x ≤ potential y :=
  Finset.sum_le_sum (fun i _=>h i)
lemma potential_strict {n : ℕ} {x y : Coordinates n} (h:x ≤ y) (hne:y≠x) : potential x < potential y := by
  have hex:∃i,x i<y i:=by
    by_contra hh
    push_neg at hh
    exact hne (funext fun i=>le_antisymm (hh i) (h i))
  obtain ⟨i,hi⟩:=hex
  exact Finset.sum_lt_sum (fun j _=>h j) ⟨i,Finset.mem_univ i,hi⟩
lemma run_succ_last {n : ℕ} (D : ℕ) (edge : Fin n→Fin n→Bool) (ls : List (Fin n))
    (k : ℕ) (x : Coordinates n) : run D edge ls (k+1) x=scan D edge ls (run D edge ls k x) := by
  induction k generalizing x with
  | zero=>rfl
  | succ k ih=>exact ih (scan D edge ls x)
lemma run_growth_or_fixed {n : ℕ} (D : ℕ) (edge : Fin n→Fin n→Bool) (ls : List (Fin n))
    (k : ℕ) (x : Coordinates n) :
    scan D edge ls (run D edge ls k x)=run D edge ls k x ∨ potential x+k ≤ potential (run D edge ls k x) := by
  induction k with
  | zero=>right;simp [run]
  | succ k ih=>
    by_cases hh:scan D edge ls (run D edge ls k x)=run D edge ls k x
    · left;rw [run_succ_last,hh];exact hh
    · right
      have hi:=ih.resolve_left hh
      have hs:=potential_strict (scan_inflationary D edge ls (run D edge ls k x)) hh
      rw [run_succ_last]
      omega
lemma run_fixed_of_witness {n : ℕ} (D : ℕ) (edge : Fin n→Fin n→Bool) (ls : List (Fin n))
    (z : Coordinates n) (M k : ℕ)
    (hz:∀p∈pairs ls,pair D (edge p.1 p.2) p.1 p.2 z=z)
    (hM:∀i,z i ≤ M) (hk:n*M<k) :
    scan D edge ls (run D edge ls k (fun _=>0))=run D edge ls k (fun _=>0) := by
  have hbound:=run_le_witness D edge ls k (fun _=>0) z (fun _=>Nat.zero_le _) hz
  have hb:potential (run D edge ls k (fun _=>0)) ≤ n*M:=by
    calc
      _ ≤ ∑i : Fin n,M:=Finset.sum_le_sum (fun i _=>(hbound i).trans (hM i))
      _ = _:=by simp
  obtain h|h:=run_growth_or_fixed D edge ls k (fun _=>0)
  · exact h
  · have hp:potential (fun _ : Fin n=>0)=0:=by simp [potential]
    rw [hp] at h
    omega
end HiddenCircuits.GraphReduction.UnitCoordinateExtraction
