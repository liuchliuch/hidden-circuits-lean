import HiddenCircuits.DH.Runtime.RawNumericModel
import HiddenCircuits.DH.Runtime.NumericEncoding

/-! Uniform serialization bounds on every reachable
numeric store hold for arbitrary Boolean matrices, without a DH promise. -/
namespace HiddenCircuits.DH.Runtime.NumericEncoding
open Complexity Complexity.BinaryArithmetic NumericStateModel

def rowBound (n : ℕ) : ℕ := 2*(n+1)*((n+1)^2+3)
def tableBound (n : ℕ) : ℕ := 2*n*(rowBound n+1)
def sizesBound (n : ℕ) : ℕ := 2*n*(n+1)

lemma safe_row_bound {n : ℕ} {s : NumericStateModel.State n} (h : Safe s) (v : Fin n) :
    (rowBits s.rows[v.val]).length≤rowBound n :=
  rowBits_bound _ n ((n+1)^2) (h.row_lengths v) (h.coefficient_bound v)
lemma safe_table_bound {n : ℕ} {s : NumericStateModel.State n} (h : Safe s) :
    (tableBits s).length≤tableBound n := by
  have hl : (tableWords s).length=n := by simp [tableWords]
  have hs:=sum_length_le (tableWords s) (rowBound n) (by
    intro w hw
    obtain ⟨row,hr,rfl⟩:=List.mem_map.mp hw
    obtain ⟨i,hi,he⟩:=List.getElem_of_mem hr
    have hn:i<n:=by simpa using hi
    have he':s.rows[i]=row:=by simpa using he
    rw [←he']
    exact safe_row_bound h ⟨i,hn⟩)
  simp only [tableBits,encodeBitList_length,hl]
  rw [hl] at hs
  unfold tableBound
  nlinarith
lemma safe_sizes_bound {n : ℕ} {s : NumericStateModel.State n} (h : Safe s) :
    (sizeBits s).length≤sizesBound n := by
  have hl : (sizeWords s).length=n := by simp [sizeWords]
  have hs:=sum_length_le (sizeWords s) n (by
    intro w hw
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hw
    obtain ⟨i,hi,he⟩:=List.getElem_of_mem hz
    have hn:i<n:=by simpa using hi
    have he':s.sizes[i]=z:=by simpa using he
    simp only [List.length_replicate]
    rw [←he']
    exact h.size_bound ⟨i,hn⟩)
  simp only [sizeBits,encodeBitList_length,hl]
  rw [hl] at hs
  unfold sizesBound
  nlinarith
lemma live_length {n : ℕ} (alive : Vector Bool n) : (PairCheck.liveBits alive).length=4*n := by
  simp [PairCheck.liveBits,PairCheck.liveWords,encodeBitList_length,List.map_map,Function.comp_def]
  omega
lemma tableWords_set {n : ℕ} (s : NumericStateModel.State n) (v : Fin n) (row : List ℕ) :
    tableWords {s with rows:=s.rows.set v.val row}=(tableWords s).set v.val (rowBits row) := by
  simp [tableWords,Vector.toList_set,List.map_set]
lemma sizeWords_set {n : ℕ} (s : NumericStateModel.State n) (v : Fin n) (size : ℕ) :
    sizeWords {s with sizes:=s.sizes.set v.val size}=(sizeWords s).set v.val (List.replicate size true) := by
  simp [sizeWords,Vector.toList_set,List.map_set]
end HiddenCircuits.DH.Runtime.NumericEncoding
