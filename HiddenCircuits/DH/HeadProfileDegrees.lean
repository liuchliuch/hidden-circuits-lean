import HiddenCircuits.DH.HeadProfileCounts

/-! One original-row scan supplies all degrees needed by complementary profile keys. -/
namespace HiddenCircuits.DH.HeadProfileCounts
open scoped BigOperators
open LinearBuckets

def degreeFrom {n : ℕ} (rows : Vector (List (Fin n)) n) :
    List (Fin n) → Vector ℕ n → Vector ℕ n × ℕ
  | [],counts => (counts,0)
  | i::is,counts =>
      let l := measureLength rows[i.val]
      let q := degreeFrom rows is (counts.set i.val l.1)
      (q.1,q.2+l.2+3)

lemma degreeFrom_get {n : ℕ} (rows : Vector (List (Fin n)) n)
    (is : List (Fin n)) (counts : Vector ℕ n) (i : Fin n) :
    (degreeFrom rows is counts).1[i.val] = if i∈is then rows[i.val].length else counts[i.val] := by
  induction is generalizing counts with
  | nil => simp [degreeFrom]
  | cons j js ih =>
    rw [degreeFrom,ih]
    by_cases hi : i∈js
    · simp [hi]
    · by_cases hij : i=j
      · subst j; simp [hi]
      · have hji : j.val≠i.val := fun he=>hij (Fin.ext he).symm
        simp [hi,hij,hji]

lemma degreeFrom_accesses {n : ℕ} (rows : Vector (List (Fin n)) n)
    (is : List (Fin n)) (counts : Vector ℕ n) :
    (degreeFrom rows is counts).2 = (is.map (fun i=>rows[i.val].length)).sum+3*is.length := by
  induction is generalizing counts <;> simp [degreeFrom, *] <;> omega

/-- Both counter-array allocation and generation of the one index traversal are charged. -/
def degreeCounts {n : ℕ} (rows : Vector (List (Fin n)) n) : Result n :=
  let q := degreeFrom rows (List.finRange n) (Vector.replicate n 0)
  ⟨q.1,q.2+2*n⟩

@[simp] theorem degreeCounts_value {n : ℕ} (rows : Vector (List (Fin n)) n) (i : Fin n) :
    (degreeCounts rows).counts[i.val] = rows[i.val].length := by simp [degreeCounts,degreeFrom_get]

/-- Exactly one list-cell visit per input incidence, with a constant per vertex. -/
theorem degreeCounts_accesses {n : ℕ} (rows : Vector (List (Fin n)) n) :
    (degreeCounts rows).accesses = (∑ i : Fin n,rows[i.val].length)+5*n := by
  simp [degreeCounts,degreeFrom_accesses,←List.ofFn_eq_map,List.sum_ofFn]
  omega

/-- Degree counts are literal graph degrees, derived from ordinary duplicate-free rows. -/
theorem degreeCounts_get {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ i : Fin n,(rows[i.val]).Nodup) (i : Fin n) :
    (degreeCounts rows).counts[i.val] = G.degree i := by
  rw [degreeCounts_value,←List.toFinset_card_of_nodup (hn i)]
  have he : (rows[i.val]).toFinset=G.neighborFinset i := by
    ext j
    simp only [List.mem_toFinset,SimpleGraph.mem_neighborFinset]
    exact hr i j
  rw [he]
  rfl

/-- Both common-neighbor and degree vectors use only the original sparse input. -/
structure ProfileData (n : ℕ) where
  common : Vector ℕ n
  degree : Vector ℕ n
  accesses : ℕ

def profileData {n : ℕ} (rows : Vector (List (Fin n)) n) (heads : List (Fin n × Fin n)) : ProfileData n :=
  let c := commonCounts rows heads
  let d := degreeCounts rows
  ⟨c.counts,d.counts,c.accesses+d.accesses⟩

theorem profileData_accesses {n : ℕ} (rows : Vector (List (Fin n)) n)
    (heads : List (Fin n × Fin n)) (hn : (heads.map Prod.snd).Nodup) :
    (profileData rows heads).accesses ≤
      30*(∑ i : Fin n,rows[i.val].length)+12*n+2*heads.length := by
  have hc := commonCounts_accesses rows heads hn
  have hd := degreeCounts_accesses rows
  dsimp only [profileData]
  omega

end HiddenCircuits.DH.HeadProfileCounts
