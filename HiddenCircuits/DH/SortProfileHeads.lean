import HiddenCircuits.DH.NonpreferredHeads
import HiddenCircuits.DH.ProfileCardinality

/-! One global stable size sort followed by parent bucketing orders all profile
families. A vertex is a head at most once per sweep, so its key is stored once. -/
namespace HiddenCircuits.DH.SortProfileHeads
open LinearBuckets SliceHeads
variable {n : ℕ}

/-- Read each head's bounded cardinal key once. -/
def decorate (keys : Vector (Fin (n+1)) n) :
    List (Fin n × Fin n) → List (Fin (n+1) × (Fin n × Fin n)) × ℕ
  | [] => ([],0)
  | p::ps => let q := decorate keys ps; ((keys[p.2.val],p)::q.1,q.2+3)

@[simp] lemma decorate_values (keys : Vector (Fin (n+1)) n) (entries : List (Fin n × Fin n)) :
    (decorate keys entries).1 = entries.map (fun p => (keys[p.2.val],p)) := by
  induction entries <;> simp [decorate, *]

@[simp] lemma decorate_accesses (keys : Vector (Fin (n+1)) n) (entries : List (Fin n × Fin n)) :
    (decorate keys entries).2 = 3*entries.length := by
  induction entries <;> simp [decorate, *] <;> omega

/-- Remove tags once after the stable size ordering. -/
def project : List (Fin (n+1) × (Fin n × Fin n)) → List (Fin n × Fin n) × ℕ
  | [] => ([],0)
  | p::ps => let q := project ps; (p.2::q.1,q.2+2)

@[simp] lemma project_values (xs : List (Fin (n+1) × (Fin n × Fin n))) :
    (project xs).1 = xs.map Prod.snd := by induction xs <;> simp [project, *]

@[simp] lemma project_accesses (xs : List (Fin (n+1) × (Fin n × Fin n))) :
    (project xs).2 = 2*xs.length := by induction xs <;> simp [project, *] <;> omega

/-- No second comparison/radix sort is required: stable parent bucketing preserves
nonincreasing global size order within every resulting parent bucket. -/
def run (keys : Vector (Fin (n+1)) n) (entries : List (Fin n × Fin n)) : Children n :=
  let d := decorate keys entries
  let s := sort Prod.fst d.1
  let p := project s.1
  let g := NonpreferredHeads.group p.1
  ⟨g.rows,d.2+s.2+p.2+g.accesses⟩

def orderedEntries (keys : Vector (Fin (n+1)) n) (entries : List (Fin n × Fin n)) :
    List (Fin n × Fin n) := (project (sort Prod.fst (decorate keys entries).1).1).1

lemma orderedEntries_perm (keys : Vector (Fin (n+1)) n) (entries : List (Fin n × Fin n)) :
    (orderedEntries keys entries).Perm entries := by
  have h := (sort_perm Prod.fst (decorate keys entries).1).map Prod.snd
  simpa [orderedEntries,List.map_map,Function.comp_def] using h

lemma orderedEntries_descending (keys : Vector (Fin (n+1)) n) (entries : List (Fin n × Fin n)) :
    (orderedEntries keys entries).Pairwise (fun p q => keys[q.2.val]≤keys[p.2.val]) := by
  have h := sort_descending Prod.fst (decorate keys entries).1
  rw [orderedEntries,project_values,List.pairwise_map]
  apply h.imp_of_mem
  intro p q hp hq hpq
  have hp' := (sort_perm Prod.fst (decorate keys entries).1).mem_iff.mp hp
  have hq' := (sort_perm Prod.fst (decorate keys entries).1).mem_iff.mp hq
  simp only [decorate_values,List.mem_map] at hp' hq'
  obtain ⟨a,ha,rfl⟩ := hp'
  obtain ⟨b,hb,rfl⟩ := hq'
  exact hpq

lemma run_get (keys : Vector (Fin (n+1)) n) (entries : List (Fin n × Fin n)) (r : Fin n) :
    (run keys entries).rows[r.val] =
      ((orderedEntries keys entries).filter (fun p => p.1==r)).map Prod.snd := by
  exact NonpreferredHeads.group_get _ r

/-- Each output family contains exactly the input head occurrences for its parent. -/
theorem run_row_perm (keys : Vector (Fin (n+1)) n) (entries : List (Fin n × Fin n)) (r : Fin n) :
    ((run keys entries).rows[r.val]).Perm ((entries.filter (fun p => p.1==r)).map Prod.snd) := by
  rw [run_get]
  exact ((orderedEntries_perm keys entries).filter _).map _

theorem run_row_descending (keys : Vector (Fin (n+1)) n) (entries : List (Fin n × Fin n)) (r : Fin n) :
    ((run keys entries).rows[r.val]).Pairwise (fun x y => keys[y.val]≤keys[x.val]) := by
  rw [run_get,List.pairwise_map]
  exact (orderedEntries_descending keys entries).filter _

/-- Decoration, stable size sorting, projection, parent grouping, and all bucket
initializations are charged by the actual loops. -/
theorem run_accesses (keys : Vector (Fin (n+1)) n) (entries : List (Fin n × Fin n)) :
    (run keys entries).accesses=15*entries.length+9*n+4 := by
  have hlen := (sort_perm Prod.fst (decorate keys entries).1).length_eq
  simp only [decorate_values,List.length_map] at hlen
  simp only [run,decorate_accesses,sort_accesses,project_accesses,NonpreferredHeads.group_accesses,
    decorate_values,List.length_map,project_values]
  omega

/-- The size pass supplies strict nested-profile order, once the frontend has
identified each class once. The required set inclusion is proved from graph
laminarity, not stored as a sort key or accepted as a runtime certificate. -/
theorem strict_profile_order (G : SimpleGraph (Fin n)) (hG : P4Free G)
    (keys : Vector (Fin (n+1)) n) (entries : List (Fin n × Fin n)) (r : Fin n)
    (hkey : ∀x∈(run keys entries).rows[r.val],
      (keys[x.val]).val=(pivotProfile G r x).ncard)
    (hheads : ∀x∈(run keys entries).rows[r.val], x∈nonneighbors G r)
    (hdistinct : ((run keys entries).rows[r.val]).Pairwise
      (fun x y => pivotProfile G r x ≠ pivotProfile G r y)) :
    ((run keys entries).rows[r.val]).Pairwise
      (fun x y => pivotProfile G r y ⊂ pivotProfile G r x) := by
  apply ((run_row_descending keys entries r).and hdistinct).imp_of_mem
  intro x y hx hy h
  apply hG.pivotProfile_strict_of_card (hheads x hx) (hheads y hy) _ h.2
  have hk : (keys[y.val]).val≤(keys[x.val]).val := h.1
  rwa [hkey y hy,hkey x hx] at hk

end HiddenCircuits.DH.SortProfileHeads
