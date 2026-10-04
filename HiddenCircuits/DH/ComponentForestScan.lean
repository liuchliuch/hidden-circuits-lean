import HiddenCircuits.DH.ComponentForestInvariant

namespace HiddenCircuits.DH.ComponentForest
open SimpleGraph BreadthFirst
attribute [local instance] Classical.propDecidable

def members {n : ℕ} (q : Result n) : List (Fin n) := q.components.flatMap Prod.snd

structure ScanSpec {n : ℕ} (G : SimpleGraph (Fin n)) (before : Vector (Option ℕ) n)
    (oldOwners : Vector (Fin n) n) (roots : List (Fin n)) (q : Result n) : Prop where
  invariant : MarkInvariant G q.marks q.owners
  extension : Extends before q.marks oldOwners q.owners
  seen : ∀v∈roots, q.marks[v.val]≠none
  blocks : ∀b∈q.components, b.2.Nodup ∧ (∀v, v∈b.2 ↔ G.Reachable b.1 v) ∧ ∀v∈b.2, q.owners[v.val]=b.1
  novel : ∀v, v∈members q ↔ before[v.val]=none ∧ q.marks[v.val]≠none
  nodup : (members q).Nodup

/-- The actual finite outer root scan extracts disjoint, exact graph components,
with shared shortest-distance marks and direct root ownership. -/
theorem scan_spec {n : ℕ} {G : SimpleGraph (Fin n)}
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (roots : List (Fin n)) (marks : Vector (Option ℕ) n) (owners : Vector (Fin n) n)
    (h : MarkInvariant G marks owners) : ScanSpec G marks owners roots (scan rows roots marks owners) := by
  induction roots generalizing marks owners with
  | nil =>
    refine ⟨h,Extends.refl marks owners,by simp,by simp [scan],?_,by simp [members,scan]⟩
    intro v;simp [members,scan]
  | cons r rs ih =>
    by_cases hn : marks[r.val]=none
    · have hb := h.unmarked_component r hn
      have hc := start_spec rows hr r marks hb
      have he := start_extends rows hr r marks owners h hn
      have hi := start_invariant rows hr r marks owners h hn
      have ht := ih (start rows r marks).marks (assign r (start rows r marks).members owners) hi
      simp only [scan,hn,↓reduceIte]
      refine ⟨ht.invariant,he.trans ht.extension,?_,?_,?_,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · apply ht.extension.marked
          rw [hc.1]
          simp
        · exact ht.seen v hv
      · intro b hb'
        rcases List.mem_cons.mp hb' with rfl | hb'
        · refine ⟨hc.2.2.1,hc.2.1,?_⟩
          intro v hv
          have hvR := (hc.2.1 v).mp hv
          have hvm : (start rows r marks).marks[v.val]≠none := by rw [hc.1];simp [hvR]
          rw [(ht.extension v hvm).2,assign_get,if_pos hv]
        · exact ht.blocks b hb'
      · intro v
        change v∈(start rows r marks).members++members (scan rows rs (start rows r marks).marks
          (assign r (start rows r marks).members owners)) ↔ _
        rw [List.mem_append,hc.2.1,ht.novel]
        by_cases hvR : G.Reachable r v
        · have hbase := hb v hvR
          have hcm : (start rows r marks).marks[v.val]≠none := by rw [hc.1];simp [hvR]
          have hqm := ht.extension.marked v hcm
          simp [hvR,hbase,hqm]
        · rw [hc.1,if_neg hvR]
          simp [hvR]
      · change ((start rows r marks).members++members (scan rows rs (start rows r marks).marks
          (assign r (start rows r marks).members owners))).Nodup
        apply List.nodup_append.mpr
        refine ⟨hc.2.2.1,ht.nodup,?_⟩
        intro a ha b hb' hab
        subst b
        have hR := (hc.2.1 a).mp ha
        have hnone := ((ht.novel a).mp hb').1
        rw [hc.1,if_pos hR] at hnone
        contradiction
    · have ht := ih marks owners h
      simp only [scan,hn,↓reduceIte]
      refine ⟨ht.invariant,ht.extension,?_,ht.blocks,ht.novel,ht.nodup⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ht.extension.marked _ hn
      · exact ht.seen v hv

lemma frontierWeight_length {n : ℕ} (rows : Vector (List (Fin n)) n) (xs : List (Fin n)) :
    xs.length≤frontierWeight rows xs := by
  induction xs with
  | nil => simp [frontierWeight]
  | cons v vs ih => simp only [frontierWeight,List.map_cons,List.sum_cons,List.length_cons] at *;omega

/-- Shared marks ensure a global linear charge: no initialization or fuel charge
is multiplied by the number of connected components. -/
theorem scan_accesses {n : ℕ} (rows : Vector (List (Fin n)) n) (roots : List (Fin n))
    (marks : Vector (Option ℕ) n) (owners : Vector (Fin n) n) :
    (scan rows roots marks owners).accesses ≤
      7*frontierWeight rows (members (scan rows roots marks owners))+6*roots.length+1 := by
  induction roots generalizing marks owners with
  | nil => simp [scan,members,frontierWeight]
  | cons r rs ih =>
    by_cases hn : marks[r.val]=none
    · have ht := ih (start rows r marks).marks (assign r (start rows r marks).members owners)
      have hc := start_accesses rows r marks
      have hl := frontierWeight_length rows (start rows r marks).members
      simp only [scan,hn,↓reduceIte,members,List.flatMap_cons,frontierWeight_append,List.length_cons] at *
      omega
    · have ht := ih marks owners
      simp only [scan,hn,↓reduceIte,members,List.length_cons] at *
      omega

theorem scan_allocations {n : ℕ} (rows : Vector (List (Fin n)) n) (roots : List (Fin n))
    (marks : Vector (Option ℕ) n) (owners : Vector (Fin n) n) :
    (scan rows roots marks owners).allocations ≤ (scan rows roots marks owners).accesses := by
  induction roots generalizing marks owners with
  | nil => simp [scan]
  | cons r rs ih =>
    by_cases hn : marks[r.val]=none
    · have ht := ih (start rows r marks).marks (assign r (start rows r marks).members owners)
      have hc := start_allocations rows r marks
      simp only [scan,hn,↓reduceIte]
      omega
    · have ht := ih marks owners
      simp only [scan,hn,↓reduceIte]
      omega

end HiddenCircuits.DH.ComponentForest
