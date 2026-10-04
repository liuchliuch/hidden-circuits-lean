import HiddenCircuits.DH.ComponentForestLayers

namespace HiddenCircuits.DH.ComponentForest
open SimpleGraph BreadthFirst
attribute [local instance] Classical.propDecidable

structure MarkInvariant {n : ℕ} (G : SimpleGraph (Fin n))
    (marks : Vector (Option ℕ) n) (owners : Vector (Fin n) n) : Prop where
  closed : ∀u v, marks[u.val]≠none → G.Reachable u v → marks[v.val]≠none
  depth : ∀v, marks[v.val]≠none → marks[v.val]=some (G.dist owners[v.val] v) ∧ G.Reachable owners[v.val] v
  owner : ∀u v, marks[u.val]≠none → marks[v.val]≠none → G.Reachable u v → owners[u.val]=owners[v.val]

lemma MarkInvariant.unmarked_component {n : ℕ} {G : SimpleGraph (Fin n)}
    {marks : Vector (Option ℕ) n} {owners : Vector (Fin n) n} (h : MarkInvariant G marks owners)
    (r : Fin n) (hr : marks[r.val]=none) : ∀v, G.Reachable r v → marks[v.val]=none := by
  intro v hv
  by_contra hn
  exact h.closed v r hn hv.symm hr

def Extends {n : ℕ} (before after : Vector (Option ℕ) n) (oldOwners newOwners : Vector (Fin n) n) : Prop :=
  ∀v : Fin n, before[v.val]≠none → after[v.val]=before[v.val] ∧ newOwners[v.val]=oldOwners[v.val]

lemma Extends.refl {n : ℕ} (marks : Vector (Option ℕ) n) (owners : Vector (Fin n) n) :
    Extends marks marks owners owners := fun _ _ => ⟨rfl,rfl⟩
lemma Extends.trans {n : ℕ} {a b c : Vector (Option ℕ) n} {x y z : Vector (Fin n) n}
    (h1 : Extends a b x y) (h2 : Extends b c y z) : Extends a c x z := by
  intro v hv
  obtain ⟨hm,ho⟩ := h1 v hv
  obtain ⟨hm',ho'⟩ := h2 v (by rwa [hm])
  exact ⟨hm'.trans hm,ho'.trans ho⟩
lemma Extends.marked {n : ℕ} {a b : Vector (Option ℕ) n} {x y : Vector (Fin n) n}
    (h : Extends a b x y) (v : Fin n) (hv : a[v.val]≠none) : b[v.val]≠none := by rw [(h v hv).1];exact hv

lemma start_extends {n : ℕ} {G : SimpleGraph (Fin n)}
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (r : Fin n) (marks : Vector (Option ℕ) n) (owners : Vector (Fin n) n)
    (h : MarkInvariant G marks owners) (hn : marks[r.val]=none) :
    Extends marks (start rows r marks).marks owners (assign r (start rows r marks).members owners) := by
  have hb := h.unmarked_component r hn
  have hs := start_spec rows hr r marks hb
  intro v hv
  have hR : ¬G.Reachable r v := fun hR => hv (hb v hR)
  exact ⟨by rw [hs.1];simp [hR],by rw [assign_get];simp [hs.2.1 v,hR]⟩

lemma start_invariant {n : ℕ} {G : SimpleGraph (Fin n)}
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (r : Fin n) (marks : Vector (Option ℕ) n) (owners : Vector (Fin n) n)
    (h : MarkInvariant G marks owners) (hn : marks[r.val]=none) :
    MarkInvariant G (start rows r marks).marks (assign r (start rows r marks).members owners) := by
  have hb := h.unmarked_component r hn
  have hs := start_spec rows hr r marks hb
  have hm (v : Fin n) : (start rows r marks).marks[v.val] =
      if G.Reachable r v then some (G.dist r v) else marks[v.val] := hs.1 v
  have ho (v : Fin n) : (assign r (start rows r marks).members owners)[v.val] =
      if G.Reachable r v then r else owners[v.val] := by simp only [assign_get,hs.2.1]
  refine ⟨?_,?_,?_⟩
  · intro u v hu huv
    by_cases hv : G.Reachable r v
    · simp [hm,hv]
    · have hnu : ¬G.Reachable r u := fun hru => hv (hru.trans huv)
      rw [hm,if_neg hnu] at hu
      simpa [hm,hv] using h.closed u v hu huv
  · intro v hv
    by_cases hR : G.Reachable r v
    · simp [hm,ho,hR]
    · have hv' : marks[v.val]≠none := by simpa [hm,hR] using hv
      simpa [hm,ho,hR] using h.depth v hv'
  · intro u v hu hv huv
    by_cases hR : G.Reachable r u
    · have hvR := hR.trans huv
      simp [ho,hR,hvR]
    · have hvR : ¬G.Reachable r v := fun hvR => hR (hvR.trans huv.symm)
      have hu' : marks[u.val]≠none := by simpa [hm,hR] using hu
      have hv' : marks[v.val]≠none := by simpa [hm,hvR] using hv
      simpa [ho,hR,hvR] using h.owner u v hu' hv' huv

lemma start_accesses {n : ℕ} (rows : Vector (List (Fin n)) n) (r : Fin n) (marks : Vector (Option ℕ) n) :
    (start rows r marks).accesses ≤ 5*frontierWeight rows (start rows r marks).members+3 := by
  have h := explore_accesses rows n 0 [r] (marks.set r.val (some 0))
  simp only [start];omega
lemma start_allocations {n : ℕ} (rows : Vector (List (Fin n)) n) (r : Fin n) (marks : Vector (Option ℕ) n) :
    (start rows r marks).allocations ≤ (start rows r marks).accesses := by
  have h := explore_allocations rows n 0 [r] (marks.set r.val (some 0))
  simp only [start];omega

lemma empty_invariant {n : ℕ} (G : SimpleGraph (Fin n)) :
    MarkInvariant G (Vector.replicate n none) (Vector.ofFn id) := by
  refine ⟨?_,?_,?_⟩ <;> simp

end HiddenCircuits.DH.ComponentForest
