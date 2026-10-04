import HiddenCircuits.GraphReduction.UnitCoordinateExtractionWitness
import HiddenCircuits.GraphReduction.UnitCoordinateExtractionStabilization

/-! Correctness of the literal bounded coordinate relaxation on original labels.
The feasible grid vector is derived in the proof from an exhaustive umbrella
list, never supplied to the evaluator. -/
namespace HiddenCircuits.GraphReduction.UnitCoordinateExtraction
open UnitIntervalOrder

lemma forall_pairs_iff_pairwise {n : ℕ} (R : Fin n → Fin n → Prop)
    (ls : List (Fin n)) :
    (∀ p ∈ pairs ls, R p.1 p.2) ↔ ls.Pairwise R := by
  induction ls with
  | nil => simp [pairs]
  | cons u us ih =>
    simp only [pairs, List.forall_mem_append, List.forall_mem_map, List.pairwise_cons]
    exact and_congr Iff.rfl ih

lemma pairs_ne {n : ℕ} (ls : List (Fin n)) (hn : ls.Nodup)
    (p : Fin n × Fin n) (hp : p ∈ pairs ls) : p.1 ≠ p.2 :=
  (forall_pairs_iff_pairwise (fun u v => u ≠ v) ls).mpr hn p hp

lemma pairs_orientation {n : ℕ} (ls : List (Fin n)) (u v : Fin n)
    (hu : u ∈ ls) (hv : v ∈ ls) (hne : u ≠ v) :
    (u,v) ∈ pairs ls ∨ (v,u) ∈ pairs ls := by
  induction ls with
  | nil => simp at hu
  | cons w ws ih =>
    rcases List.mem_cons.mp hu with rfl | htu
    · have hv : v ∈ ws := (List.mem_cons.mp hv).resolve_left (Ne.symm hne)
      exact Or.inl (by simp [pairs, hv])
    · rcases List.mem_cons.mp hv with rfl | htv
      · exact Or.inr (by simp [pairs, htu])
      · rcases ih htu htv with hh | hh
        · exact Or.inl (by simp [pairs, hh])
        · exact Or.inr (by simp [pairs, hh])

/-- The witness is internally constructed from the ordered graph, then put back
in the original vertex-label order. -/
theorem list_grid_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ls : List (Fin n)) (hn : ls.Nodup) (hc : ∀ v, v ∈ ls)
    (hu : ListUmbrella G ls) :
    ∃ z : Coordinates n,
      (∀ p ∈ pairs ls, pair (max 1 n) (decide (G.Adj p.1 p.2)) p.1 p.2 z = z) ∧
      (∀ v, z v + max 1 n < 2*n*max 1 n) := by
  let e := hn.getEquivOfForallMemList ls hc
  have he : ∀ i, e i = ls.get i := fun _ => rfl
  have hlen : ls.length = n := by
    simpa using Fintype.card_congr e
  obtain ⟨y,hm,hb,ha⟩ := ordered_grid_witness (G.comap ls.get) hu
  let z : Coordinates n := fun v => y (e.symm v)
  have hzget : ∀ i, z (ls.get i) = y i := by
    intro i
    change y (e.symm (ls.get i)) = y i
    rw [←he, e.symm_apply_apply]
  have hmono : ls.Pairwise (fun u v => z u ≤ z v) := by
    apply List.pairwise_iff_get.mpr
    intro i j hij
    rw [hzget, hzget]
    exact hm (le_of_lt hij)
  have hadj : ∀ u v, G.Adj u v ↔ u ≠ v ∧ z u ≤ z v+max 1 n ∧ z v ≤ z u+max 1 n := by
    intro u v
    have heu : ls.get (e.symm u) = u := by rw [←he]; exact e.apply_symm_apply u
    have hev : ls.get (e.symm v) = v := by rw [←he]; exact e.apply_symm_apply v
    simpa only [SimpleGraph.comap_adj, heu, hev, ne_eq, e.symm.injective.eq_iff, hlen]
      using ha (e.symm u) (e.symm v)
  refine ⟨z, ?_, ?_⟩
  · intro p hp
    apply (pair_fixed_iff (max 1 n) _ _ _ (pairs_ne ls hn p hp) z).mpr
    have hle := (forall_pairs_iff_pairwise (fun u v => z u ≤ z v) ls).mpr hmono p hp
    refine ⟨hle, ?_⟩
    by_cases hedge : G.Adj p.1 p.2
    · simpa [hedge] using ((hadj p.1 p.2).mp hedge).2.2
    · have hnot : ¬z p.2 ≤ z p.1+max 1 n := by
        intro hh
        exact hedge ((hadj p.1 p.2).mpr ⟨pairs_ne ls hn p hp, by omega, hh⟩)
      simpa [hedge] using Nat.lt_of_not_ge hnot
  · intro v
    simpa only [hlen] using hb (e.symm v)

lemma pair_fixed_adjacency {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (u v : Fin n) (hne : u ≠ v) (x : Coordinates n)
    (h : pair D (decide (G.Adj u v)) u v x = x) :
    G.Adj u v ↔ u ≠ v ∧ x u ≤ x v+D ∧ x v ≤ x u+D := by
  have hh := (pair_fixed_iff D _ u v hne x).mp h
  by_cases he : G.Adj u v
  · simp only [he, decide_true, ite_true] at hh
    exact ⟨fun _ => ⟨hne, by omega, hh.2⟩, fun _ => he⟩
  · simp only [he, decide_false, Bool.false_eq_true, ite_false] at hh
    constructor
    · exact fun ha => (he ha).elim
    · rintro ⟨_,_,hbad⟩
      omega

/-- A fixed scan over an exhaustive list yields exact closed interval adjacency. -/
theorem scan_fixed_adjacency {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (ls : List (Fin n)) (hc : ∀ v, v ∈ ls) (x : Coordinates n)
    (hf : scan D (fun u v => decide (G.Adj u v)) ls x = x) :
    ∀ u v, G.Adj u v ↔ u ≠ v ∧ x u ≤ x v+D ∧ x v ≤ x u+D := by
  have hp := (scan_fixed_iff D (fun u v => decide (G.Adj u v)) ls x).mp hf
  intro u v
  by_cases hne : u = v
  · subst v; simp
  · rcases pairs_orientation ls u v (hc u) (hc v) hne with h | h
    · exact pair_fixed_adjacency G D u v hne x (hp (u,v) h)
    · have hh := pair_fixed_adjacency G D v u (Ne.symm hne) x (hp (v,u) h)
      constructor
      · intro ha
        obtain ⟨_,h1,h2⟩ := hh.mp ha.symm
        exact ⟨hne,h2,h1⟩
      · rintro ⟨_,h1,h2⟩
        exact (hh.mpr ⟨(Ne.symm hne),h2,h1⟩).symm

/-- A concrete polynomial clock, uniform in the graph and its components. -/
def fuel (n : ℕ) : ℕ := 2*(n+1)^3+1

lemma witness_potential_lt_fuel (n : ℕ) : n*(2*n*max 1 n) < fuel n := by
  have hm : max 1 n ≤ n+1 := max_le (by omega) (by omega)
  have hh : n*(2*n*max 1 n) ≤ n*(2*n*(n+1)) := by gcongr
  unfold fuel
  nlinarith [Nat.zero_le (n^2), Nat.zero_le (n^3)]

/-- The actual runtime output vector, initialized at zero. -/
def coordinates {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ls : List (Fin n)) : Coordinates n :=
  run (max 1 n) (fun u v => decide (G.Adj u v)) ls (fuel n) (fun _ => 0)

theorem coordinates_fixed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ls : List (Fin n)) (hn : ls.Nodup) (hc : ∀ v, v ∈ ls)
    (hu : ListUmbrella G ls) :
    scan (max 1 n) (fun u v => decide (G.Adj u v)) ls (coordinates G ls) = coordinates G ls := by
  obtain ⟨z,hz,hb⟩ := list_grid_witness G ls hn hc hu
  exact run_fixed_of_witness (max 1 n) _ ls z (2*n*max 1 n) (fuel n) hz
    (fun i => by have := hb i; omega) (witness_potential_lt_fuel n)

/-- The bounded relaxation computes a quadratic grid representation on original
labels, for empty and disconnected graphs as well as connected graphs. -/
theorem coordinates_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ls : List (Fin n)) (hn : ls.Nodup) (hc : ∀ v, v ∈ ls)
    (hu : ListUmbrella G ls) :
    (∀ v, coordinates G ls v + max 1 n < 2*n*max 1 n) ∧
    (∀ u v, G.Adj u v ↔ u ≠ v ∧ coordinates G ls u ≤ coordinates G ls v+max 1 n ∧
      coordinates G ls v ≤ coordinates G ls u+max 1 n) := by
  obtain ⟨z,hz,hb⟩ := list_grid_witness G ls hn hc hu
  refine ⟨?_, scan_fixed_adjacency G (max 1 n) ls hc (coordinates G ls)
    (coordinates_fixed G ls hn hc hu)⟩
  intro v
  have hh := run_le_witness (max 1 n) (fun u v => decide (G.Adj u v)) ls (fuel n)
    (fun _ => 0) z (fun _ => Nat.zero_le _) hz v
  change coordinates G ls v ≤ z v at hh
  have := hb v
  omega

end HiddenCircuits.GraphReduction.UnitCoordinateExtraction
