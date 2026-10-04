import HiddenCircuits.Approximation.SelfReduction.MatchingFibers
import HiddenCircuits.GraphIsomorphismCount

/-! Concrete bounded-depth matching-deletion instances, with explicit rejected
branches. Residual graphs are genuine induced subgraphs on retained vertices. -/
namespace HiddenCircuits.Approximation.SelfReduction
open scoped BigOperators

/-- `none` is a rejected branch at a specified remaining depth. Active states
store a literal retained vertex set of even cardinality. -/
def MatchingState (b : ℕ) := Σ d : ℕ, Option {U : Finset (Fin (b+1)) // U.card=2*d}

def matchingRank {b : ℕ} (s : MatchingState b) : ℕ := s.1

noncomputable def matchingStateCount {b : ℕ} (G : SimpleGraph (Fin (b+1))) (s : MatchingState b) : ℕ :=
  match s.2 with
  | none => 0
  | some U => perfectMatchingCount (G.induce (U.val : Set (Fin (b+1))))

/-- A real graph isomorphism identifies two successive restrictions with
one restriction to the twice-erased retained set. -/
def erasePairIso {V : Type*} [DecidableEq V] (G : SimpleGraph V) (U : Finset V) (u v : U) :
    ((G.induce (U : Set V)).induce (withoutPair u v)) ≃g
      G.induce ((U.erase u.val).erase v.val : Set V) where
  toFun x := ⟨x.val.val, by
    have hu : x.val.val ≠ u.val := fun h => x.property.1 (Subtype.ext h)
    have hv : x.val.val ≠ v.val := fun h => x.property.2 (Subtype.ext h)
    simpa only [Finset.mem_coe, Finset.mem_erase] using ⟨hv,hu,x.val.property⟩⟩
  invFun x := ⟨⟨x.val, (Finset.mem_erase.mp (Finset.mem_erase.mp x.property).2).2⟩, by
    have hx := Finset.mem_erase.mp x.property
    have hx' := Finset.mem_erase.mp hx.2
    constructor
    · intro h; exact hx'.1 (congrArg Subtype.val h)
    · intro h; exact hx.1 (congrArg Subtype.val h)⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  map_rel_iff' := by intro x y; rfl

theorem perfectMatchingCount_empty_vertices {V : Type*} [Fintype V] [IsEmpty V]
    (G : SimpleGraph V) : perfectMatchingCount G=1 := by
  classical
  rw [perfectMatchingCount_eq_partners]
  apply Fintype.card_eq_one_iff.mpr
  let p : PerfectPartner G := ⟨fun v => isEmptyElim v, by intro v; exact isEmptyElim v,
    by intro v; exact isEmptyElim v⟩
  refine ⟨p,?_⟩
  intro q
  apply Subtype.ext
  funext v
  exact isEmptyElim v

theorem matchingState_leaf {b : ℕ} (G : SimpleGraph (Fin (b+1))) (s : MatchingState b)
    (h : matchingRank s=0) : matchingStateCount G s ≤ 1 := by
  classical
  rcases s with ⟨d,U⟩
  change d=0 at h
  subst d
  cases U with
  | none => simp [matchingStateCount]
  | some U =>
    have he : U.val=∅ := Finset.card_eq_zero.mp (by simpa using U.property)
    simp only [matchingStateCount]
    have hi : IsEmpty {x // x ∈ U.val} := ⟨fun x => by simpa [he] using x.property⟩
    letI := hi
    exact le_of_eq (perfectMatchingCount_empty_vertices _)

end HiddenCircuits.Approximation.SelfReduction
