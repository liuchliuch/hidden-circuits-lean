import HiddenCircuits.GraphReduction.FiberBijection

/-! The simple unweighted bipartite probe graph of Section 9, with arbitrary,
possibly overlapping original neighborhoods. -/
namespace HiddenCircuits.GraphReduction
open SimpleGraph

variable {X Y I : Type*}

/-- Original vertices and separately labeled probes on one color class. -/
abbrev ProbePart (X I : Type*) (s : ℕ) := X ⊕ (I × Fin s)

/-- Exactly the original edges, two attachment blocks, and each complete probe pair.
The relation contains no edges between different probe pairs. -/
def probeRelation (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (s : ℕ) : ProbePart X I s → ProbePart Y I s → Prop
  | .inl x, .inl y => R x y
  | .inl x, .inr (i,_) => A i x
  | .inr (i,_), .inl y => B i y
  | .inr (i,_), .inr (j,_) => i=j

/-- An actual simple undirected graph, all of whose edges have weight one. -/
def probeGraph (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop)
    (s : ℕ) : SimpleGraph (ProbePart X I s ⊕ ProbePart Y I s) :=
  cutGraph (probeRelation R A B s)

 theorem probeGraph_card [Fintype X] [Fintype Y] [Fintype I] (s : ℕ) :
    Fintype.card (ProbePart X I s ⊕ ProbePart Y I s) =
      Fintype.card X + Fintype.card Y + 2 * Fintype.card I * s := by
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  ring

/-- Extend original color choices by the actual, fixed probe-pair label. -/
def extendColor (c : X → Option I) (s : ℕ) : ProbePart X I s → Option I
  | .inl x => c x
  | .inr (i,_) => some i

/-- The probe pair used by an original left vertex, or none for an original edge. -/
def leftAssignment {s : ℕ} (e : ProbePart X I s ≃ ProbePart Y I s) (x : X) : Option I :=
  match e (.inl x) with
  | .inl _ => none
  | .inr (i,_) => some i

/-- The probe pair used by an original right vertex, or none for an original edge. -/
def rightAssignment {s : ℕ} (e : ProbePart X I s ≃ ProbePart Y I s) (y : Y) : Option I :=
  match e.symm (.inl y) with
  | .inl _ => none
  | .inr (i,_) => some i

variable {R : X → Y → Prop} {A : I → X → Prop} {B : I → Y → Prop} {s : ℕ}

/-- Every actual matching edge remains within its uniquely determined color fiber. -/
theorem assignment_preserved (e : CutBijection (probeRelation R A B s)) (v) :
    extendColor (rightAssignment e.val) s (e.val v) =
      extendColor (leftAssignment e.val) s v := by
  cases v with
  | inl x =>
    cases he : e.val (.inl x) with
    | inl y =>
      have hi : e.val.symm (.inl y) = .inl x := (Equiv.apply_eq_iff_eq_symm_apply _).mp he |>.symm
      simp [extendColor,leftAssignment,rightAssignment,he,hi]
    | inr p => cases p; simp [extendColor,leftAssignment,he]
  | inr p =>
    obtain ⟨i,j⟩ := p
    cases he : e.val (.inr (i,j)) with
    | inl y =>
      have hi : e.val.symm (.inl y) = .inr (i,j) := (Equiv.apply_eq_iff_eq_symm_apply _).mp he |>.symm
      simp [extendColor,rightAssignment,he,hi]
    | inr q =>
      obtain ⟨k,l⟩ := q
      have h := e.property (.inr (i,j))
      rw [he] at h
      change i=k at h
      simp [extendColor,he,h]

 theorem leftAssignment_allowed (e : CutBijection (probeRelation R A B s))
    (x : X) (i : I) (h : leftAssignment e.val x = some i) : A i x := by
  have he := e.property (.inl x)
  unfold leftAssignment at h
  split at h
  · contradiction
  · simp only [Option.some.injEq] at h
    subst i
    simp_all only [probeRelation]

 theorem rightAssignment_allowed (e : CutBijection (probeRelation R A B s))
    (y : Y) (i : I) (h : rightAssignment e.val y = some i) : B i y := by
  have he := e.property (e.val.symm (.inl y))
  rw [Equiv.apply_symm_apply] at he
  unfold rightAssignment at h
  split at h
  · contradiction
  · simp only [Option.some.injEq] at h
    subst i
    simp_all only [probeRelation]

/-- Graph matchings are genuinely equivalent to the allowed augmented cut bijections. -/
noncomputable def probePerfectMatchingEquiv (R : X → Y → Prop)
    (A : I → X → Prop) (B : I → Y → Prop) (s : ℕ) :
    PerfectMatching (probeGraph R A B s) ≃ CutBijection (probeRelation R A B s) :=
  cutPerfectMatchingEquiv _

end HiddenCircuits.GraphReduction
