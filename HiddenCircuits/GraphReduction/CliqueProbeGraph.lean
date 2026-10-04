import HiddenCircuits.GraphReduction.ColoredPerfectPartner
import HiddenCircuits.GraphReduction.ProbeGraph

/-! Actual simple unweighted clique-probe graphs with possibly overlapping neighborhoods. -/
namespace HiddenCircuits.GraphReduction
variable {V I : Type*}

/-- Probe classes are cliques, attached to their prescribed original neighborhoods;
different probe classes have no edges between them. -/
def cliqueProbeGraph (G : SimpleGraph V) (A : I → V → Prop) (s : ℕ) :
    SimpleGraph (V ⊕ (I × Fin s)) where
  Adj
    | .inl v, .inl w => G.Adj v w
    | .inl v, .inr (i,_) => A i v
    | .inr (i,_), .inl v => A i v
    | .inr (i,j), .inr (k,l) => i=k ∧ j≠l
  symm := by
    intro x y
    rcases x with x|⟨i,j⟩ <;> rcases y with y|⟨k,l⟩
    · exact G.adj_symm
    · exact id
    · exact id
    · exact fun h => ⟨h.1.symm,h.2.symm⟩
  loopless := ⟨by intro v; rcases v with v|⟨i,j⟩; exact G.loopless.irrefl v; simp⟩

 theorem cliqueProbeGraph_card [Fintype V] [Fintype I] (s : ℕ) :
    Fintype.card (V ⊕ (I × Fin s)) = Fintype.card V + Fintype.card I*s := by simp

/-- The unique probe label actually used by an original vertex. -/
def cliqueAssignment {G : SimpleGraph V} {A : I → V → Prop} {s : ℕ}
    (p : PerfectPartner (cliqueProbeGraph G A s)) (v : V) : Option I :=
  match p.val (.inl v) with
  | .inl _ => none
  | .inr (i,_) => some i

 theorem cliqueAssignment_preserved {G : SimpleGraph V} {A : I → V → Prop} {s : ℕ}
    (p : PerfectPartner (cliqueProbeGraph G A s)) (v) :
    extendColor (cliqueAssignment p) s (p.val v) = extendColor (cliqueAssignment p) s v := by
  have hi := p.property.1 v
  cases v with
  | inl v =>
    cases he : p.val (.inl v) with
    | inl w =>
      rw [he] at hi
      simp [extendColor,cliqueAssignment,he,hi]
    | inr w => rcases w with ⟨i,j⟩; simp [extendColor,cliqueAssignment,he]
  | inr v =>
    rcases v with ⟨i,j⟩
    cases he : p.val (.inr (i,j)) with
    | inl w =>
      rw [he] at hi
      simp [extendColor,cliqueAssignment,he,hi]
    | inr w =>
      rcases w with ⟨k,l⟩
      have ha := p.property.2 (.inr (i,j))
      rw [he] at ha
      change i=k ∧ j≠l at ha
      simp [extendColor,he,ha.1]

 theorem cliqueAssignment_allowed {G : SimpleGraph V} {A : I → V → Prop} {s : ℕ}
    (p : PerfectPartner (cliqueProbeGraph G A s)) (v : V) (i : I)
    (h : cliqueAssignment p v=some i) : A i v := by
  have ha := p.property.2 (.inl v)
  unfold cliqueAssignment at h
  split at h
  · contradiction
  · simp only [Option.some.injEq] at h
    subst i
    simp_all only [cliqueProbeGraph]

end HiddenCircuits.GraphReduction
