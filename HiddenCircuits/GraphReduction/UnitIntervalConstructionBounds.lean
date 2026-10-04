import HiddenCircuits.GraphReduction.UnitIntervalOrderConstruction

/-! Intermediate coordinate magnitudes for the executable midpoint construction.
This is arithmetic control for a future bit-machine refinement, not an assumed
running-time certificate. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalOrder

def lowerBounds {n : ℕ} (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj] (f : Fin n → ℚ) : Finset ℚ :=
  insert 0 (Finset.univ.image f ∪
    (Finset.univ.filter (fun i : Fin n => ¬G.Adj i.castSucc (Fin.last n))).image (fun i => f i+1))
def upperBounds {n : ℕ} (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj] (f : Fin n → ℚ) : Finset ℚ :=
  (Finset.univ.filter (fun i : Fin n => G.Adj i.castSucc (Fin.last n))).image (fun i => f i+1)
lemma lowerBounds_nonempty {n : ℕ} (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj] (f : Fin n → ℚ) :
    (lowerBounds G f).Nonempty := ⟨0,by simp [lowerBounds]⟩

lemma buildModel_castSucc {n : ℕ} (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj]
    (h : Umbrella G) (i : Fin n) :
    (buildModel (n+1) G h).left i.castSucc =
      (buildModel n (G.comap Fin.castSucc) (fun i j k hij hjk he => h i.castSucc j.castSucc k.castSucc hij hjk he)).left i := by
  simp only [buildModel,Nat.recAux,Fin.snoc_castSucc]

lemma buildModel_last {n : ℕ} (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj]
    (h : Umbrella G) :
    (buildModel (n+1) G h).left (Fin.last n) =
      let f := (buildModel n (G.comap Fin.castSucc) (fun i j k hij hjk he => h i.castSucc j.castSucc k.castSucc hij hjk he)).left
      separator (lowerBounds G f) (upperBounds G f) (lowerBounds_nonempty G f) := by
  simp only [buildModel,Nat.recAux,Fin.snoc_last,lowerBounds,upperBounds]

lemma separator_upper {A B : Finset ℚ} (hA : A.Nonempty) {L : ℚ}
    (ha : ∀ a ∈ A, a ≤ L) (hb : ∀ b ∈ B, b ≤ L) : separator A B hA ≤ L+1 := by
  unfold separator
  split_ifs with hB
  · have h1 := ha _ (A.max'_mem hA)
    have h2 := hb _ (B.min'_mem hB)
    linarith
  · have h1 := ha _ (A.max'_mem hA); linarith

/-- Before grid compression, left endpoints grow at most linearly in n. -/
theorem buildModel_left_bound : ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : Umbrella G) (v : Fin n), (buildModel n G h).left v ≤ 2*n := by
  intro n
  induction n with
  | zero => intro G _ h v; exact Fin.elim0 v
  | succ n ih =>
    intro G _ h v
    let H := G.comap Fin.castSucc
    have hH : Umbrella H := fun i j k hij hjk he => h i.castSucc j.castSucc k.castSucc hij hjk he
    have hiBound := ih H hH
    refine Fin.lastCases ?_ (fun i => ?_) v
    · rw [buildModel_last]
      dsimp only
      apply (separator_upper (L:=2*(n:ℚ)+1) (lowerBounds_nonempty _ _) ?_ ?_).trans (by push_cast; linarith)
      · intro a ha
        simp only [lowerBounds,Finset.mem_insert,Finset.mem_union,Finset.mem_image,
          Finset.mem_univ,true_and,Finset.mem_filter] at ha
        rcases ha with rfl|⟨i,rfl⟩|⟨i,_,rfl⟩
        · positivity
        · have hh := hiBound i; linarith
        · have hh := hiBound i; linarith
      · intro b hb
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
        have hh := hiBound i; linarith
    · rw [buildModel_castSucc]
      have hh := hiBound i
      push_cast
      linarith

end HiddenCircuits.GraphReduction.UnitIntervalOrder
