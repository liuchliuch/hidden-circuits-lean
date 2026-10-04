import HiddenCircuits.Complexity.GraphVerifier.Certificates

/-! Flat executable bit tests for the actual graph decoder and independent-set certificate. -/
namespace HiddenCircuits.Complexity.GraphVerifier

/-- Out-of-range access has a fixed default; the separate exact-length test excludes it. -/
def bitAt (xs : BitString) (i : ℕ) : Bool := xs[i]?.getD false

def flatEdge (n : ℕ) (xs : BitString) (i j : Fin n) : Bool :=
  bitAt xs (finProdFinEquiv (i,j)).val

/-- Exactly the three conditions checked by the actual adjacency-matrix decoder. -/
def ValidPayload (n : ℕ) (xs : BitString) : Prop :=
  xs.length=n*n ∧ (∀ i j, flatEdge n xs i j=flatEdge n xs j i) ∧
    (∀ i, flatEdge n xs i i=false)

instance (n : ℕ) (xs : BitString) : Decidable (ValidPayload n xs) :=
  inferInstanceAs (Decidable (_ ∧ (∀ i j : Fin n, _ = _) ∧ (∀ i : Fin n, _ = _)))

def payloadGraph (n : ℕ) (xs : BitString) (h : ValidPayload n xs) : MatrixGraph n :=
  ⟨flatEdge n xs,h.2.1,h.2.2⟩

 theorem bitAt_get (xs : BitString) (i : ℕ) (hi : i < xs.length) :
    bitAt xs i=xs.get ⟨i,hi⟩ := by simp [bitAt,List.getElem?_eq_getElem,hi]

 theorem ofBits_valid (n : ℕ) (xs : BitString) (h : ValidPayload n xs) :
    MatrixGraph.ofBits n xs=some (payloadGraph n xs h) := by
  unfold MatrixGraph.ofBits
  rw [dif_pos h.1]
  have he : (fun i j : Fin n => xs.get ⟨(finProdFinEquiv (i,j)).val,by simpa [h.1] using (finProdFinEquiv (i,j)).isLt⟩)=
      flatEdge n xs := by
    funext i j
    exact (bitAt_get xs _ _).symm
  have hs : ∀ i j : Fin n,
      xs.get ⟨(finProdFinEquiv (i,j)).val,by simpa [h.1] using (finProdFinEquiv (i,j)).isLt⟩=
      xs.get ⟨(finProdFinEquiv (j,i)).val,by simpa [h.1] using (finProdFinEquiv (j,i)).isLt⟩ := by
    change (∀ i j, (fun i j : Fin n => xs.get ⟨(finProdFinEquiv (i,j)).val,by simpa [h.1] using (finProdFinEquiv (i,j)).isLt⟩) i j =
      (fun i j : Fin n => xs.get ⟨(finProdFinEquiv (i,j)).val,by simpa [h.1] using (finProdFinEquiv (i,j)).isLt⟩) j i)
    rw [he]
    exact h.2.1
  have hl : ∀ i : Fin n,
      xs.get ⟨(finProdFinEquiv (i,i)).val,by simpa [h.1] using (finProdFinEquiv (i,i)).isLt⟩=false := by
    intro i
    rw [← bitAt_get]
    exact h.2.2 i
  rw [dif_pos hs,dif_pos hl]
  congr 1
  exact MatrixGraph.ext he

 theorem ofBits_some_edges (n : ℕ) (xs : BitString) (G : MatrixGraph n)
    (h : MatrixGraph.ofBits n xs=some G) : ValidPayload n xs ∧ G.edge=flatEdge n xs := by
  unfold MatrixGraph.ofBits at h
  split at h
  next hlen =>
    dsimp only at h
    split_ifs at h with hs hl
    · have he : (fun i j : Fin n => xs.get ⟨(finProdFinEquiv (i,j)).val,by simpa [hlen] using (finProdFinEquiv (i,j)).isLt⟩)=
          flatEdge n xs := by funext i j; exact (bitAt_get xs _ _).symm
      simp only [Option.some.injEq] at h
      subst G
      refine ⟨⟨hlen,?_,?_⟩,he⟩
      · intro i j
        have hh := hs i j
        simpa only [← bitAt_get] using hh
      · intro i
        have hh := hl i
        simpa only [← bitAt_get] using hh
    all_goals simp at h
  next hlen => simp at h

 theorem ofBits_isSome (n : ℕ) (xs : BitString) :
    (MatrixGraph.ofBits n xs).isSome=decide (ValidPayload n xs) := by
  cases he : MatrixGraph.ofBits n xs with
  | none =>
    have hn : ¬ValidPayload n xs := by intro h; rw [ofBits_valid n xs h] at he; cases he
    simp [hn]
  | some G =>
    have hh := (ofBits_some_edges n xs G he).1
    simp [hh]

/-- Direct selected-pair test on the flat payload, with no decoded graph or dependent choices. -/
def ValidSelectedPairs (n : ℕ) (payload witness : BitString) : Prop :=
  ∀ i j : Fin n, bitAt witness i.val=true → bitAt witness j.val=true → flatEdge n payload i j=false

instance (n : ℕ) (payload witness : BitString) : Decidable (ValidSelectedPairs n payload witness) :=
  inferInstanceAs (Decidable (∀ i j : Fin n, _ = _ → _ = _ → _ = _))

/-- Canonical padding is exactly an all-false scan of the unused suffix. -/
theorem zeroPadded_iff_drop (w : BitString) (n : ℕ) :
    ZeroPadded (fun i : Fin w.length => w.get i) n ↔ (w.drop n).all (fun b => !b)=true := by
  rw [List.all_eq_true]
  constructor
  · intro h b hb
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hb
    have hh : n+i < w.length := by simp only [List.length_drop] at hi; omega
    have hbit := h ⟨n+i,hh⟩ (by change n ≤ n+i; omega)
    have he' : w[n+i]=b := by simpa using he
    change w[n+i]=false at hbit
    rw [← he',hbit]
    rfl
  · intro h i hi
    have hk : i.val-n < (w.drop n).length := by simp; omega
    have he : (w.drop n)[i.val-n]=w.get i := by simp [Nat.add_sub_of_le hi]
    have hb := h _ (List.getElem_mem hk)
    rw [he] at hb
    simpa using hb

 theorem selectedPairs_iff {n : ℕ} (payload witness : BitString) (G : MatrixGraph n)
    (hg : G.edge=flatEdge n payload) (hn : n ≤ witness.length) :
    ValidSelectedPairs n payload witness ↔
      G.ValidIndependent (restrictCertificate hn (fun i => witness.get i)) := by
  unfold ValidSelectedPairs MatrixGraph.ValidIndependent restrictCertificate
  have hbit (i : Fin n) : bitAt witness i.val=witness.get (i.castLE hn) :=
    bitAt_get witness i.val (i.isLt.trans_le hn)
  simp only [hbit,hg]

end HiddenCircuits.Complexity.GraphVerifier
