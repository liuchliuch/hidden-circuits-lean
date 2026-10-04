import HiddenCircuits.Complexity.GraphVerifier.MatchingCertificates
import HiddenCircuits.Complexity.GraphVerifier.PairScanSemantics

/-! Flat matching verification: local matrix tests and exactly-one-entry row tests. -/
namespace HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime

def EntryOK (n : ℕ) (payload witness : BitString) (i j : ℕ) : Prop :=
  bitAt payload (j+n*i)=bitAt payload (i+n*j) ∧
    (i=j → bitAt payload (j+n*i)=false) ∧
    bitAt witness (j+n*i)=bitAt witness (i+n*j) ∧
    (bitAt witness (j+n*i)=true → bitAt payload (j+n*i)=true)
instance (n : ℕ) (payload witness : BitString) (i j : ℕ) : Decidable (EntryOK n payload witness i j) :=
  inferInstanceAs (Decidable (_=_ ∧ (_=_ → _=_) ∧ _=_ ∧ (_=_ → _=_)))
def entryFlag (n : ℕ) (payload witness : BitString) (i j : ℕ) : Bool := decide (EntryOK n payload witness i j)
def scanPairs (n : ℕ) (payload witness : BitString) : Bool :=
  (List.range n).all (fun i => (List.range n).all (fun j => entryFlag n payload witness i j))
def pairDecision (f b l r d a : Bool) : Bool :=
  a && (f==b) && !(d && f) && (l==r) && (!l || f)

 theorem pairDecision_correct (n : ℕ) (payload witness : BitString) (i j : ℕ) (a : Bool) :
    pairDecision (bitAt payload (j+n*i)) (bitAt payload (i+n*j))
      (bitAt witness (j+n*i)) (bitAt witness (i+n*j)) (decide (i=j)) a=
      (a && entryFlag n payload witness i j) := by
  unfold pairDecision entryFlag EntryOK
  by_cases hij:i=j <;> simp only [hij,decide_true,decide_false]
  all_goals cases h₁:bitAt payload (j+n*i) <;> cases h₂:bitAt payload (i+n*j) <;>
    cases h₃:bitAt witness (j+n*i) <;> cases h₄:bitAt witness (i+n*j) <;> cases a <;> simp_all

 theorem scanPairs_iff (n : ℕ) (payload witness : BitString) : scanPairs n payload witness=true ↔
    (∀ i j : Fin n, flatEdge n payload i j=flatEdge n payload j i) ∧
      (∀ i : Fin n, flatEdge n payload i i=false) ∧
      (∀ i j : Fin n, flatEdge n witness i j=flatEdge n witness j i) ∧
      (∀ i j : Fin n, flatEdge n witness i j=true → flatEdge n payload i j=true) := by
  simp only [scanPairs,List.all_eq_true,List.mem_range,entryFlag,decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨fun i j => (h i.val i.isLt j.val j.isLt).1,
      fun i => (h i.val i.isLt i.val i.isLt).2.1 rfl,
      fun i j => (h i.val i.isLt j.val j.isLt).2.2.1,
      fun i j => (h i.val i.isLt j.val j.isLt).2.2.2⟩
  · rintro ⟨hs,hl,hc,he⟩ i hi j hj
    exact ⟨hs ⟨i,hi⟩ ⟨j,hj⟩,fun hij => by subst j;exact hl ⟨i,hi⟩,
      hc ⟨i,hi⟩ ⟨j,hj⟩,he ⟨i,hi⟩ ⟨j,hj⟩⟩

def RowsOne (n : ℕ) (w : BitString) : Prop := ∀ i : Fin n, ∃! j : Fin n, flatEdge n w i j=true
instance (n : ℕ) (w : BitString) : Decidable (RowsOne n w) := by
  unfold RowsOne ExistsUnique
  infer_instance

 theorem matching_payload_iff {n : ℕ} (G : MatrixGraph n) (w : BitString) (hw : n*n≤w.length) :
    scanPairs n G.bits w=true ∧ RowsOne n w ↔
      G.ValidPerfect (fun i => bitAt w i.val) := by
  rw [scanPairs_iff]
  have he (i j : Fin n) : flatEdge n G.bits i j=G.edge i j := by
    unfold flatEdge
    rw [bitAt_get G.bits _ (by simpa using (finProdFinEquiv (i,j)).isLt)]
    exact G.get_bits i j _
  constructor
  · rintro ⟨⟨_,_,hs,hi⟩,hr⟩
    refine ⟨hr,hs,?_⟩
    intro i j hj
    exact (he i j) ▸ hi i j hj
  · rintro ⟨hr,hs,hi⟩
    refine ⟨⟨?_,?_,hs,?_⟩,hr⟩
    · intro i j;rw [he,he,G.symm]
    · intro i;rw [he,G.loopless]
    · intro i j hj;rw [he];exact hi i j hj

end HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
