-- Recovered prefix, followed by explicitly reconstructed confined-route proofs.
import HiddenCircuits.Approximation.CanonicalPaths.MonotoneRectangle
namespace HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
attribute [local instance] Classical.propDecidable
variable {n : ℕ}
def Ordered (R : Fin n → Fin n → Prop) : Prop :=
  ∀ i j r s, i ≤ j → r ≤ s → R i s → R j r → R i r ∧ R j s
abbrev State (R : Fin n → Fin n → Prop) := {p : Equiv.Perm (Fin n) // ∀ i, R i (p i)}
noncomputable def disagreements {R : Fin n → Fin n → Prop} (p q : State R) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p.val i≠q.val i)
@[simp] theorem mem_disagreements {R : Fin n → Fin n → Prop} (p q : State R) (i : Fin n) :
    i∈disagreements p q ↔ p.val i≠q.val i := by simp [disagreements]
theorem disagreements_symm {R : Fin n → Fin n → Prop} (p q : State R) :
    disagreements p q=disagreements q p := by ext i; simp [ne_comm]
def Move {R : Fin n → Fin n → Prop} (S : Finset (Fin n)) (p q : State R) : Prop :=
  ∃ i∈S, ∃ j∈S, q.val=(Equiv.swap i j).trans p.val
theorem Move.symm {R : Fin n → Fin n → Prop} {S : Finset (Fin n)} {p q : State R}
    (h : Move S p q) : Move S q p := by
  rcases h with ⟨i,hi,j,hj,h⟩
  refine ⟨i,hi,j,hj,?_⟩
  rw [h]
  apply Equiv.ext
  intro k
  simp
inductive Route {R : Fin n → Fin n → Prop} (S : Finset (Fin n)) :
    State R → State R → ℕ → Prop
  | nil (p) : Route S p p 0
  | step {p q r k} : Move S p q → Route S q r k → Route S p r (k+1)
theorem Route.append {R : Fin n → Fin n → Prop} {S : Finset (Fin n)} {p q r : State R}
    {k l : ℕ} (h : Route S p q k) (h' : Route S q r l) : Route S p r (k+l) := by
  induction h with
  | nil p => simpa using h'
  | step hm hr ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Route.step hm (ih h')

theorem Route.reverse {R : Fin n → Fin n → Prop} {S : Finset (Fin n)} {p q : State R} {k : ℕ}
    (h : Route S p q k) : Route S q p k := by
  induction h with
  | nil p => exact Route.nil p
  | step hm hr ih =>
    simpa using ih.append (Route.step hm.symm (Route.nil _))

private theorem route_enlarge {R : Fin n → Fin n → Prop} {S T : Finset (Fin n)}
    (hst : S⊆T) {p q : State R} {k : ℕ} (h : Route S p q k) : Route T p q k := by
  induction h with
  | nil p => exact Route.nil p
  | step hm hr ih =>
    obtain ⟨i,hi,j,hj,he⟩ := hm
    exact Route.step ⟨i,hst hi,j,hst hj,he⟩ ih

/-- The first disagreement can be uncrossed on whichever matching has the larger row. -/
theorem uncross_first {R : Fin n → Fin n → Prop} (hR : Ordered R) (p q : State R)
    (hne : (disagreements p q).Nonempty)
    (hlarge : q.val ((disagreements p q).min' hne) < p.val ((disagreements p q).min' hne)) :
    ∃ p' : State R,Move (disagreements p q) p p' ∧ disagreements p' q ⊂ disagreements p q := by
  let S := disagreements p q
  let i := S.min' hne
  let j := p.val.symm (q.val i)
  have hi : i∈S := Finset.min'_mem S hne
  have hdiff : p.val i≠q.val i := (mem_disagreements p q i).mp hi
  have hpj : p.val j=q.val i := p.val.apply_symm_apply _
  have hij : i≠j := by
    intro h
    exact hdiff (by simpa only [h] using hpj)
  have hj : j∈S := by
    apply (mem_disagreements p q j).mpr
    intro h
    have he : i=j := q.val.injective (hpj.symm.trans h)
    exact hij he
  have hijle : i ≤ j := Finset.min'_le S j hj
  have hcross := hR i j (q.val i) (p.val i) hijle hlarge.le (p.property i) (by simpa only [hpj] using p.property j)
  let p' : State R := ⟨(Equiv.swap i j).trans p.val,by
    intro k
    by_cases hk : k=i
    · subst k
      simpa only [Equiv.trans_apply,Equiv.swap_apply_left,hpj] using hcross.1
    by_cases hk' : k=j
    · subst k
      simpa only [Equiv.trans_apply,Equiv.swap_apply_right] using hcross.2
    · simpa only [Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne hk hk'] using p.property k⟩
  have hsub : disagreements p' q⊆S := by
    intro k hk
    by_contra hn
    have hki : k≠i := fun h => hn (h.symm ▸ hi)
    have hkj : k≠j := fun h => hn (h.symm ▸ hj)
    have he : p.val k=q.val k := by simpa only [S,mem_disagreements,not_not] using hn
    have hd := (mem_disagreements p' q k).mp hk
    exact hd (by simpa only [p',Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne hki hkj] using he)
  refine ⟨p',⟨i,hi,j,hj,rfl⟩,Finset.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩⟩
  intro he
  have himem : i∈disagreements p' q := he.symm ▸ hi
  have hbad := (mem_disagreements p' q i).mp himem
  exact hbad (by simp only [p',Equiv.trans_apply,Equiv.swap_apply_left,hpj])

/-- A genuine route of at most one switch per disagreement, confined to those columns. -/
theorem exists_confined_route {R : Fin n → Fin n → Prop} (hR : Ordered R) (p q : State R) :
    ∃ k ≤ (disagreements p q).card,Route (disagreements p q) p q k := by
  have aux : ∀ m,∀ p q : State R,(disagreements p q).card=m →
      ∃ k ≤ m,Route (disagreements p q) p q k := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro p q hcard
      by_cases he : p=q
      · subst q
        exact ⟨0,Nat.zero_le _,Route.nil _⟩
      have hne : (disagreements p q).Nonempty := by
        by_contra hn
        apply he
        apply Subtype.ext
        apply Equiv.ext
        intro i
        have hh : i∉disagreements p q := fun h => hn ⟨i,h⟩
        simpa only [mem_disagreements,not_not] using hh
      let i := (disagreements p q).min' hne
      have hdiff : p.val i≠q.val i := (mem_disagreements p q i).mp (Finset.min'_mem _ hne)
      rcases lt_or_gt_of_ne hdiff with hsmall|hlarge
      · have hne' : (disagreements q p).Nonempty := by simpa only [disagreements_symm q p] using hne
        have hlarge' : p.val ((disagreements q p).min' hne') < q.val ((disagreements q p).min' hne') := by
          simpa only [disagreements_symm q p] using hsmall
        obtain ⟨q',hm,hs⟩ := uncross_first hR q p hne' hlarge'
        have hlt : (disagreements q' p).card<m := by
          have hh := Finset.card_lt_card hs
          simpa only [disagreements_symm q p,hcard] using hh
        obtain ⟨k,hk,hr⟩ := ih _ hlt q' p rfl
        have hroute := Route.step hm (route_enlarge hs.subset hr)
        refine ⟨k+1,by omega,?_⟩
        simpa only [disagreements_symm q p] using hroute.reverse
      · obtain ⟨p',hm,hs⟩ := uncross_first hR p q hne hlarge
        have hlt : (disagreements p' q).card<m := by simpa only [hcard] using Finset.card_lt_card hs
        obtain ⟨k,hk,hr⟩ := ih _ hlt p' q rfl
        exact ⟨k+1,by omega,Route.step hm (route_enlarge hs.subset hr)⟩
  exact aux _ p q rfl

theorem endpoint_ordered (E : MonotoneEndpoints n) : Ordered (fun col row => Allowed E row col) := by
  intro i j r s hij hrs his hjr
  exact rectangle_completion E hrs hij hjr his

end HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
