import HiddenCircuits.RawCode
import HiddenCircuits.ProjectionSplit

/-! Literal logical concatenation and physical selected-track compatibility. -/
namespace HiddenCircuits
namespace State

def HasTrack {n q : ℕ} (S : State n q) (t : ℕ) : Prop :=
  ∃ h : t<n, (⟨t,h⟩ : Fin n) ∈ S.val

lemma hasTrack_iff_mem {n q : ℕ} (S : State n q) (i : Fin n) :
    S.HasTrack i.val ↔ i ∈ S.val := by
  constructor
  · rintro ⟨h,hh⟩; exact hh
  · intro h; exact ⟨i.isLt,h⟩

lemma ext_hasTrack {n q : ℕ} {S T : State n q}
    (h : ∀ t, S.HasTrack t ↔ T.HasTrack t) : S=T := by
  apply Subtype.ext
  apply Finset.ext
  intro i
  rw [← hasTrack_iff_mem,← hasTrack_iff_mem]
  exact h i.val

@[simp] lemma hasTrack_castTracks {n m q : ℕ} (h : n=m) (S : State n q) (t : ℕ) :
    (castTracks h S).HasTrack t ↔ S.HasTrack t := by subst m; rfl
@[simp] lemma hasTrack_castParticles {n q r : ℕ} (h : q=r) (S : State n q) (t : ℕ) :
    (castParticles h S).HasTrack t ↔ S.HasTrack t := by subst r; rfl

lemma hasTrack_join {a b u v : ℕ} (S : State a u) (T : State b v) (t : ℕ) :
    (join S T).HasTrack t ↔ S.HasTrack t ∨ (a ≤ t ∧ T.HasTrack (t-a)) := by
  by_cases ht : t<a
  · have hn : t<a+b := by omega
    have hm := join_mem_left S T ⟨t,ht⟩
    constructor
    · rintro ⟨h,hh⟩
      left
      exact ⟨ht,hm.mp hh⟩
    · rintro (⟨h,hh⟩ | ⟨ha,hh⟩)
      · exact ⟨hn,hm.mpr hh⟩
      · omega
  · constructor
    · rintro ⟨h,hh⟩
      have hb : t-a<b := by omega
      right
      refine ⟨by omega, hb, ?_⟩
      apply (join_mem_right S T ⟨t-a,hb⟩).mp
      have he : Fin.natAdd a ⟨t-a,hb⟩ = (⟨t,h⟩ : Fin (a+b)) := by
        apply Fin.ext
        change a+(t-a)=t
        omega
      simpa only [he] using hh
    · rintro (⟨h,hh⟩ | ⟨ha,hb,hh⟩)
      · omega
      · have hn : t<a+b := by omega
        refine ⟨hn,?_⟩
        have hm := (join_mem_right S T ⟨t-a,hb⟩).mpr hh
        have he : Fin.natAdd a ⟨t-a,hb⟩ = (⟨t,hn⟩ : Fin (a+b)) := by
          apply Fin.ext
          change a+(t-a)=t
          omega
        simpa only [he] using hm

end State

/-- Left-recursive addition lets tuple concatenation compute without intermediate casts. -/
def concatSize : ℕ → ℕ → ℕ
  | 0,b => b
  | a+1,b => concatSize a b + 1

lemma concatSize_eq (a b : ℕ) : concatSize a b = a+b := by
  induction a with
  | zero => simp [concatSize]
  | succ a ih => simp [concatSize,ih,Nat.succ_add]

def concatCore : (a b : ℕ) → CodeBits a → CodeBits b → CodeBits (concatSize a b)
  | 0,_,_,y => y
  | a+1,b,x,y => (x.1,concatCore a b x.2 y)

def splitCore : (a b : ℕ) → CodeBits (concatSize a b) → CodeBits a × CodeBits b
  | 0,_,y => (PUnit.unit,y)
  | a+1,b,x => ((x.1,(splitCore a b x.2).1),(splitCore a b x.2).2)

lemma split_concat_core (a b : ℕ) (x : CodeBits a) (y : CodeBits b) :
    splitCore a b (concatCore a b x y)=(x,y) := by
  induction a with
  | zero => cases x; rfl
  | succ a ih =>
    rcases x with ⟨x,xs⟩
    change ((x,(splitCore a b (concatCore a b xs y)).1),
      (splitCore a b (concatCore a b xs y)).2)=((x,xs),y)
    rw [ih xs]

lemma concat_split_core (a b : ℕ) (x : CodeBits (concatSize a b)) :
    concatCore a b (splitCore a b x).1 (splitCore a b x).2=x := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rcases x with ⟨x,xs⟩
    change (x,concatCore a b (splitCore a b xs).1 (splitCore a b xs).2)=(x,xs)
    rw [ih xs]

def concatCoreEquiv (a b : ℕ) : CodeBits a × CodeBits b ≃ CodeBits (concatSize a b) where
  toFun x := concatCore a b x.1 x.2
  invFun := splitCore a b
  left_inv x := split_concat_core a b x.1 x.2
  right_inv := concat_split_core a b

/-- Canonical consecutive concatenation of actual logical tuples. -/
def codeConcatEquiv (a b : ℕ) : CodeBits a × CodeBits b ≃ CodeBits (a+b) :=
  (concatCoreEquiv a b).trans (Equiv.cast (congrArg CodeBits (concatSize_eq a b)))

def codeConcat (a b : ℕ) (x : CodeBits a) (y : CodeBits b) : CodeBits (a+b) :=
  codeConcatEquiv a b (x,y)

lemma rawCode_succ_hasTrack (a : ℕ) (x : CodeBits (a+1)) (t : ℕ) :
    (rawCode (a+1) x).HasTrack t ↔
      (localRawCode x.1).HasTrack t ∨ (4≤t ∧ (rawCode a x.2).HasTrack (t-4)) := by
  change (State.castParticles (by omega) (State.join (localRawCode x.1) (rawCode a x.2))).HasTrack t ↔ _
  rw [State.hasTrack_castParticles,State.hasTrack_join]

lemma concatCore_hasTrack (a b : ℕ) (x : CodeBits a) (y : CodeBits b) (t : ℕ) :
    (rawCode (concatSize a b) (concatCore a b x y)).HasTrack t ↔
      (rawCode a x).HasTrack t ∨
        (blockWidth a ≤ t ∧ (rawCode b y).HasTrack (t-blockWidth a)) := by
  induction a generalizing t with
  | zero =>
    have hz : ¬ (rawCode 0 x).HasTrack t := by rintro ⟨h,_⟩; exact Nat.not_lt_zero t h
    change (rawCode b y).HasTrack t ↔ (rawCode 0 x).HasTrack t ∨
      (0≤t ∧ (rawCode b y).HasTrack (t-0))
    simp [hz]
  | succ a ih =>
    rcases x with ⟨x,xs⟩
    change (rawCode (concatSize a b+1) (x,concatCore a b xs y)).HasTrack t ↔ _
    rw [rawCode_succ_hasTrack,rawCode_succ_hasTrack,ih xs (t-4)]
    change ((localRawCode x).HasTrack t ∨
      4≤t ∧ ((rawCode a xs).HasTrack (t-4) ∨
        blockWidth a ≤ t-4 ∧ (rawCode b y).HasTrack ((t-4)-blockWidth a))) ↔
      ((localRawCode x).HasTrack t ∨ 4≤t ∧ (rawCode a xs).HasTrack (t-4)) ∨
        (4+blockWidth a ≤ t ∧ (rawCode b y).HasTrack (t-(4+blockWidth a)))
    rw [Nat.sub_sub]
    have hh : 4≤t ∧ blockWidth a ≤ t-4 ↔ 4+blockWidth a ≤ t := by omega
    tauto

lemma rawCode_cast_hasTrack {a b : ℕ} (h : a=b) (x : CodeBits a) (t : ℕ) :
    (rawCode b (cast (congrArg CodeBits h) x)).HasTrack t ↔ (rawCode a x).HasTrack t := by
  subst b
  rfl

/-- Logical concatenation is exactly concatenation of the actual selected physical tracks. -/
theorem rawCode_concat (a b : ℕ) (x : CodeBits a) (y : CodeBits b) :
    rawCode (a+b) (codeConcat a b x y) = splitState a b (rawCode a x,rawCode b y) := by
  apply State.ext_hasTrack
  intro t
  change (rawCode (a+b) (cast (congrArg CodeBits (concatSize_eq a b)) (concatCore a b x y))).HasTrack t ↔ _
  rw [rawCode_cast_hasTrack (concatSize_eq a b),concatCore_hasTrack]
  simp only [splitState,State.hasTrack_castParticles,State.hasTrack_castTracks,State.hasTrack_join]

/-- Canonical three-region logical grouping used by the localized circuit interface. -/
def codeTripleConcatEquiv (a b c : ℕ) :
    CodeBits a × (CodeBits b × CodeBits c) ≃ CodeBits (a+(b+c)) :=
  (Equiv.prodCongr (Equiv.refl _) (codeConcatEquiv b c)).trans (codeConcatEquiv a (b+c))

theorem rawCode_triple_concat (a b c : ℕ) (x : CodeBits a × (CodeBits b × CodeBits c)) :
    rawCode (a+(b+c)) (codeTripleConcatEquiv a b c x) =
      splitState a (b+c) (rawCode a x.1,splitState b c (rawCode b x.2.1,rawCode c x.2.2)) := by
  change rawCode (a+(b+c)) (codeConcat a (b+c) x.1 (codeConcat b c x.2.1 x.2.2)) = _
  rw [rawCode_concat,rawCode_concat]

lemma rawCode_concat_hasTrack (a b : ℕ) (x : CodeBits a) (y : CodeBits b) (t : ℕ) :
    (rawCode (a+b) (codeConcat a b x y)).HasTrack t ↔
      (rawCode a x).HasTrack t ∨
        (blockWidth a ≤ t ∧ (rawCode b y).HasTrack (t-blockWidth a)) := by
  rw [rawCode_concat]
  simp only [splitState,State.hasTrack_castParticles,State.hasTrack_castTracks,State.hasTrack_join]

/-- Consecutive logical grouping is associative with the explicit natural-index transport. -/
theorem codeConcat_assoc (a b c : ℕ) (x : CodeBits a) (y : CodeBits b) (z : CodeBits c) :
    codeConcat a (b+c) x (codeConcat b c y z) =
      cast (congrArg CodeBits (Nat.add_assoc a b c)) (codeConcat (a+b) c (codeConcat a b x y) z) := by
  apply rawCode_injective (a+(b+c))
  apply State.ext_hasTrack
  intro t
  rw [rawCode_cast_hasTrack (Nat.add_assoc a b c)]
  simp_rw [rawCode_concat_hasTrack]
  rw [blockWidth_add,Nat.sub_sub]
  have hh : blockWidth a ≤ t ∧ blockWidth b ≤ t-blockWidth a ↔
      blockWidth a+blockWidth b ≤ t := by omega
  tauto

end HiddenCircuits
