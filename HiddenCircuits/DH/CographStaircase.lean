import HiddenCircuits.DH.CographSpine

/-! The alternating staircase lemma underlying two-sweep cotree extraction.
Rows and columns are ordinary strictly nested graph profiles. -/
namespace HiddenCircuits.DH.CographStaircase
variable {A B : Type*}

/-- Successive rows have strictly decreasing true sets. -/
def Rows (edge : A → B → Prop) (as : List A) (bs : List B) : Prop :=
  as.Pairwise (fun a a' => (∀ b∈bs, edge a' b → edge a b) ∧
    ∃ b∈bs, edge a b ∧ ¬edge a' b)

/-- Successive columns have strictly increasing true sets. -/
def Cols (edge : A → B → Prop) (as : List A) (bs : List B) : Prop :=
  bs.Pairwise (fun b b' => (∀ a∈as, edge a b → edge a b') ∧
    ∃ a∈as, edge a b' ∧ ¬edge a b)

lemma first_row_full {edge : A → B → Prop} {a : A} {as : List A} {b : B} {bs : List B}
    (hc : Cols edge (a::as) (b::bs)) (he : edge a b) : ∀ c∈b::bs, edge a c := by
  intro c h
  rcases List.mem_cons.mp h with rfl | h
  · exact he
  · exact ((List.pairwise_cons.mp hc).1 c h).1 a List.mem_cons_self he

lemma first_col_empty {edge : A → B → Prop} {a : A} {as : List A} {b : B} {bs : List B}
    (hr : Rows edge (a::as) (b::bs)) (he : ¬edge a b) : ∀ c∈a::as, ¬edge c b := by
  intro c h hc
  rcases List.mem_cons.mp h with rfl | h
  · exact he hc
  · exact he (((List.pairwise_cons.mp hr).1 c h).1 b List.mem_cons_self hc)

lemma remove_full_row {edge : A → B → Prop} {a : A} {as : List A} {bs : List B}
    (hc : Cols edge (a::as) bs) (hfull : ∀ b∈bs, edge a b) : Cols edge as bs := by
  apply hc.imp_of_mem
  intro b b' hb hb' h
  refine ⟨fun x hx => h.1 x (List.mem_cons_of_mem _ hx),?_⟩
  obtain ⟨x,hx,ht,hf⟩ := h.2
  rcases List.mem_cons.mp hx with rfl | hx
  · exact False.elim (hf (hfull b hb))
  · exact ⟨x,hx,ht,hf⟩

lemma remove_empty_col {edge : A → B → Prop} {as : List A} {b : B} {bs : List B}
    (hr : Rows edge as (b::bs)) (hempty : ∀ a∈as, ¬edge a b) : Rows edge as bs := by
  apply hr.imp_of_mem
  intro a a' ha ha' h
  refine ⟨fun x hx => h.1 x (List.mem_cons_of_mem _ hx),?_⟩
  obtain ⟨x,hx,ht,hf⟩ := h.2
  rcases List.mem_cons.mp hx with rfl | hx
  · exact False.elim (hempty a ha ht)
  · exact ⟨x,hx,ht,hf⟩

/-- After taking a full first row, the next column is empty on the residual rows. -/
lemma after_row_next_col_empty {edge : A → B → Prop} {a : A} {as : List A} {b : B} {bs : List B}
    (hr : Rows edge (a::as) (b::bs)) (hc : Cols edge (a::as) (b::bs)) :
    ∀ c∈as, ¬edge c b := by
  intro c hmem he
  obtain ⟨d,hd,_,hcd⟩ := ((List.pairwise_cons.mp hr).1 c hmem).2
  rcases List.mem_cons.mp hd with rfl | hd
  · exact hcd he
  · exact hcd (((List.pairwise_cons.mp hc).1 d hd).1 c (List.mem_cons_of_mem _ hmem) he)

/-- After taking an empty first column, the next row is full on the residual columns. -/
lemma after_col_next_row_full {edge : A → B → Prop} {a : A} {as : List A} {b : B} {bs : List B}
    (hr : Rows edge (a::as) (b::bs)) (hc : Cols edge (a::as) (b::bs)) :
    ∀ c∈bs, edge a c := by
  intro c hmem
  obtain ⟨d,hd,hdc,_⟩ := ((List.pairwise_cons.mp hc).1 c hmem).2
  rcases List.mem_cons.mp hd with rfl | hd
  · exact hdc
  · exact ((List.pairwise_cons.mp hr).1 d hd).1 c (List.mem_cons_of_mem _ hmem) hdc

/-- The only query needed is the first head pair. False starts with a normal
nonneighbor class; true starts with a complementary nonneighbor class. -/
def HeadChoice (edge : A → B → Prop) (takeRight : Bool) (as : List A) (bs : List B) : Prop :=
  match as,bs with
  | a::_,b::_ => edge a b ↔ takeRight = false
  | _,_ => True

/-- Alternate constant-time head removals; exhausted lists are drained once. -/
def weave (takeRight : Bool) (as : List A) (bs : List B) : List (A ⊕ B) :=
  match as,bs with
  | [],bs => bs.map Sum.inr
  | as,[] => as.map Sum.inl
  | a::as,b::bs =>
      if takeRight then Sum.inr b :: weave false (a::as) bs
      else Sum.inl a :: weave true as (b::bs)
termination_by as.length+bs.length

/-- Adjacency between normal and complementary branch representatives, including
empty normal cuts and complete complementary cuts. -/
def cross (edge : A → B → Prop) : (A ⊕ B) → (A ⊕ B) → Prop
  | .inl _,.inl _ => False
  | .inr _,.inr _ => True
  | .inl a,.inr b => edge a b
  | .inr b,.inl a => edge a b

def joined : (A ⊕ B) → Bool
  | .inl _ => false
  | .inr _ => true

lemma mem_weave (s : Bool) (as : List A) (bs : List B) (x : A ⊕ B) :
    x∈weave s as bs ↔ (∃ a∈as, x=Sum.inl a) ∨ (∃ b∈bs, x=Sum.inr b) := by
  cases x <;> fun_induction weave s as bs <;> simp_all [List.mem_map]

@[simp] lemma weave_length (s : Bool) (as : List A) (bs : List B) :
    (weave s as bs).length = as.length+bs.length := by
  fun_induction weave s as bs <;> simp_all [weave] <;> omega

/-- The alternating order exactly reconstructs every cross-branch adjacency by
the later branch's union/join tag. -/
theorem weave_spec (edge : A → B → Prop) (s : Bool) (as : List A) (bs : List B)
    (hr : Rows edge as bs) (hc : Cols edge as bs) (hh : HeadChoice edge s as bs) :
    (weave s as bs).Pairwise (fun x y => cross edge x y ↔ joined y = true) := by
  fun_induction weave s as bs with
  | case1 s bs => simpa [List.pairwise_map,cross,joined] using (List.pairwise_of_forall (l := bs) (R := fun _ _ => True) (by intros; trivial))
  | case2 s as hne => simpa [List.pairwise_map,cross,joined] using (List.pairwise_of_forall (l := as) (R := fun _ _ => True) (by intros; trivial))
  | case3 a as b bs ih =>
    have he : ¬edge a b := by simpa [HeadChoice] using hh
    have hnone := first_col_empty hr he
    have hr' := remove_empty_col hr hnone
    have hc' : Cols edge (a::as) bs := (List.pairwise_cons.mp hc).2
    have hh' : HeadChoice edge false (a::as) bs := by
      cases bs with
      | nil => trivial
      | cons c cs =>
        exact iff_of_true (after_col_next_row_full hr hc c List.mem_cons_self) rfl
    refine List.pairwise_cons.mpr ⟨?_,ih hr' hc' hh'⟩
    intro y hy
    rcases (mem_weave false (a::as) bs y).mp hy with ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩
    · exact iff_of_false (hnone x hx) Bool.false_ne_true
    · exact iff_of_true trivial rfl
  | case4 s a as b bs hs ih =>
    have hs' : s=false := by cases s <;> simp_all
    subst s
    have he : edge a b := by simpa [HeadChoice] using hh
    have hfull := first_row_full hc he
    have hr' : Rows edge as (b::bs) := (List.pairwise_cons.mp hr).2
    have hc' := remove_full_row hc hfull
    have hh' : HeadChoice edge true as (b::bs) := by
      cases as with
      | nil => trivial
      | cons c cs =>
        exact iff_of_false (after_row_next_col_empty hr hc c List.mem_cons_self) (by decide : true ≠ false)
    refine List.pairwise_cons.mpr ⟨?_,ih hr' hc' hh'⟩
    intro y hy
    rcases (mem_weave true as (b::bs) y).mp hy with ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩
    · simp [cross,joined]
    · exact iff_of_true (hfull x hx) rfl

/-- Any pairwise property preserved inside both input lists and across the two
sides is preserved by the actual alternating weave. -/
theorem weave_pairwise {R : (A ⊕ B) → (A ⊕ B) → Prop}
    (s : Bool) (as : List A) (bs : List B)
    (ha : as.Pairwise (fun a a' => R (.inl a) (.inl a')))
    (hb : bs.Pairwise (fun b b' => R (.inr b) (.inr b')))
    (hab : ∀a∈as, ∀b∈bs, R (.inl a) (.inr b) ∧ R (.inr b) (.inl a)) :
    (weave s as bs).Pairwise R := by
  fun_induction weave s as bs with
  | case1 s bs => exact List.pairwise_map.mpr hb
  | case2 s as hne => exact List.pairwise_map.mpr ha
  | case3 a as b bs ih =>
    refine List.pairwise_cons.mpr ⟨?_,ih ha (List.pairwise_cons.mp hb).2 ?_⟩
    · intro y hy
      rcases (mem_weave false (a::as) bs y).mp hy with ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩
      · exact (hab x hx b List.mem_cons_self).2
      · exact (List.pairwise_cons.mp hb).1 x hx
    · intro x hx y hy
      exact hab x hx y (List.mem_cons_of_mem _ hy)
  | case4 s a as b bs hs ih =>
    refine List.pairwise_cons.mpr ⟨?_,ih (List.pairwise_cons.mp ha).2 hb ?_⟩
    · intro y hy
      rcases (mem_weave true as (b::bs) y).mp hy with ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩
      · exact (List.pairwise_cons.mp ha).1 x hx
      · exact (hab a List.mem_cons_self x hx).1
    · intro x hx y hy
      exact hab x (List.mem_cons_of_mem _ hx) y hy

end HiddenCircuits.DH.CographStaircase
