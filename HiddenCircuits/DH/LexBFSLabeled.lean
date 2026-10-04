import HiddenCircuits.DH.LexBFSSparse

/-! Proof-side provenance blocks for the interleaved pointer-partition loop.
Each original cell remains one ghost block even after its live old-cell ID disappears.
Fresh companions occupy distinct numeric IDs and are emitted beside their original block. -/
namespace HiddenCircuits.DH.LexBFSLabeled
open LexBFSModel LexBFSSparse

structure Block (n b : ℕ) where
  original : Fin b
  residual : List (Fin n)
  companion : Option (Fin b)
  moved : List (Fin n)
  deriving Repr

/-- Companion allocation is exactly first touch, so its list is nonempty precisely when allocated. -/
def Block.Valid {n b : ℕ} (c : Block n b) : Prop := c.companion = none ↔ c.moved = []

def namedCell {n b : ℕ} (id : Fin b) (xs : List (Fin n)) : List (Fin b × List (Fin n)) :=
  if xs = [] then [] else [(id,xs)]

def Block.emit {n b : ℕ} (first : Bool) (c : Block n b) : List (Fin b × List (Fin n)) :=
  let old := namedCell c.original c.residual
  let fresh := c.companion.toList.flatMap (fun d => namedCell d c.moved)
  if first then fresh++old else old++fresh

@[simp] lemma namedCell_values {n b : ℕ} (id : Fin b) (xs : List (Fin n)) :
    (namedCell id xs).map Prod.snd = nonemptyCell xs := by
  by_cases h : xs=[] <;> simp [namedCell,nonemptyCell,h]

lemma Block.emit_values {n b : ℕ} (first : Bool) (c : Block n b) (hc : c.Valid) :
    (c.emit first).map Prod.snd =
      if first then nonemptyCell c.moved ++ nonemptyCell c.residual else
        nonemptyCell c.residual ++ nonemptyCell c.moved := by
  cases h : c.companion with
  | none =>
    have hm : c.moved=[] := hc.mp h
    cases first <;> simp [Block.emit,h,hm,nonemptyCell]
  | some d => cases first <;> simp [Block.emit,h]

/-- One actual neighbor transfer; a supplied fresh ID is used only on first touch. -/
def Block.advance {n b : ℕ} (c : Block n b) (v : Fin n) (fresh : Fin b) : Block n b :=
  ⟨c.original,c.residual.erase v,some (c.companion.getD fresh),c.moved++[v]⟩

lemma Block.advance_valid {n b : ℕ} (c : Block n b) (v : Fin n) (fresh : Fin b) :
    (c.advance v fresh).Valid := by simp [Block.Valid,Block.advance]

lemma Block.advance_pair {n b : ℕ} (c : Block n b) (v : Fin n) (fresh : Fin b)
    (hv : v ∈ c.residual) :
    ((c.advance v fresh).residual,(c.advance v fresh).moved) = moveRow [v] c.residual c.moved := by
  simp [Block.advance,moveRow,hv]

/-- This search is a ghost operation, with no claimed implementation cost. The heap engine
locates the same block directly through its owner array. -/
def moveOne {n b : ℕ} (v : Fin n) : List (Block n b) → ℕ → Option (List (Block n b) × ℕ)
  | [],fresh => some ([],fresh)
  | c::cs,fresh =>
      if v ∈ c.residual then
        match c.companion with
        | some d => some (c.advance v d::cs,fresh)
        | none => if hf : fresh < b then some (c.advance v ⟨fresh,hf⟩::cs,fresh+1) else none
      else (moveOne v cs fresh).map (fun q => (c::q.1,q.2))

/-- Residual cells are pairwise disjoint, as inherited from the genuine partition. -/
def Separate {n b : ℕ} (cs : List (Block n b)) : Prop :=
  cs.Pairwise (fun c d => ∀ v ∈ c.residual, v ∉ d.residual)

/-- Stable provenance and deletion-only residual updates. -/
def Descends {n b : ℕ} (c d : Block n b) : Prop :=
  c.original = d.original ∧ d.residual.Sublist c.residual

lemma Block.advance_descends {n b : ℕ} (c : Block n b) (v : Fin n) (fresh : Fin b) :
    Descends c (c.advance v fresh) := ⟨rfl,List.erase_sublist⟩

lemma moveOne_frame {n b : ℕ} (v : Fin n) (cs ds : List (Block n b)) (fresh fresh' : ℕ)
    (h : moveOne v cs fresh = some (ds,fresh')) : List.Forall₂ Descends cs ds := by
  induction cs generalizing ds fresh fresh' with
  | nil => simp only [moveOne,Option.some.injEq,Prod.mk.injEq] at h; obtain ⟨rfl,rfl⟩ := h; exact .nil
  | cons c cs ih =>
    simp only [moveOne] at h
    split at h
    · cases hb : c.companion with
      | some d =>
        simp only [hb,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        exact .cons (c.advance_descends v d) (List.forall₂_same.mpr (fun c _ => ⟨rfl,List.Sublist.refl _⟩))
      | none =>
        simp only [hb] at h
        split at h
        · obtain ⟨rfl,rfl⟩ := (Prod.mk.inj (Option.some.inj h))
          exact .cons (c.advance_descends v _) (List.forall₂_same.mpr (fun c _ => ⟨rfl,List.Sublist.refl _⟩))
        · contradiction
    · obtain ⟨q,hq,he⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      exact .cons ⟨rfl,List.Sublist.refl _⟩ (ih _ _ _ hq)

private lemma forall₂_mem_right {A B : Type*} {R : A → B → Prop} {as : List A} {bs : List B}
    (h : List.Forall₂ R as bs) {b : B} (hb : b ∈ bs) : ∃ a ∈ as, R a b := by
  induction h with
  | nil => simp at hb
  | cons hr hs ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_,List.mem_cons_self,hr⟩
    · obtain ⟨a,ha,hab⟩ := ih hb
      exact ⟨a,List.mem_cons_of_mem _ ha,hab⟩

lemma Separate.descends {n b : ℕ} {cs ds : List (Block n b)}
    (h : List.Forall₂ Descends cs ds) (hs : Separate cs) : Separate ds := by
  induction h with
  | nil => exact .nil
  | @cons c d cs ds hcd hrest ih =>
    obtain ⟨hc,ht⟩ := List.pairwise_cons.mp hs
    refine List.pairwise_cons.mpr ⟨?_,ih ht⟩
    intro e he v hv
    obtain ⟨old,hold,ho⟩ := forall₂_mem_right hrest he
    exact fun hve => hc old hold v (hcd.2.subset hv) (ho.2.subset hve)

/-- Processing one vertex in its unique old block is exactly simultaneous one-row refinement
of every block, including all the blocks which this vertex does not touch. -/
lemma moveOne_pairs {n b : ℕ} (v : Fin n) (cs ds : List (Block n b)) (fresh fresh' : ℕ)
    (hs : Separate cs) (h : moveOne v cs fresh = some (ds,fresh')) :
    ds.map (fun c => (c.residual,c.moved)) =
      cs.map (fun c => moveRow [v] c.residual c.moved) := by
  induction cs generalizing ds fresh fresh' with
  | nil => simp only [moveOne,Option.some.injEq,Prod.mk.injEq] at h; obtain ⟨rfl,rfl⟩ := h; rfl
  | cons c cs ih =>
    obtain ⟨hsep,hs⟩ := List.pairwise_cons.mp hs
    simp only [moveOne] at h
    split at h
    next hv =>
      have htail : cs.map (fun c => (c.residual,c.moved)) =
          cs.map (fun c => moveRow [v] c.residual c.moved) := by
        apply List.map_congr_left
        intro d hd
        simp [moveRow,hsep d hd v hv]
      cases hb : c.companion with
      | some d =>
        simp only [hb,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        simp only [List.map_cons,c.advance_pair v d hv,htail]
      | none =>
        simp only [hb] at h
        split at h
        · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
          simp only [List.map_cons,c.advance_pair v _ hv,htail]
        · contradiction
    next hv =>
      obtain ⟨q,hq,he⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      simp only [List.map_cons,moveRow,hv,↓reduceIte]
      exact congrArg (List.cons _) (ih _ _ _ hs hq)

lemma moveOne_skip_prefix {n b : ℕ} (v : Fin n) (left right : List (Block n b)) (fresh : ℕ)
    (hl : ∀ c ∈ left, v ∉ c.residual) :
    moveOne v (left++right) fresh = (moveOne v right fresh).map (fun q => (left++q.1,q.2)) := by
  induction left with
  | nil => simp
  | cons c left ih =>
    simp only [List.cons_append,moveOne,hl c List.mem_cons_self,↓reduceIte]
    rw [ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)),Option.map_map]
    rfl

lemma emit_frame {n b : ℕ} (first : Bool) (left middle right : List (Block n b)) :
    ((left++middle++right).flatMap (Block.emit first)) =
      left.flatMap (Block.emit first) ++ middle.flatMap (Block.emit first) ++ right.flatMap (Block.emit first) := by
  simp

lemma moveOne_fresh {n b : ℕ} (v : Fin n) (cs ds : List (Block n b)) (fresh fresh' : ℕ)
    (h : moveOne v cs fresh = some (ds,fresh')) : fresh ≤ fresh' ∧ fresh' ≤ fresh+1 := by
  induction cs generalizing ds fresh fresh' with
  | nil => simp only [moveOne,Option.some.injEq,Prod.mk.injEq] at h; omega
  | cons c cs ih =>
    simp only [moveOne] at h
    split at h
    · cases hb : c.companion with
      | some d => simp only [hb,Option.some.injEq,Prod.mk.injEq] at h; omega
      | none =>
        simp only [hb] at h
        split at h
        · have hh := Prod.mk.inj (Option.some.inj h); omega
        · contradiction
    · obtain ⟨q,hq,he⟩ := Option.map_eq_some_iff.mp h
      have hh : q.2=fresh' := congrArg Prod.snd he
      rw [← hh]
      exact ih _ _ _ hq

lemma moveOne_valid {n b : ℕ} (v : Fin n) (cs ds : List (Block n b)) (fresh fresh' : ℕ)
    (hc : ∀ c ∈ cs, c.Valid) (h : moveOne v cs fresh = some (ds,fresh')) :
    ∀ d ∈ ds, d.Valid := by
  induction cs generalizing ds fresh fresh' with
  | nil => simp only [moveOne,Option.some.injEq,Prod.mk.injEq] at h; obtain ⟨rfl,rfl⟩ := h; simp
  | cons c cs ih =>
    have htail : ∀ d ∈ cs, d.Valid := fun d hd => hc d (List.mem_cons_of_mem _ hd)
    simp only [moveOne] at h
    split at h
    · cases hb : c.companion with
      | some d =>
        simp only [hb,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact c.advance_valid v d
        · exact htail e he
      | none =>
        simp only [hb] at h
        split at h
        · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact c.advance_valid v _
          · exact htail e he
        · contradiction
    · obtain ⟨q,hq,he⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hc e List.mem_cons_self
      · exact ih _ _ _ htail hq e he

/-- Interleaved old-cell updates, with at most one fresh companion allocation per listed vertex. -/
def moveAll {n b : ℕ} : List (Fin n) → List (Block n b) → ℕ → Option (List (Block n b) × ℕ)
  | [],cs,fresh => some (cs,fresh)
  | v::row,cs,fresh => (moveOne v cs fresh).bind (fun q => moveAll row q.1 q.2)

lemma moveAll_fresh {n b : ℕ} (row : List (Fin n)) (cs ds : List (Block n b)) (fresh fresh' : ℕ)
    (h : moveAll row cs fresh = some (ds,fresh')) : fresh ≤ fresh' ∧ fresh' ≤ fresh+row.length := by
  induction row generalizing cs fresh with
  | nil => simp only [moveAll,Option.some.injEq,Prod.mk.injEq] at h; omega
  | cons v row ih =>
    obtain ⟨q,hq,ht⟩ := Option.bind_eq_some_iff.mp h
    have h1 := moveOne_fresh v cs q.1 fresh q.2 hq
    have h2 := ih _ _ ht
    simp only [List.length_cons]
    omega

lemma moveAll_valid {n b : ℕ} (row : List (Fin n)) (cs ds : List (Block n b)) (fresh fresh' : ℕ)
    (hc : ∀ c ∈ cs, c.Valid) (h : moveAll row cs fresh = some (ds,fresh')) :
    ∀ d ∈ ds, d.Valid := by
  induction row generalizing cs fresh with
  | nil => simp only [moveAll,Option.some.injEq,Prod.mk.injEq] at h; obtain ⟨rfl,rfl⟩ := h; exact hc
  | cons v row ih =>
    obtain ⟨q,hq,ht⟩ := Option.bind_eq_some_iff.mp h
    exact ih _ _ (moveOne_valid v cs q.1 fresh q.2 hc hq) ht

lemma moveAll_pairs {n b : ℕ} (row : List (Fin n)) (cs ds : List (Block n b)) (fresh fresh' : ℕ)
    (hs : Separate cs) (h : moveAll row cs fresh = some (ds,fresh')) :
    ds.map (fun c => (c.residual,c.moved)) =
      cs.map (fun c => moveRow row c.residual c.moved) := by
  induction row generalizing cs fresh with
  | nil => simp only [moveAll,Option.some.injEq,Prod.mk.injEq] at h; obtain ⟨rfl,rfl⟩ := h; rfl
  | cons v row ih =>
    obtain ⟨q,hq,ht⟩ := Option.bind_eq_some_iff.mp h
    have hsep := Separate.descends (moveOne_frame v cs q.1 fresh q.2 hq) hs
    rw [ih _ _ hsep ht]
    have hm := congrArg (List.map (fun p : List (Fin n) × List (Fin n) => moveRow row p.1 p.2))
      (moveOne_pairs v cs q.1 fresh q.2 hs hq)
    simp only [List.map_map,Function.comp_def] at hm
    rw [hm]
    apply List.map_congr_left
    intro c hc
    exact (moveRow_append [v] row c.residual c.moved).symm

/-- The emission reads only the two logical lists belonging to each provenance block. -/
lemma emit_pairs {n b : ℕ} (first : Bool) (cs : List (Block n b)) (hc : ∀ c ∈ cs, c.Valid) :
    (cs.flatMap (Block.emit first)).map Prod.snd =
      (cs.map (fun c => (c.residual,c.moved))).flatMap (fun q =>
        if first then nonemptyCell q.2 ++ nonemptyCell q.1 else nonemptyCell q.1 ++ nonemptyCell q.2) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons,List.map_append,List.map_cons]
    rw [c.emit_values first (hc c List.mem_cons_self),ih (fun c h => hc c (List.mem_cons_of_mem _ h))]

/-- Complete labeled-loop correctness, obtained from actual erase/append transitions.
Fresh IDs and companion tables cannot change the stable semantic partition produced. -/
theorem moveAll_refine {n b : ℕ} (first : Bool) (row : List (Fin n)) (cs ds : List (Block n b))
    (fresh fresh' : ℕ) (hs : Separate cs)
    (hclean : ∀ c ∈ cs, c.companion=none ∧ c.moved=[])
    (hr : row.Pairwise (· < ·)) (hc : ∀ c ∈ cs, c.residual.Pairwise (· < ·))
    (h : moveAll row cs fresh = some (ds,fresh')) :
    (ds.flatMap (Block.emit first)).map Prod.snd =
      refine first (fun v => decide (v ∈ row)) (cs.map Block.residual) := by
  have hv : ∀ c ∈ cs, c.Valid := by
    intro c hmem
    have he := hclean c hmem
    simp [Block.Valid,he.1,he.2]
  rw [emit_pairs first ds (moveAll_valid row cs ds fresh fresh' hv h),moveAll_pairs row cs ds fresh fresh' hs h]
  simp only [List.flatMap_map,refine]
  clear h hs hv
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons,List.map_cons]
    have hempty := (hclean c List.mem_cons_self).2
    rw [hempty,moveRow_refine first row c.residual hr (hc c List.mem_cons_self)]
    congr 1
    apply ih
    · exact fun c hc => hclean c (List.mem_cons_of_mem _ hc)
    · exact fun c hmem => hc c (List.mem_cons_of_mem _ hmem)

lemma moveOne_exists {n b : ℕ} (v : Fin n) (cs : List (Block n b)) (fresh : ℕ) (hf : fresh < b) :
    ∃ ds fresh', moveOne v cs fresh = some (ds,fresh') := by
  induction cs with
  | nil => exact ⟨[],fresh,rfl⟩
  | cons c cs ih =>
    by_cases hv : v ∈ c.residual
    · cases hb : c.companion with
      | none => exact ⟨c.advance v ⟨fresh,hf⟩::cs,fresh+1,by simp [moveOne,hv,hb,hf]⟩
      | some d => exact ⟨c.advance v d::cs,fresh,by simp [moveOne,hv,hb]⟩
    · obtain ⟨ds,fresh',h⟩ := ih
      exact ⟨c::ds,fresh',by simp [moveOne,hv,h]⟩

/-- Sufficient spare capacity is consumed at most once per actual row entry. -/
theorem moveAll_exists {n b : ℕ} (row : List (Fin n)) (cs : List (Block n b)) (fresh : ℕ)
    (hf : fresh+row.length ≤ b) : ∃ ds fresh', moveAll row cs fresh = some (ds,fresh') := by
  induction row generalizing cs fresh with
  | nil => exact ⟨cs,fresh,rfl⟩
  | cons v row ih =>
    have hf' : fresh < b := by simp only [List.length_cons] at hf; omega
    obtain ⟨mid,fmid,hm⟩ := moveOne_exists v cs fresh hf'
    have hcost := (moveOne_fresh v cs mid fresh fmid hm).2
    obtain ⟨ds,fresh',hd⟩ := ih mid fmid (by simp only [List.length_cons] at hf; omega)
    exact ⟨ds,fresh',by simp [moveAll,hm,hd]⟩

/-- Includes inactive old IDs as well: companions can never alias an earlier cell ID. -/
def Block.ids {n b : ℕ} (c : Block n b) : List (Fin b) := c.original::c.companion.toList

def ids {n b : ℕ} (cs : List (Block n b)) : List (Fin b) := cs.flatMap Block.ids

/-- The only ID-list change is insertion of the literal previous fresh cursor. -/
def IdChange {b : ℕ} (fresh fresh' : ℕ) (old new : List (Fin b)) : Prop :=
  (fresh'=fresh ∧ new=old) ∨ ∃ (hf : fresh < b) (left right : List (Fin b)),
    fresh'=fresh+1 ∧ old=left++right ∧ new=left++⟨fresh,hf⟩::right

lemma moveOne_ids {n b : ℕ} (v : Fin n) (cs ds : List (Block n b)) (fresh fresh' : ℕ)
    (h : moveOne v cs fresh = some (ds,fresh')) : IdChange fresh fresh' (ids cs) (ids ds) := by
  induction cs generalizing ds fresh fresh' with
  | nil => simp only [moveOne,Option.some.injEq,Prod.mk.injEq] at h; obtain ⟨rfl,rfl⟩ := h; exact Or.inl ⟨rfl,rfl⟩
  | cons c cs ih =>
    simp only [moveOne] at h
    split at h
    · cases hb : c.companion with
      | some d =>
        simp only [hb,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        exact Or.inl ⟨rfl,by simp [ids,Block.ids,Block.advance,hb]⟩
      | none =>
        simp only [hb] at h
        split at h
        next hf =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact Or.inr ⟨hf,[c.original],ids cs,rfl,
            by simp [ids,Block.ids,hb],by simp [ids,Block.ids,Block.advance,hb]⟩
        · contradiction
    · obtain ⟨q,hq,he⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      rcases ih _ _ _ hq with ⟨hf,he⟩ | ⟨hf,left,right,hfresh,hold,hnew⟩
      · exact Or.inl ⟨hf,by change c.ids++ids q.1 = c.ids++ids cs; rw [he]⟩
      · exact Or.inr ⟨hf,c.ids++left,right,hfresh,
          by change c.ids++ids cs = _; rw [hold,List.append_assoc],
          by change c.ids++ids q.1 = _; rw [hnew,List.append_assoc]⟩

/-- All original and allocated companion IDs are distinct and strictly below the free cursor. -/
def Addresses {n b : ℕ} (fresh : ℕ) (cs : List (Block n b)) : Prop :=
  (ids cs).Nodup ∧ ∀ i ∈ ids cs, i.val < fresh

lemma IdChange.preserves {b : ℕ} {fresh fresh' : ℕ} {old new : List (Fin b)}
    (h : IdChange fresh fresh' old new) (hn : old.Nodup) (hb : ∀ i ∈ old, i.val < fresh) :
    new.Nodup ∧ ∀ i ∈ new, i.val < fresh' := by
  rcases h with ⟨rfl,rfl⟩ | ⟨hf,left,right,rfl,rfl,rfl⟩
  · exact ⟨hn,hb⟩
  · obtain ⟨hl,hr,hcross⟩ := List.nodup_append.mp hn
    have hnleft : (⟨fresh,hf⟩ : Fin b) ∉ left := by
      intro h; exact (Nat.lt_irrefl fresh) (hb ⟨fresh,hf⟩ (List.mem_append_left _ h))
    have hnright : (⟨fresh,hf⟩ : Fin b) ∉ right := by
      intro h; exact (Nat.lt_irrefl fresh) (hb ⟨fresh,hf⟩ (List.mem_append_right _ h))
    constructor
    · refine List.nodup_append.mpr ⟨hl,List.nodup_cons.mpr ⟨hnright,hr⟩,?_⟩
      intro i hi j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact fun he => hnleft (he ▸ hi)
      · exact hcross i hi j hj
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact (hb i (List.mem_append_left _ hi)).trans (Nat.lt_succ_self _)
      · rcases List.mem_cons.mp hi with rfl | hi
        · exact Nat.lt_succ_self _
        · exact (hb i (List.mem_append_right _ hi)).trans (Nat.lt_succ_self _)

lemma moveOne_addresses {n b : ℕ} (v : Fin n) (cs ds : List (Block n b)) (fresh fresh' : ℕ)
    (ha : Addresses fresh cs) (h : moveOne v cs fresh = some (ds,fresh')) : Addresses fresh' ds :=
  (moveOne_ids v cs ds fresh fresh' h).preserves ha.1 ha.2

lemma moveAll_addresses {n b : ℕ} (row : List (Fin n)) (cs ds : List (Block n b)) (fresh fresh' : ℕ)
    (ha : Addresses fresh cs) (h : moveAll row cs fresh = some (ds,fresh')) : Addresses fresh' ds := by
  induction row generalizing cs fresh with
  | nil => simp only [moveAll,Option.some.injEq,Prod.mk.injEq] at h; obtain ⟨rfl,rfl⟩ := h; exact ha
  | cons v row ih =>
    obtain ⟨q,hq,ht⟩ := Option.bind_eq_some_iff.mp h
    exact ih _ _ (moveOne_addresses v cs q.1 fresh q.2 ha hq) ht

/-- An original-ID bound survives even after its old live cell becomes empty. -/
lemma moveOne_original_bound {n b : ℕ} (v : Fin n) (cs ds : List (Block n b)) (fresh fresh' base : ℕ)
    (hb : ∀ c ∈ cs, c.original.val < base) (h : moveOne v cs fresh = some (ds,fresh')) :
    ∀ d ∈ ds, d.original.val < base := by
  intro d hd
  obtain ⟨c,hc,hcd⟩ := forall₂_mem_right (moveOne_frame v cs ds fresh fresh' h) hd
  rw [← hcd.1]
  exact hb c hc

lemma Block.emit_ids {n b : ℕ} (first : Bool) (c : Block n b) (hc : c.Valid) :
    (c.emit first).map Prod.fst =
      if first then c.companion.toList ++ (if c.residual=[] then [] else [c.original]) else
        (if c.residual=[] then [] else [c.original]) ++ c.companion.toList := by
  cases hb : c.companion with
  | none =>
    have hm : c.moved=[] := hc.mp hb
    cases first <;> by_cases he : c.residual=[] <;> simp [Block.emit,namedCell,hb,hm,he]
  | some d =>
    have hm : c.moved≠[] := fun h => by have := hc.mpr h; simp [hb] at this
    cases first <;> by_cases he : c.residual=[] <;> simp [Block.emit,namedCell,hb,hm,he]

lemma Block.emit_ids_existing {n b : ℕ} (first : Bool) (c : Block n b) (v : Fin n) (d : Fin b)
    (hc : c.Valid) (hb : c.companion=some d) (hv : v ∈ c.residual) :
    (c.emit first).map Prod.fst = if first then [d,c.original] else [c.original,d] := by
  have he : c.residual≠[] := List.ne_nil_of_mem hv
  rw [c.emit_ids first hc]
  cases first <;> simp [hb,he]

lemma Block.advance_existing_ids {n b : ℕ} (first : Bool) (c : Block n b) (v : Fin n) (d : Fin b)
    (hb : c.companion=some d) :
    ((c.advance v d).emit first).map Prod.fst =
      if c.residual.erase v=[] then [d] else
        if first then [d,c.original] else [c.original,d] := by
  rw [(c.advance v d).emit_ids first (c.advance_valid v d)]
  by_cases he : c.residual.erase v=[] <;> cases first <;> simp [Block.advance,hb,he]

lemma Block.emit_ids_new {n b : ℕ} (first : Bool) (c : Block n b) (v : Fin n)
    (hc : c.Valid) (hb : c.companion=none) (hv : v ∈ c.residual) :
    (c.emit first).map Prod.fst = [c.original] := by
  have he : c.residual≠[] := List.ne_nil_of_mem hv
  rw [c.emit_ids first hc]
  cases first <;> simp [hb,he]

lemma Block.advance_new_ids {n b : ℕ} (first : Bool) (c : Block n b) (v : Fin n) (d : Fin b)
    (hb : c.companion=none) :
    ((c.advance v d).emit first).map Prod.fst =
      if c.residual.erase v=[] then [d] else
        if first then [d,c.original] else [c.original,d] := by
  rw [(c.advance v d).emit_ids first (c.advance_valid v d)]
  by_cases he : c.residual.erase v=[] <;> cases first <;> simp [Block.advance,hb,he]

lemma emit_ids_frame {n b : ℕ} (first : Bool) (left right : List (Block n b)) (c : Block n b) :
    ((left++c::right).flatMap (Block.emit first)).map Prod.fst =
      (left.flatMap (Block.emit first)).map Prod.fst ++
        (c.emit first).map Prod.fst ++ (right.flatMap (Block.emit first)).map Prod.fst := by
  simp [List.append_assoc]

/-- Increasing row order restores both per-block cell orders at the pivot boundary. -/
lemma moveAll_sorted {n b : ℕ} (row : List (Fin n)) (cs ds : List (Block n b)) (fresh fresh' : ℕ)
    (hs : Separate cs) (hm : ∀ c ∈ cs, c.moved=[])
    (hr : row.Pairwise (· < ·)) (hc : ∀ c ∈ cs, c.residual.Pairwise (· < ·))
    (h : moveAll row cs fresh = some (ds,fresh')) :
    ∀ d ∈ ds, d.residual.Pairwise (· < ·) ∧ d.moved.Pairwise (· < ·) := by
  intro d hd
  have hin : (d.residual,d.moved) ∈ ds.map (fun c => (c.residual,c.moved)) :=
    List.mem_map.mpr ⟨d,hd,rfl⟩
  rw [moveAll_pairs row cs ds fresh fresh' hs h] at hin
  obtain ⟨c,hc',he⟩ := List.mem_map.mp hin
  rw [hm c hc',moveRow_spec row c.residual [] hr.nodup (hc c hc').nodup] at he
  have her := congrArg Prod.fst he
  have hem := congrArg Prod.snd he
  simp only [List.nil_append] at her hem
  rw [← her,← hem]
  exact ⟨(hc c hc').filter _,hr.filter _⟩

end HiddenCircuits.DH.LexBFSLabeled

