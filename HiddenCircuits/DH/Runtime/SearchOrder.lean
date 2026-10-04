import HiddenCircuits.DH.Runtime.PruningModel

/-! First-success preservation in the literal nested pair loops. -/
namespace HiddenCircuits.DH.Runtime.SearchOrder

 def first {α β : Type*} (f : α→Option β) : List α→Option β
  | [] => none
  | a::as => (f a).orElse (fun _=>first f as)

 lemma first_append {α β : Type*} (f : α→Option β) (xs ys : List α) :
    first f (xs++ys)=(first f xs).orElse (fun _=>first f ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [first,h,ih]

 lemma fold_preserves {α β : Type*} (f : α→Option β) (xs : List α) (result : β) :
    xs.foldl (fun old x=>old.orElse (fun _=>f x)) (some result)=some result := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

 lemma first_fold {α β : Type*} (f : α→Option β) (xs : List α) (initial : Option β) :
    xs.foldl (fun old x=>old.orElse (fun _=>f x)) initial=
      initial.orElse (fun _=>first f xs) := by
  cases initial with
  | some result => exact fold_preserves f xs result
  | none =>
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      cases h : f x with
      | none => simpa [first,List.foldl_cons,h] using ih
      | some result => simpa [first,List.foldl_cons,h] using fold_preserves f xs result

 lemma first_map {α β γ : Type*} (f : β→Option γ) (g : α→β) (xs : List α) :
    first f (xs.map g)=first (fun x=>f (g x)) xs := by
  induction xs <;> simp [first, *]

 lemma first_flatMap {α β γ : Type*} (f : β→Option γ) (g : α→List β) (xs : List α) :
    first f (xs.flatMap g)=first (fun x=>first f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,first_append,ih,first]

 /-- A physical row/column traversal with a retained first answer is exactly
row-major first-success search, for any predicate and every matrix payload. -/
 theorem nested_first {α β γ : Type*} (f : α→β→Option γ) (xs : List α) (ys : List β)
    (initial : Option γ) :
    xs.foldl (fun old x=>ys.foldl (fun out y=>out.orElse (fun _=>f x y)) old) initial =
      initial.orElse (fun _=>first (fun xy : α×β=>f xy.1 xy.2)
        (xs.flatMap (fun x=>ys.map (fun y=>(x,y))))) := by
  simp_rw [first_fold,first_flatMap,first_map]

 lemma first_some {α β : Type*} (f : α→Option β) (xs : List α) {b : β} (h : first f xs=some b) :
    ∃a∈xs, f a=some b := by
  induction xs with
  | nil => simp [first] at h
  | cons a xs ih =>
    cases he : f a with
    | none =>
      obtain ⟨a',ha',he'⟩ := ih (by simpa [first,he] using h)
      exact ⟨a',List.mem_cons_of_mem _ ha',he'⟩
    | some b' =>
      have hb : b'=b := by simpa [first,he] using h
      exact ⟨a,List.mem_cons_self,by simpa only [hb] using he⟩

 lemma scan_eq_first {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (alive : Vector Bool n) (pairs : List (Fin n×Fin n)) :
    PruningModel.scan G alive pairs=first (fun uv=>PruningModel.tryPair G alive uv.1 uv.2) pairs := by
  induction pairs with
  | nil => rfl
  | cons uv pairs ih => simp only [PruningModel.scan,first,ih]

 theorem nested_find {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (alive : Vector Bool n) :
    (List.finRange n).foldl (fun old u=>(List.finRange n).foldl
      (fun out v=>out.orElse (fun _=>PruningModel.tryPair G alive u v)) old) none =
      PruningModel.find G alive := by
  rw [nested_first]
  change first (fun uv=>PruningModel.tryPair G alive uv.1 uv.2) (PruningModel.candidates n)=_
  exact (scan_eq_first G alive _).symm

end HiddenCircuits.DH.Runtime.SearchOrder
