import HiddenCircuits.DH.LexBFSModel

/-! Intrusive linked-list primitives used by stable ordered partition refinement.
The executable stores are finite arrays; list values occur only in refinement predicates. -/
namespace HiddenCircuits.DH.LexBFSLinks

abbrev Pointer (n : ℕ) := Option (Fin n)
abbrev Store (n : ℕ) := Vector (Pointer n) n

/-- A null pointer does not name a memory location. -/
def write {n : ℕ} (a : Store n) (p : Pointer n) (v : Pointer n) : Store n :=
  match p with
  | none => a
  | some i => a.set i.val v

@[simp] lemma write_none {n : ℕ} (a : Store n) (v : Pointer n) : write a none v = a := rfl
@[simp] lemma write_some {n : ℕ} (a : Store n) (i : Fin n) (v : Pointer n) :
    (write a (some i) v)[i.val] = v := by simp [write]
lemma write_other {n : ℕ} (a : Store n) (p v : Pointer n) (i : Fin n)
    (hi : p ≠ some i) : (write a p v)[i.val] = a[i.val] := by
  cases p with
  | none => rfl
  | some j => have hji : j.val ≠ i.val := fun h => hi (congrArg some (Fin.ext h))
              simp [write,hji]

/-- Each list element names one array cell, whose successor is the following element.
The final successor may name an external boundary or be null. -/
def Forward {n : ℕ} (a : Store n) : List (Fin n) → Pointer n → Prop
  | [],_ => True
  | v::vs,r => a[v.val] = vs.head?.or r ∧ Forward a vs r

lemma Forward.congr {n : ℕ} {a b : Store n} {xs : List (Fin n)} {r : Pointer n}
    (h : Forward a xs r) (he : ∀ v ∈ xs, b[v.val] = a[v.val]) : Forward b xs r := by
  induction xs with
  | nil => trivial
  | cons v vs ih =>
    exact ⟨(he v List.mem_cons_self).trans h.1,
      ih h.2 (fun w hw => he w (List.mem_cons_of_mem _ hw))⟩

lemma head_append {n : ℕ} (xs ys : List (Fin n)) (r : Pointer n) :
    (xs++ys).head?.or r = xs.head?.or (ys.head?.or r) := by cases xs <;> rfl

lemma Forward.append {n : ℕ} {a : Store n} (xs ys : List (Fin n)) (r : Pointer n) :
    Forward a (xs++ys) r ↔ Forward a xs (ys.head?.or r) ∧ Forward a ys r := by
  induction xs with
  | nil => simp [Forward]
  | cons v vs ih => simp only [List.cons_append,Forward,head_append,ih,and_assoc]

lemma Forward.write_frame {n : ℕ} {a : Store n} {xs : List (Fin n)} {r p v : Pointer n}
    (h : Forward a xs r) (hp : ∀ x ∈ xs, p ≠ some x) : Forward (write a p v) xs r :=
  h.congr (fun x hx => write_other a p v x (hp x hx))

/-- Retarget the one final link of a duplicate-free segment. -/
lemma Forward.retarget {n : ℕ} {a : Store n} {xs : List (Fin n)} {r s : Pointer n}
    (h : Forward a xs r) (hn : xs.Nodup) :
    Forward (write a xs.getLast? s) xs s := by
  induction xs with
  | nil => trivial
  | cons v vs ih =>
    cases vs with
    | nil => simp [Forward,write]
    | cons w ws =>
      have hv : (w::ws).getLast? ≠ some v := by
        intro he
        exact (List.nodup_cons.mp hn).1 (List.mem_of_getLast? he)
      refine ⟨?_,ih h.2 (List.nodup_cons.mp hn).2⟩
      simpa [List.getLast?_cons_cons,write_other a _ s v hv] using h.1

/-- Removing a named node only changes its predecessor's forward link. -/
lemma Forward.remove {n : ℕ} {a : Store n} (pre post : List (Fin n)) (v : Fin n)
    (h : Forward a (pre++v::post) none) (hn : (pre++v::post).Nodup) :
    Forward (write a pre.getLast? post.head?) (pre++post) none := by
  have hp := (Forward.append pre (v::post) none).mp h
  have hnd := List.nodup_append.mp hn
  apply (Forward.append pre post none).mpr
  constructor
  · simpa using hp.1.retarget hnd.1
  · apply hp.2.2.write_frame
    intro x hx he
    have hm : x ∈ pre := List.mem_of_getLast? he
    exact hnd.2.2 x hm x (List.mem_cons_of_mem _ hx) rfl

/-- Literal two-array doubly linked storage. -/
structure Links (n : ℕ) where
  next : Store n
  prev : Store n

/-- Unlink one live node using two pointer reads and at most two array writes. -/
def unlink {n : ℕ} (a : Links n) (v : Fin n) : Links n :=
  let before := a.prev[v.val]
  let after := a.next[v.val]
  ⟨write a.next before after,write a.prev after before⟩

/-- The semantic list is a ghost: it is not stored or traversed by `unlink`. -/
def Realizes {n : ℕ} (a : Links n) (xs : List (Fin n)) : Prop :=
  Forward a.next xs none ∧ Forward a.prev xs.reverse none

lemma Forward.at {n : ℕ} {a : Store n} (pre post : List (Fin n)) (v : Fin n)
    (h : Forward a (pre++v::post) none) : a[v.val] = post.head? := by
  simpa using ((Forward.append pre (v::post) none).mp h).2.1

/-- Exact removal theorem for the executable direct-pointer primitive. -/
theorem unlink_realizes {n : ℕ} {a : Links n} (pre post : List (Fin n)) (v : Fin n)
    (h : Realizes a (pre++v::post)) (hn : (pre++v::post).Nodup) :
    Realizes (unlink a v) (pre++post) := by
  have hf := h.1.at pre post v
  have hr : Forward a.prev (post.reverse++v::pre.reverse) none := by
    simpa [List.reverse_append,List.reverse_cons,List.append_assoc] using h.2
  have hb := hr.at post.reverse pre.reverse v
  simp only [List.head?_reverse] at hb
  constructor
  · simpa only [unlink,hf,hb] using h.1.remove pre post v hn
  · have hnr : (post.reverse++v::pre.reverse).Nodup := by
      simpa [List.reverse_append,List.reverse_cons,List.append_assoc] using (List.nodup_reverse.mpr hn)
    have hh := hr.remove post.reverse pre.reverse v hnr
    simpa only [unlink,hf,hb,List.getLast?_reverse,List.head?_reverse,List.reverse_append] using hh

/-- Insert a fresh node between two known adjacent boundary pointers. -/
def insert {n : ℕ} (a : Links n) (left right : Pointer n) (v : Fin n) : Links n :=
  ⟨write (a.next.set v.val right) left (some v),
   write (a.prev.set v.val left) right (some v)⟩

lemma Forward.set_frame {n : ℕ} {a : Store n} {xs : List (Fin n)} {r s : Pointer n}
    (h : Forward a xs r) (v : Fin n) (hv : v ∉ xs) :
    Forward (a.set v.val s) xs r := by
  apply h.congr
  intro x hx
  have hne : v.val ≠ x.val := fun he => hv (Fin.ext he ▸ hx)
  simp [hne]

lemma Forward.insert {n : ℕ} {a : Store n} (pre post : List (Fin n)) (v : Fin n)
    (h : Forward a (pre++post) none) (hn : (pre++post).Nodup)
    (hv : v ∉ pre++post) :
    Forward (write (a.set v.val post.head?) pre.getLast? (some v))
      (pre++v::post) none := by
  have hp := (Forward.append pre post none).mp h
  have hnd := List.nodup_append.mp hn
  have hvp : v ∉ pre := fun hm => hv (List.mem_append_left _ hm)
  have hvt : v ∉ post := fun hm => hv (List.mem_append_right _ hm)
  apply (Forward.append pre (v::post) none).mpr
  constructor
  · simpa using (hp.1.set_frame v hvp).retarget (s := some v) hnd.1
  · constructor
    · have hnlast : pre.getLast? ≠ some v := fun he => hvp (List.mem_of_getLast? he)
      simp [write_other _ _ _ v hnlast]
    · apply (hp.2.set_frame v hvt).write_frame
      intro x hx he
      exact hnd.2.2 x (List.mem_of_getLast? he) x hx rfl

/-- The insertion primitive has the exact stable list effect, with no scan or copied list. -/
theorem insert_realizes {n : ℕ} {a : Links n} (pre post : List (Fin n)) (v : Fin n)
    (h : Realizes a (pre++post)) (hn : (pre++post).Nodup) (hv : v ∉ pre++post) :
    Realizes (insert a pre.getLast? post.head? v) (pre++v::post) := by
  constructor
  · exact h.1.insert pre post v hn hv
  · have hr : Forward a.prev (post.reverse++pre.reverse) none := by
      simpa [List.reverse_append] using h.2
    have hnr : (post.reverse++pre.reverse).Nodup := by
      simpa [List.reverse_append] using (List.nodup_reverse.mpr hn)
    have hvr : v ∉ post.reverse++pre.reverse := by simpa [List.mem_append,or_comm] using hv
    simpa only [insert,List.head?_reverse,List.getLast?_reverse,
      List.reverse_append,List.reverse_cons,List.append_assoc] using
      hr.insert post.reverse pre.reverse v hnr hvr

/-- At most one actual memory write is performed by a nullable pointer write. -/
def writeAccesses {n : ℕ} : Pointer n → ℕ
  | none => 0
  | some _ => 1

lemma writeAccesses_le {n : ℕ} (p : Pointer n) : writeAccesses p ≤ 1 := by cases p <;> simp [writeAccesses]

/-- Two reads and the two nullable writes are the entire unlink operation. -/
def unlinkAccesses {n : ℕ} (a : Links n) (v : Fin n) : ℕ :=
  2 + writeAccesses a.prev[v.val] + writeAccesses a.next[v.val]

lemma unlinkAccesses_le {n : ℕ} (a : Links n) (v : Fin n) : unlinkAccesses a v ≤ 4 := by
  have h₁ := writeAccesses_le a.prev[v.val]
  have h₂ := writeAccesses_le a.next[v.val]
  unfold unlinkAccesses
  omega

/-- Fresh-node insertion writes its two fields and at most two neighboring fields. -/
def insertAccesses {n : ℕ} (left right : Pointer n) : ℕ :=
  2 + writeAccesses left + writeAccesses right

lemma insertAccesses_le {n : ℕ} (left right : Pointer n) : insertAccesses left right ≤ 4 := by
  have h₁ := writeAccesses_le left
  have h₂ := writeAccesses_le right
  unfold insertAccesses
  omega

lemma Realizes.congr {n : ℕ} {a b : Links n} {xs : List (Fin n)}
    (h : Realizes a xs) (hn : ∀ v ∈ xs, b.next[v.val] = a.next[v.val])
    (hp : ∀ v ∈ xs, b.prev[v.val] = a.prev[v.val]) : Realizes b xs :=
  ⟨h.1.congr hn,h.2.congr (fun v hv => hp v (List.mem_reverse.mp hv))⟩

/-- Pointer updates leave every disjoint linked list unchanged. -/
lemma unlink_frame {n : ℕ} {a : Links n} {xs : List (Fin n)} (v : Fin n)
    (h : Realizes a xs)
    (hp : ∀ x ∈ xs, a.prev[v.val] ≠ some x)
    (hn : ∀ x ∈ xs, a.next[v.val] ≠ some x) : Realizes (unlink a v) xs := by
  apply h.congr
  · intro x hx
    exact write_other _ _ _ x (hp x hx)
  · intro x hx
    exact write_other _ _ _ x (hn x hx)

lemma insert_frame {n : ℕ} {a : Links n} {xs : List (Fin n)} (v : Fin n)
    (left right : Pointer n) (h : Realizes a xs) (hv : v ∉ xs)
    (hl : ∀ x ∈ xs, left ≠ some x) (hr : ∀ x ∈ xs, right ≠ some x) :
    Realizes (insert a left right v) xs := by
  apply h.congr
  · intro x hx
    have hne : v.val ≠ x.val := fun he => hv (Fin.ext he ▸ hx)
    change (write _ left _)[x.val] = _
    rw [write_other _ _ _ x (hl x hx)]
    simp [hne]
  · intro x hx
    have hne : v.val ≠ x.val := fun he => hv (Fin.ext he ▸ hx)
    change (write _ right _)[x.val] = _
    rw [write_other _ _ _ x (hr x hx)]
    simp [hne]

end HiddenCircuits.DH.LexBFSLinks
