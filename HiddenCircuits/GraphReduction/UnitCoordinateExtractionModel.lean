import HiddenCircuits.GraphReduction.UnitIntervalIntegerExtraction

/-! Bounded natural-number constraint relaxation for coordinate extraction.
The bound is used only in the proof and to choose a fixed polynomial clock;
no coordinate or algorithm certificate is an input to the evaluator. -/
namespace HiddenCircuits.GraphReduction.UnitCoordinateExtraction

abbrev Coordinates (n : ℕ) := Fin n → ℕ

/-- Relax the two inequalities for an earlier/later pair. -/
def pair {n : ℕ} (D : ℕ) (edge : Bool) (u v : Fin n) (x : Coordinates n) : Coordinates n :=
  if edge then Function.update (Function.update x v (max (x v) (x u))) u
    (max (x u) (x v-D))
  else Function.update x v (max (x v) (x u+D+1))

lemma pair_inflationary {n : ℕ} (D : ℕ) (edge : Bool) (u v : Fin n) (x : Coordinates n) :
    x ≤ pair D edge u v x := by
  intro w
  cases edge <;> simp only [pair,Bool.false_eq_true,ite_false,ite_true]
  all_goals by_cases hw : w=u <;> by_cases hv : w=v <;> simp_all [Function.update_apply]

lemma pair_monotone {n : ℕ} (D : ℕ) (edge : Bool) (u v : Fin n) :
    Monotone (pair D edge u v) := by
  intro x y h
  have hu := h u
  have hv := h v
  cases edge with
  | false =>
    apply update_le_update_iff.mpr
    exact ⟨max_le_max hv (Nat.add_le_add_right (Nat.add_le_add_right hu D) 1),fun i _=>h i⟩
  | true =>
    apply update_le_update_iff.mpr
    refine ⟨max_le_max hu (Nat.sub_le_sub_right hv D),?_⟩
    have hh : Function.update x v (max (x v) (x u)) ≤
        Function.update y v (max (y v) (y u)) :=
      update_le_update_iff.mpr ⟨max_le_max hv hu,fun j _=>h j⟩
    exact fun i _=>hh i

lemma pair_fixed_iff {n : ℕ} (D : ℕ) (edge : Bool) (u v : Fin n) (hne : u≠v)
    (x : Coordinates n) :
    pair D edge u v x=x ↔ x u≤x v ∧
      (if edge then x v≤x u+D else x u+D<x v) := by
  cases edge with
  | false =>
    simp only [pair,Bool.false_eq_true,ite_false]
    constructor
    · intro h
      have hv := congrFun h v
      simp only [Function.update_self] at hv
      have hh := le_max_right (x v) (x u+D+1)
      rw [hv] at hh
      omega
    · rintro ⟨_,h⟩
      have he : max (x v) (x u+D+1)=x v := max_eq_left (by omega)
      rw [he,Function.update_eq_self]
  | true =>
    simp only [pair,ite_true]
    constructor
    · intro h
      have hu := congrFun h u
      have hv := congrFun h v
      simp only [Function.update_self,Function.update_of_ne hne.symm] at hu hv
      have h1 := le_max_right (x v) (x u)
      have h2 := le_max_right (x u) (x v-D)
      rw [hv] at h1
      rw [hu] at h2
      omega
    · rintro ⟨h1,h2⟩
      rw [max_eq_left h1,max_eq_left (show x v-D≤x u by omega),
        Function.update_eq_self,Function.update_eq_self]

def pairs {n : ℕ} : List (Fin n) → List (Fin n × Fin n)
  | [] => []
  | u::us => us.map (fun v=>(u,v)) ++ pairs us

def inner {n : ℕ} (D : ℕ) (edge : Fin n → Fin n → Bool) (u : Fin n) :
    List (Fin n) → Coordinates n → Coordinates n
  | [],x => x
  | v::vs,x => inner D edge u vs (pair D (edge u v) u v x)

def scan {n : ℕ} (D : ℕ) (edge : Fin n → Fin n → Bool) :
    List (Fin n) → Coordinates n → Coordinates n
  | [],x => x
  | u::us,x => scan D edge us (inner D edge u us x)

def run {n : ℕ} (D : ℕ) (edge : Fin n → Fin n → Bool) (ls : List (Fin n)) :
    ℕ → Coordinates n → Coordinates n
  | 0,x => x
  | k+1,x => run D edge ls k (scan D edge ls x)

lemma inner_foldl {n : ℕ} (D : ℕ) (edge : Fin n → Fin n → Bool)
    (u : Fin n) (vs : List (Fin n)) (x : Coordinates n) :
    inner D edge u vs x = (vs.map (fun v=>(u,v))).foldl
      (fun y p=>pair D (edge p.1 p.2) p.1 p.2 y) x := by
  induction vs generalizing x with
  | nil => rfl
  | cons v vs ih => simpa [inner] using ih (pair D (edge u v) u v x)

lemma scan_foldl {n : ℕ} (D : ℕ) (edge : Fin n → Fin n → Bool)
    (ls : List (Fin n)) (x : Coordinates n) :
    scan D edge ls x = (pairs ls).foldl
      (fun y p=>pair D (edge p.1 p.2) p.1 p.2 y) x := by
  induction ls generalizing x with
  | nil => rfl
  | cons u us ih => rw [scan,ih,pairs,List.foldl_append,inner_foldl]

section Inflationary
variable {α β : Type*} [PartialOrder α] (step : β → α → α)
variable (hstep : ∀ b x,x≤step b x)
include hstep

lemma fold_inflationary (bs : List β) (x : α) :
    x≤bs.foldl (fun x b=>step b x) x := by
  induction bs generalizing x with
  | nil => exact le_rfl
  | cons b bs ih => exact (hstep b x).trans (ih (step b x))

lemma fold_fixed_iff (bs : List β) (x : α) :
    bs.foldl (fun x b=>step b x) x=x ↔ ∀b∈bs,step b x=x := by
  induction bs generalizing x with
  | nil => simp
  | cons b bs ih =>
    constructor
    · intro h
      have hb : step b x=x := le_antisymm (by
        have hh := fold_inflationary step hstep bs (step b x)
        change bs.foldl (fun x b=>step b x) (step b x)=x at h
        rwa [h] at hh) (hstep b x)
      have ht : bs.foldl (fun x b=>step b x) x=x := by simpa [hb] using h
      simpa only [List.mem_cons,forall_eq_or_imp] using And.intro hb ((ih x).mp ht)
    · intro h
      have hb := h b (by simp)
      have ht := (ih x).mpr (fun c hc=>h c (by simp [hc]))
      simpa [List.foldl_cons,hb] using ht
end Inflationary

lemma scan_inflationary {n : ℕ} (D : ℕ) (edge : Fin n → Fin n → Bool)
    (ls : List (Fin n)) (x : Coordinates n) : x≤scan D edge ls x := by
  rw [scan_foldl]
  exact fold_inflationary _ (fun (p : Fin n × Fin n) y=>pair_inflationary D (edge p.1 p.2) p.1 p.2 y) _ _

lemma scan_fixed_iff {n : ℕ} (D : ℕ) (edge : Fin n → Fin n → Bool)
    (ls : List (Fin n)) (x : Coordinates n) :
    scan D edge ls x=x ↔ ∀p∈pairs ls,pair D (edge p.1 p.2) p.1 p.2 x=x := by
  rw [scan_foldl]
  exact fold_fixed_iff _ (fun (p : Fin n × Fin n) y=>pair_inflationary D (edge p.1 p.2) p.1 p.2 y) _ _

lemma inner_le_witness {n : ℕ} (D : ℕ) (edge : Fin n → Fin n → Bool)
    (u : Fin n) (vs : List (Fin n)) (x z : Coordinates n) (hx : x≤z)
    (hz : ∀v∈vs,pair D (edge u v) u v z=z) : inner D edge u vs x≤z := by
  induction vs generalizing x with
  | nil => exact hx
  | cons v vs ih =>
    apply ih
    · calc pair D (edge u v) u v x ≤ pair D (edge u v) u v z := pair_monotone D _ _ _ hx
           _ = z := hz v (by simp)
    · exact fun w hw=>hz w (by simp [hw])

lemma scan_le_witness {n : ℕ} (D : ℕ) (edge : Fin n → Fin n → Bool)
    (ls : List (Fin n)) (x z : Coordinates n) (hx : x≤z)
    (hz : ∀p∈pairs ls,pair D (edge p.1 p.2) p.1 p.2 z=z) : scan D edge ls x≤z := by
  induction ls generalizing x with
  | nil => exact hx
  | cons u us ih =>
    apply ih
    · exact inner_le_witness D edge u us x z hx (fun v hv=>hz (u,v) (by simp [pairs,hv]))
    · exact fun p hp=>hz p (by simp [pairs,hp])

lemma run_le_witness {n : ℕ} (D : ℕ) (edge : Fin n → Fin n → Bool)
    (ls : List (Fin n)) (k : ℕ) (x z : Coordinates n) (hx : x≤z)
    (hz : ∀p∈pairs ls,pair D (edge p.1 p.2) p.1 p.2 z=z) : run D edge ls k x≤z := by
  induction k generalizing x with
  | zero => exact hx
  | succ k ih => exact ih _ (scan_le_witness D edge ls x z hx hz)

end HiddenCircuits.GraphReduction.UnitCoordinateExtraction
