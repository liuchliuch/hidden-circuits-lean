import HiddenCircuits.GraphReduction.UnitIntervalMaskedScan

/-! Literal length-n Boolean-list masks, with exact fixed-universe count and
first-argmax semantics. This is the list interface consumed by the bit machine. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalBitMasks
open UnitIntervalGreedy
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def read (mask : List Bool) (v : Fin n) : Bool := mask[v.val]?.getD false
def active (mask : List Bool) : Finset (Fin n) := Finset.univ.filter (fun v => read mask v)
def members (mask : List Bool) : List (Fin n) := (List.finRange n).filter (read mask)
def count (mask : List Bool) : ℕ := (List.finRange n).countP (read mask)
def score (mask : List Bool) (v : Fin n) : ℕ :=
  (List.finRange n).countP (fun w => read mask w && decide (ClosedAdj G v w))
def priority (alive selected : List Bool) (v : Fin n) : ℕ :=
  (count (n:=n) alive+1)*score G selected v + (count (n:=n) alive-score G alive v)
/-- First maximum in ascending vertex-label order. -/
def choose (alive selected remaining : List Bool) : Option (Fin n) :=
  (members remaining).argmax (priority G alive selected)

def set (mask : List Bool) (v : Fin n) (value : Bool) : List Bool := mask.set v.val value

def ofFinset (S : Finset (Fin n)) : List Bool := List.ofFn (fun v => decide (v ∈ S))

lemma sorted_filter (p : Fin n → Bool) :
    (Finset.univ.filter (fun v => p v)).sort (· ≤ ·) = (List.finRange n).filter p := by
  apply (Finset.univ.filter (fun v => p v)).sortedLT_sort.eq_of_mem_iff (((List.sortedLT_finRange n).pairwise.filter p).sortedLT)
  intro v
  simp

lemma count_filter_card (p : Fin n → Bool) :
    (List.finRange n).countP p = (Finset.univ.filter (fun v => p v)).card := by
  have h := congrArg List.length (sorted_filter p)
  simpa only [Finset.length_sort,←List.countP_eq_length_filter] using h.symm

lemma members_eq_sort (mask : List Bool) : members (n:=n) mask = (active mask).sort (· ≤ ·) :=
  (sorted_filter _).symm
lemma count_eq_card (mask : List Bool) : count (n:=n) mask = (active (n:=n) mask).card := count_filter_card _

lemma score_eq (mask : List Bool) (v : Fin n) : score G mask v = UnitIntervalGreedy.score G (active mask) v := by
  rw [score,count_filter_card]
  unfold UnitIntervalGreedy.score UnitIntervalGreedy.neighbors active
  congr 1
  ext w
  simp [Bool.and_eq_true]

lemma priority_eq (alive selected : List Bool) (v : Fin n) :
    priority G alive selected v = UnitIntervalMaskedScan.priority G (active alive) (active selected) v := by
  simp only [priority,UnitIntervalMaskedScan.priority,count_eq_card,score_eq]

lemma choose_eq (alive selected remaining : List Bool) :
    choose G alive selected remaining =
      UnitIntervalMaskedScan.choose G (active alive) (active selected) (active remaining) := by
  simp only [choose,UnitIntervalMaskedScan.choose,members_eq_sort]
  congr 1
  funext v
  exact priority_eq G alive selected v

@[simp] lemma ofFinset_length (S : Finset (Fin n)) : (ofFinset S).length = n := by simp [ofFinset]
@[simp] lemma active_ofFinset (S : Finset (Fin n)) : active (ofFinset S) = S := by
  ext v
  simp [active,ofFinset,read,List.getElem?_ofFn,v.isLt]
@[simp] lemma set_length (mask : List Bool) (v : Fin n) (value : Bool) : (set mask v value).length = mask.length := by
  simp [set]

lemma read_set (mask : List Bool) (hm : mask.length = n) (v w : Fin n) (value : Bool) :
    read (set mask v value) w = if w=v then value else read mask w := by
  by_cases h : w=v
  · subst w
    have hv : v.val < mask.length := by rw [hm]; exact v.isLt
    simp [read,set,List.getElem?_set_self hv]
  · have hvw : v.val ≠ w.val := fun he => h (Fin.ext he.symm)
    simp [read,set,List.getElem?_set_ne hvw,h]

lemma active_set_true (mask : List Bool) (hm : mask.length = n) (v : Fin n) :
    active (set mask v true) = insert v (active mask) := by
  ext w
  simp only [active,Finset.mem_filter,Finset.mem_univ,true_and,read_set mask hm,
    Finset.mem_insert]
  by_cases h : w=v <;> simp [h]
lemma active_set_false (mask : List Bool) (hm : mask.length = n) (v : Fin n) :
    active (set mask v false) = (active mask).erase v := by
  ext w
  simp only [active,Finset.mem_filter,Finset.mem_univ,true_and,read_set mask hm,
    Finset.mem_erase]
  by_cases h : w=v <;> simp [h]

/-- All masks are literal Boolean lists; selected labels are literal Fin n values. -/
structure State (n : ℕ) where
  order : List (Fin n)
  selected : List Bool
  remaining : List Bool

def run (alive : List Bool) : ℕ → State n → State n
  | 0,s => s
  | fuel+1,s =>
    match choose G alive s.selected s.remaining with
    | none => s
    | some y => if score G s.selected y = 0 then s else
        run alive fuel ⟨s.order++[y],set s.selected y true,set s.remaining y false⟩

/-- Exact refinement to the finite-set component scan, including every mask
update and deterministic tie. -/
theorem run_refines (alive : List Bool) (fuel : ℕ) (s : State n)
    (hs : s.selected.length = n) (hr : s.remaining.length = n)
    (hi : active s.selected = s.order.toFinset) :
    (run G alive fuel s).selected.length = n ∧
    (run G alive fuel s).remaining.length = n ∧
    active (run G alive fuel s).selected = (run G alive fuel s).order.toFinset ∧
    ((run G alive fuel s).order,active (run G alive fuel s).remaining) =
      UnitIntervalMaskedScan.run G (active alive) fuel s.order (active s.remaining) := by
  induction fuel generalizing s with
  | zero => exact ⟨hs,hr,hi,rfl⟩
  | succ fuel ih =>
    simp only [run,UnitIntervalMaskedScan.run,choose_eq,hi]
    cases hy : UnitIntervalMaskedScan.choose G (active alive) s.order.toFinset (active s.remaining) with
    | none => simp only [hy]; exact ⟨hs,hr,hi,True.intro⟩
    | some y =>
      simp only [hy,score_eq,hi]
      by_cases hz : UnitIntervalGreedy.score G s.order.toFinset y = 0
      · simp only [hz,ite_true]; exact ⟨hs,hr,hi,True.intro⟩
      · simp only [hz,ite_false]
        have hs' : (set s.selected y true).length = n := (set_length _ _ _).trans hs
        have hr' : (set s.remaining y false).length = n := (set_length _ _ _).trans hr
        have hi' : active (set s.selected y true) = (s.order++[y]).toFinset := by
          rw [active_set_true _ hs,hi]
          ext v; simp [or_comm]
        have hh := ih ⟨s.order++[y],set s.selected y true,set s.remaining y false⟩ hs' hr' hi'
        simpa only [active_set_false _ hr] using hh

end HiddenCircuits.GraphReduction.UnitIntervalBitMasks

namespace HiddenCircuits.GraphReduction.UnitIntervalBitMasks

lemma weighted_priority_lt_iff (a s t d e : ℕ) (hd : d ≤ a) (he : e ≤ a) :
    (a+1)*s+(a-d) < (a+1)*t+(a-e) ↔ s<t ∨ (s=t ∧ e<d) := by
  have hd' := Nat.sub_add_cancel hd
  have he' := Nat.sub_add_cancel he
  constructor
  · intro hp
    by_cases hs : s<t
    · exact Or.inl hs
    · have hge : t ≤ s := Nat.le_of_not_gt hs
      by_cases hst : s=t
      · exact Or.inr ⟨hst,by rw [hst] at hp; omega⟩
      · have hm := Nat.mul_le_mul_left (a+1) (show t+1 ≤ s by omega)
        nlinarith
  · rintro (hst|⟨rfl,hed⟩)
    · have hm := Nat.mul_le_mul_left (a+1) (Nat.succ_le_of_lt hst)
      nlinarith
    · omega

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
lemma score_le_count (mask : List Bool) (v : Fin n) : score G mask v ≤ count (n:=n) mask := by
  rw [score_eq,count_eq_card]
  exact Finset.card_filter_le _ _

/-- The physical selector may compare score/degree pairs directly, skipping
both the priority multiplication and a separate alive-count scan. -/
theorem priority_improves (alive selected : List Bool) (best candidate : Fin n) :
    priority G alive selected best < priority G alive selected candidate ↔
      score G selected best < score G selected candidate ∨
        (score G selected best = score G selected candidate ∧
          score G alive candidate < score G alive best) :=
  weighted_priority_lt_iff _ _ _ _ _ (score_le_count G alive best) (score_le_count G alive candidate)

end HiddenCircuits.GraphReduction.UnitIntervalBitMasks

namespace HiddenCircuits.GraphReduction.UnitIntervalBitMasks

/-- Retain the first maximum: equal candidates never replace an incumbent. -/
def consider {α : Type*} (priority : α → ℕ) (old : Option α) (candidate : α) : Option α :=
  match old with
  | none => some candidate
  | some best => if priority best < priority candidate then some candidate else some best

lemma consider_eq_argAux {α : Type*} (p : α → ℕ) :
    consider p = List.argAux (fun b c => p c < p b) := by
  funext old candidate
  cases old <;> rfl

lemma consider_fold_argmax {α : Type*} (p : α → ℕ) (xs : List α) :
    xs.foldl (consider p) none = xs.argmax p := by
  rw [consider_eq_argAux]
  rfl

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
def chooseStep (alive selected remaining : List Bool) (old : Option (Fin n)) (v : Fin n) : Option (Fin n) :=
  if read remaining v then consider (priority G alive selected) old v else old

/-- The actual ascending scan with an optional winner equals filtered argmax,
for every candidate prefix, not merely the full vertex list. -/
theorem choose_fold_prefix (alive selected remaining : List Bool) (xs : List (Fin n)) :
    xs.foldl (chooseStep G alive selected remaining) none =
      (xs.filter (read remaining)).argmax (priority G alive selected) := by
  rw [←consider_fold_argmax,List.foldl_filter]
  rfl

theorem choose_fold (alive selected remaining : List Bool) :
    (List.finRange n).foldl (chooseStep G alive selected remaining) none =
      choose G alive selected remaining := choose_fold_prefix G alive selected remaining _

end HiddenCircuits.GraphReduction.UnitIntervalBitMasks
