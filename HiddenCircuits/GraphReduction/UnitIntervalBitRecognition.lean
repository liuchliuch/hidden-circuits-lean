import HiddenCircuits.GraphReduction.UnitIntervalBitMasks
import HiddenCircuits.GraphReduction.UnitIntervalMaskPadding

/-! Full literal Boolean-list-mask recognition semantics, with original-n clocks
throughout. This layer is the exact semantic target of the physical stack program. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalBitRecognition
open UnitIntervalBitMasks UnitIntervalOrder
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def eraseList : List Bool → List (Fin n) → List Bool
  | mask,[] => mask
  | mask,v::vs => eraseList (set mask v false) vs

@[simp] lemma eraseList_length (mask : List Bool) (ls : List (Fin n)) :
    (eraseList mask ls).length = mask.length := by
  induction ls generalizing mask with
  | nil => rfl
  | cons v vs ih => simp only [eraseList,ih,set_length]

lemma active_eraseList (mask : List Bool) (hm : mask.length = n) (ls : List (Fin n)) :
    active (eraseList mask ls) = active mask \ ls.toFinset := by
  induction ls generalizing mask with
  | nil => simp [eraseList]
  | cons v vs ih =>
    rw [eraseList,ih (set mask v false) ((set_length _ _ _).trans hm),active_set_false _ hm]
    ext w
    simp only [List.toFinset_cons,Finset.mem_sdiff,Finset.mem_erase,Finset.mem_insert]
    tauto

def componentState (alive : List Bool) (root : Fin n) : UnitIntervalBitMasks.State n :=
  run G alive n ⟨[root],ofFinset {root},set alive root false⟩
def component (alive : List Bool) (root : Fin n) : List (Fin n) := (componentState G alive root).order

lemma component_eq (alive : List Bool) (ha : alive.length = n) (root : Fin n) :
    component G alive root = UnitIntervalMaskedRecognition.component G (active alive) root := by
  have hh := run_refines G alive n (⟨[root],ofFinset {root},set alive root false⟩ : UnitIntervalBitMasks.State n)
    (ofFinset_length _) ((set_length _ _ _).trans ha) (by simp)
  have he := congrArg Prod.fst hh.2.2.2
  simp only [active_set_false _ ha] at he
  rw [UnitIntervalMaskedRecognition.component_original_clock]
  simpa only [component,componentState,Fintype.card_fin] using he

def goodRoot (alive : List Bool) : Option (Fin n) :=
  (members alive).find? (fun root => decide (ListUmbrella G (component G alive root)))

lemma goodRoot_eq (alive : List Bool) (ha : alive.length = n) :
    goodRoot G alive = UnitIntervalMaskedRecognition.goodRoot G (active alive) := by
  simp only [goodRoot,UnitIntervalMaskedRecognition.goodRoot,members_eq_sort,component_eq G alive ha]

/-- Every loop bound is the original n; alive masks only disable labels. -/
def search : ℕ → List Bool → Option (List (Fin n))
  | 0,alive => if count (n:=n) alive = 0 then some [] else none
  | fuel+1,alive => if count (n:=n) alive = 0 then some [] else
      match goodRoot G alive with
      | none => none
      | some root =>
        let ls := component G alive root
        (search fuel (eraseList alive ls)).map (fun rest => ls++rest)

/-- Exact equality with the fixed-label finite-set recognizer. -/
theorem search_eq (fuel : ℕ) (alive : List Bool) (ha : alive.length = n) :
    search G fuel alive = UnitIntervalMaskedRecognition.search G fuel (active alive) := by
  induction fuel generalizing alive with
  | zero => simp only [search,UnitIntervalMaskedRecognition.search,count_eq_card,Finset.card_eq_zero]
  | succ fuel ih =>
    simp only [search,UnitIntervalMaskedRecognition.search,count_eq_card,Finset.card_eq_zero,
      goodRoot_eq G alive ha,component_eq G alive ha]
    by_cases he : active (n:=n) alive = ∅
    · simp [he]
    · simp only [he,ite_false]
      cases hroot : UnitIntervalMaskedRecognition.goodRoot G (active alive) with
      | none => rfl
      | some root =>
        simp only
        rw [ih _ ((eraseList_length _ _).trans ha),active_eraseList _ ha]

def recognize : Option (List (Fin n)) := search G n (List.replicate n true)

lemma active_all : active (List.replicate n true) = (Finset.univ : Finset (Fin n)) := by
  ext v
  simp [active,UnitIntervalBitMasks.read,List.getElem?_replicate,v.isLt]

theorem recognize_iff : (recognize G).isSome = true ↔ RealUnitInterval.UnitIntervalGraph G := by
  unfold recognize
  rw [search_eq G n _ (by simp),active_all]
  simpa only [UnitIntervalMaskedRecognition.recognize,Fintype.card_fin] using UnitIntervalMaskedRecognition.recognize_iff G

end HiddenCircuits.GraphReduction.UnitIntervalBitRecognition
