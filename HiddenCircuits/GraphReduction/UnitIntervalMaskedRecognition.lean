import HiddenCircuits.GraphReduction.UnitIntervalMaskedScan
import HiddenCircuits.GraphReduction.UnitIntervalRecognition

/-! Fixed-universe recognition: all live sets and emitted labels remain in the
original Fin n (or any finite ordered label type). This is the semantic target
for the binary array/mask implementation. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalMaskedRecognition
open UnitIntervalOrder
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

def component (A : Finset V) (root : V) : List V :=
  (UnitIntervalMaskedScan.run G A A.card [root] (A.erase root)).1

lemma component_lift (A : Finset V) (root : {v // v ∈ A}) :
    component G A root.val =
      (UnitIntervalGreedy.component (UnitIntervalMaskedScan.induced G A) root).map Subtype.val := by
  simpa only [component,UnitIntervalGreedy.component,Fintype.card_coe,List.map_cons,List.map_nil,
    UnitIntervalMaskedScan.lift_erase,UnitIntervalMaskedScan.lift_univ] using
    congrArg Prod.fst (UnitIntervalMaskedScan.run_lift G A A.card [root] (Finset.univ.erase root))

lemma component_mem (A : Finset V) {root v : V} (hr : root ∈ A) (hv : v ∈ component G A root) : v ∈ A := by
  rw [component_lift G A ⟨root,hr⟩] at hv
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hv
  exact v.property
lemma component_root (A : Finset V) {root : V} (hr : root ∈ A) : root ∈ component G A root := by
  rw [component_lift G A ⟨root,hr⟩]
  exact List.mem_map.mpr ⟨⟨root,hr⟩,UnitIntervalGreedy.component_root_mem _ _,rfl⟩
lemma component_nodup (A : Finset V) {root : V} (hr : root ∈ A) : (component G A root).Nodup := by
  rw [component_lift G A ⟨root,hr⟩]
  exact (UnitIntervalGreedy.component_nodup _ _).map Subtype.val_injective
lemma component_closed (A : Finset V) {root v w : V} (hr : root ∈ A)
    (hv : v ∈ component G A root) (hw : w ∈ A) (hwn : w ∉ component G A root) : ¬G.Adj v w := by
  rw [component_lift G A ⟨root,hr⟩] at hv hwn
  obtain ⟨z,hz,hzv⟩ := List.mem_map.mp hv
  subst v
  exact UnitIntervalGreedy.component_closed (UnitIntervalMaskedScan.induced G A) ⟨root,hr⟩ hz
    (show (⟨w,hw⟩ : {v // v ∈ A}) ∉ _ from fun he => hwn (List.mem_map.mpr ⟨⟨w,hw⟩,he,rfl⟩))

def goodRoot (A : Finset V) : Option V :=
  (A.sort (· ≤ ·)).find? (fun root => decide (ListUmbrella G (component G A root)))

lemma goodRoot_spec (A : Finset V) {root : V} (h : goodRoot G A = some root) :
    root ∈ A ∧ ListUmbrella G (component G A root) := by
  unfold goodRoot at h
  refine ⟨(Finset.mem_sort _).mp (List.mem_of_find?_eq_some h),?_⟩
  have hh : decide (ListUmbrella G (component G A root)) = true :=
    List.find?_some (p:=fun v : V => decide (ListUmbrella G (component G A v))) h
  exact of_decide_eq_true hh

lemma goodRoot_exists (A : Finset V) (hA : A.Nonempty) (r : RealUnitInterval.Representation G) :
    ∃ root, goodRoot G A = some root := by
  obtain ⟨root,hr,hmin⟩ := A.exists_min_image r.left hA
  let ra : RealUnitInterval.Representation (UnitIntervalMaskedScan.induced G A) := r.induce (↑A : Set V)
  obtain ⟨r',hs⟩ := UnitIntervalGreedy.component_sorted ra (⟨root,hr⟩ : {v // v ∈ A})
    (fun v => hmin v.val v.property)
  have hu := listUmbrella_of_sorted r' _ (UnitIntervalGreedy.component_nodup _ _) hs
  have hv : ListUmbrella G (component G A root) := by
    rw [component_lift G A ⟨root,hr⟩]
    exact listUmbrella_map Subtype.val _ hu
  cases he : goodRoot G A with
  | some root => exact ⟨root,rfl⟩
  | none =>
    have hh := List.find?_eq_none.mp he root ((Finset.mem_sort _).mpr hr)
    exact (hh (by simpa using hv)).elim

/-- All recursion preserves the original vertex type; only the alive mask changes. -/
def search : ℕ → Finset V → Option (List V)
  | 0,A => if A = ∅ then some [] else none
  | fuel+1,A => if A = ∅ then some [] else
      match goodRoot G A with
      | none => none
      | some root =>
        let ls := component G A root
        (search fuel (A \ ls.toFinset)).map (fun rest => ls++rest)

theorem search_sound (fuel : ℕ) (A : Finset V) (ls : List V) (h : search G fuel A = some ls) :
    ls.Nodup ∧ ls.toFinset = A ∧ ListUmbrella G ls := by
  induction fuel generalizing A ls with
  | zero =>
    simp only [search] at h
    split at h
    · rename_i he; subst A; cases h
      exact ⟨by simp,by simp,by intro i; exact Fin.elim0 i⟩
    · contradiction
  | succ fuel ih =>
    simp only [search] at h
    split at h
    · rename_i he; subst A; cases h
      exact ⟨by simp,by simp,by intro i; exact Fin.elim0 i⟩
    · split at h
      · contradiction
      · rename_i root hroot
        obtain ⟨rest,hr,he⟩ := Option.map_eq_some_iff.mp h
        subst ls
        obtain ⟨hn,hcover,hu⟩ := ih _ _ hr
        obtain ⟨hrootA,hrootU⟩ := goodRoot_spec G A hroot
        have hrest : ∀ v ∈ rest, v ∈ A ∧ v ∉ component G A root := by
          intro v hv
          have hm : v ∈ rest.toFinset := List.mem_toFinset.mpr hv
          rw [hcover] at hm
          simpa only [Finset.mem_sdiff,List.mem_toFinset] using hm
        refine ⟨?_,?_,?_⟩
        · rw [List.nodup_append]
          exact ⟨component_nodup G A hrootA,hn,fun v hv w hw he =>
            (hrest w hw).2 (he ▸ hv)⟩
        · rw [List.toFinset_append,hcover]
          ext v
          simp only [Finset.mem_union,Finset.mem_sdiff,List.mem_toFinset]
          have hv := component_mem G A hrootA (v:=v)
          tauto
        · exact listUmbrella_append _ _ hrootU hu (fun v hv w hw =>
            component_closed G A hrootA hv (hrest w hw).1 (hrest w hw).2)

theorem search_complete (fuel : ℕ) (A : Finset V) (hf : A.card ≤ fuel)
    (r : RealUnitInterval.Representation G) : ∃ ls, search G fuel A = some ls := by
  induction fuel generalizing A with
  | zero =>
    have he : A=∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hf)
    exact ⟨[],by simp [search,he]⟩
  | succ fuel ih =>
    by_cases he : A=∅
    · exact ⟨[],by simp [search,he]⟩
    · obtain ⟨root,hroot⟩ := goodRoot_exists G A (Finset.nonempty_iff_ne_empty.mpr he) r
      have hr := (goodRoot_spec G A hroot).1
      have hs : A \ (component G A root).toFinset ⊂ A := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset,?_⟩
        intro hh
        have hm : root ∈ A \ (component G A root).toFinset := by rw [hh]; exact hr
        exact (Finset.mem_sdiff.mp hm).2 (List.mem_toFinset.mpr (component_root G A hr))
      have hc := Finset.card_lt_card hs
      obtain ⟨rest,hrest⟩ := ih (A \ (component G A root).toFinset) (by omega)
      exact ⟨component G A root++rest,by simp [search,he,hroot,hrest]⟩

def recognize : Option (List V) := search G (Fintype.card V) Finset.univ

theorem recognize_iff : (recognize G).isSome = true ↔ RealUnitInterval.UnitIntervalGraph G := by
  constructor
  · intro h
    obtain ⟨ls,he⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hn,hc,hu⟩ := search_sound G (Fintype.card V) Finset.univ ls he
    have hall : ∀ v, v ∈ ls := by intro v; apply List.mem_toFinset.mp; rw [hc]; exact Finset.mem_univ _
    exact ⟨(representationOfList G ls hn hall hu).toReal⟩
  · rintro ⟨r⟩
    obtain ⟨ls,he⟩ := search_complete G (Fintype.card V) Finset.univ (by simp) r
    simp [recognize,he]

end HiddenCircuits.GraphReduction.UnitIntervalMaskedRecognition
