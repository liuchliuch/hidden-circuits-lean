import HiddenCircuits.DH.Runtime.BagStateModel

/-! A graph-independent size invariant for unconditional machine bounds.
Even an arbitrary Boolean input matrix can only merge distinct live bags. -/
namespace HiddenCircuits.DH.Runtime.PruningModel
open scoped BigOperators

 def liveSet {n : ℕ} (s : ModuleExecution.Store n) : Finset (Fin n) :=
  Finset.univ.filter (fun v=>s.alive[v.val]=true)

 def volume {n : ℕ} (s : ModuleExecution.Store n) : ℕ :=
  ∑v∈liveSet s, s.bags[v.val].size

@[simp] lemma mem_liveSet {n : ℕ} (s : ModuleExecution.Store n) (v : Fin n) :
    v∈liveSet s ↔ s.alive[v.val]=true := by simp [liveSet]

lemma applyBag_liveSet {n : ℕ} (s : ModuleExecution.Store n) (a : Action n) (hne : a.keep≠a.removed) :
    liveSet (applyBag s a)=(liveSet s).erase a.removed := by
  ext v
  simp only [mem_liveSet,applyBag_alive s a hne,remove_alive,Finset.mem_erase]
  tauto

/-- Every ordinary binary merge conserves the exact original-vertex volume.
No graph symmetry, distance heredity, or matching interpretation is assumed. -/
theorem applyBag_volume {n : ℕ} (s : ModuleExecution.Store n) (a : Action n)
    (hu : s.alive[a.keep.val]=true) (hv : s.alive[a.removed.val]=true) (hne : a.keep≠a.removed) :
    volume (applyBag s a)=volume s := by
  let L := liveSet s
  let S := L.erase a.removed
  have hU : a.keep∈S := Finset.mem_erase.mpr ⟨hne,(mem_liveSet s a.keep).mpr hu⟩
  have hV : a.removed∈L := (mem_liveSet s a.removed).mpr hv
  have hnew := Finset.sum_erase_add S (fun v : Fin n=>(applyBag s a).bags[v.val].size) hU
  have hmid := Finset.sum_erase_add S (fun v : Fin n=>s.bags[v.val].size) hU
  have hold := Finset.sum_erase_add L (fun v : Fin n=>s.bags[v.val].size) hV
  dsimp only at hnew hmid hold
  have hrest : (∑v∈S.erase a.keep, (applyBag s a).bags[v.val].size)=
      ∑v∈S.erase a.keep, s.bags[v.val].size := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [applyBag_other s a v (Finset.mem_erase.mp hv).1]
  rw [hrest,applyBag_kept,CoefficientModel.mergeBag_size] at hnew
  unfold volume
  rw [applyBag_liveSet s a hne]
  change (∑v∈S, (applyBag s a).bags[v.val].size)=∑v∈L, s.bags[v.val].size
  dsimp only [S,L] at hnew hmid hold ⊢
  omega

lemma bag_size_le_volume {n : ℕ} (s : ModuleExecution.Store n) (v : Fin n) (hv : s.alive[v.val]=true) :
    s.bags[v.val].size≤volume s := by
  change s.bags[v.val].size≤∑x∈liveSet s, s.bags[x.val].size
  exact Finset.single_le_sum (f:=fun x : Fin n=>s.bags[x.val].size) (fun _ _=>Nat.zero_le _) ((mem_liveSet s v).mpr hv)

@[simp] theorem initial_volume (n : ℕ) : volume (ModuleExecution.initial n)=n := by
  simp [volume,liveSet,ModuleExecution.initial,BagExpr.size]

/-- The scalar bit bound remains valid on malformed/non-DH Boolean matrices
as long as the program enforces distinct live pair endpoints. -/
lemma applyBag_bounded {n : ℕ} (s : ModuleExecution.Store n) (a : Action n)
    (hu : s.alive[a.keep.val]=true) (hv : s.alive[a.removed.val]=true) (hne : a.keep≠a.removed)
    (hvol : volume s≤n) (hsize : ∀v : Fin n, s.bags[v.val].size≤n) :
    volume (applyBag s a)≤n ∧ ∀v : Fin n, (applyBag s a).bags[v.val].size≤n := by
  have hvol' : volume (applyBag s a)≤n := by rw [applyBag_volume s a hu hv hne];exact hvol
  refine ⟨hvol',?_⟩
  intro v
  by_cases he : v=a.keep
  · subst v
    apply (bag_size_le_volume (applyBag s a) a.keep ?_).trans hvol'
    rw [applyBag_alive s a hne,remove_alive]
    exact ⟨hu,hne⟩
  · rw [applyBag_other s a v he]
    exact hsize v

end HiddenCircuits.DH.Runtime.PruningModel
