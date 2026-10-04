import HiddenCircuits.DH.Runtime.PruningCorrectness
import HiddenCircuits.DH.Runtime.CoefficientModel
import HiddenCircuits.DH.StoreFinalization

/-! Refinement of the exhaustive fixed-label action trace to genuine bag states.
Only the numeric table is stored by the forthcoming bit program; these bag
expressions are proof-side witnesses for its coefficient meaning. -/
namespace HiddenCircuits.DH.Runtime.PruningModel
open SimpleGraph ModuleExecution

/-- Each action changes only the survivor bag and the removed live mark. -/
def applyBag {n : ℕ} (s : ModuleExecution.Store n) (a : Action n) : ModuleExecution.Store n :=
  match a.kind with
  | .pendant => (ModuleExecution.absorb s a.keep a.removed).value
  | .twin joined => (ModuleExecution.contract s [a.keep,a.removed] a.keep
      (.node joined (.leaf a.keep) (.leaf a.removed))).value

lemma applyBag_alive {n : ℕ} (s : ModuleExecution.Store n) (a : Action n) (hne : a.keep≠a.removed) :
    (applyBag s a).alive=remove s.alive a := by
  apply Vector.ext
  intro i hi
  let v : Fin n := ⟨i,hi⟩
  apply Bool.eq_iff_iff.mpr
  cases hk : a.kind with
  | pendant => simpa only [applyBag,hk] using (ModuleExecution.absorb_alive s a.keep a.removed v).trans (remove_alive s.alive a v).symm
  | twin joined =>
    have h := ModuleExecution.contract_alive s [a.keep,a.removed] a.keep
      (.node joined (.leaf a.keep) (.leaf a.removed)) v
    change (applyBag s a).alive[v.val]=true ↔ (remove s.alive a)[v.val]=true
    simp only [applyBag,hk]
    rw [h,remove_alive]
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
    have hvne : v=a.keep → v≠a.removed := fun he=>he ▸ hne
    tauto

lemma applyBag_kept {n : ℕ} (s : ModuleExecution.Store n) (a : Action n) :
    (applyBag s a).bags[a.keep.val]=CoefficientModel.mergeBag a.kind s.bags[a.keep.val] s.bags[a.removed.val] := by
  cases hk : a.kind with
  | pendant => simp [applyBag,hk,CoefficientModel.mergeBag]
  | twin joined =>
    simp only [applyBag,hk,ModuleExecution.contract_kept_bag]
    cases joined <;> rfl

lemma applyBag_other {n : ℕ} (s : ModuleExecution.Store n) (a : Action n) (v : Fin n) (hv : v≠a.keep) :
    (applyBag s a).bags[v.val]=s.bags[v.val] := by
  cases hk : a.kind with
  | pendant => simpa only [applyBag,hk] using ModuleExecution.absorb_other_bag s a.keep a.removed v hv
  | twin joined =>
    simpa only [applyBag,hk] using (ModuleExecution.contract_other_bag s [a.keep,a.removed] a.keep
      (.node joined (.leaf a.keep) (.leaf a.removed)) v hv)

lemma twin_pair_module {n : ℕ} (G : SimpleGraph (Fin n)) (s : ModuleExecution.Store n)
    (u v : Fin n)
    (ht : ∀x, s.alive[x.val]=true → x≠u → x≠v → (G.Adj v x ↔ G.Adj u x)) :
    GraphModule (ModuleExecution.liveGraph G s) (ModuleExecution.liveModule s [u,v] : Set (ModuleExecution.Live s)) := by
  intro a ha b hb x hx
  have ha' : a.val=u ∨ a.val=v := by simpa using ha
  have hb' : b.val=u ∨ b.val=v := by simpa using hb
  have hx' : x.val≠u ∧ x.val≠v := by simpa using hx
  change G.Adj a.val x.val ↔ G.Adj b.val x.val
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;> rw [ha',hb']
  · exact (ht x.val x.property hx'.1 hx'.2).symm
  · exact ht x.val x.property hx'.1 hx'.2

/-- Every checked action preserves the full original-graph bag interpretation,
without assuming distance heredity for this local soundness statement. -/
noncomputable def applyBag_interpretation {n : ℕ} {G : SimpleGraph (Fin n)}
    {s : ModuleExecution.Store n} (I : ModuleExecution.Interpretation G s)
    (a : Action n) (h : Valid G s.alive a) : ModuleExecution.Interpretation G (applyBag s a) := by
  obtain ⟨hu,hv,hne,hkind⟩ := h
  cases hk : a.kind with
  | pendant =>
    rw [hk] at hkind
    change G.Adj a.removed a.keep ∧ ∀x, s.alive[x.val]=true → G.Adj a.removed x → x=a.keep at hkind
    have hp : PendantPair (ModuleExecution.liveGraph G s) ⟨a.keep,hu⟩ ⟨a.removed,hv⟩ :=
      ⟨hkind.1,fun x hx=>Subtype.ext (hkind.2 x.val x.property hx)⟩
    simpa only [applyBag,hk] using I.absorb a.keep a.removed hu hv hp
  | twin joined =>
    rw [hk] at hkind
    change (G.Adj a.keep a.removed ↔ joined=true) ∧
      ∀x, s.alive[x.val]=true → x≠a.keep → x≠a.removed → (G.Adj a.removed x ↔ G.Adj a.keep x) at hkind
    let t : LabeledCographTree (Fin n) := .node joined (.leaf a.keep) (.leaf a.removed)
    have ht : t.Correct G := by
      apply LabeledCographTree.Correct.node joined (LabeledCographTree.correct_leaf G a.keep)
        (LabeledCographTree.correct_leaf G a.removed)
      intro x hx y hy
      have hx' : x=a.keep := by simpa [LabeledCographTree.leaves] using hx
      have hy' : y=a.removed := by simpa [LabeledCographTree.leaves] using hy
      subst x;subst y
      exact hkind.1
    have hn : t.leaves.Nodup := by simp [t,LabeledCographTree.leaves,hne]
    have hc : ∀v, v∈t.leaves ↔ v∈[a.keep,a.removed] := by intro v;rfl
    have hl : ∀v∈[a.keep,a.removed], s.alive[v.val]=true := by
      intro v hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hu
      · have he := List.mem_singleton.mp hm;subst v;exact hv
    simpa only [applyBag,hk] using I.contract [a.keep,a.removed] a.keep (by simp) hl t hn ht hc (twin_pair_module G s _ _ hkind.2)

def executeActions {n : ℕ} : List (Action n)→ModuleExecution.Store n→ModuleExecution.Store n
  | [],s => s
  | a::as,s => executeActions as (applyBag s a)

/-- The same exact action list drives the live-mask model and the bag model. -/
theorem Trace.executeActions {n : ℕ} {G : SimpleGraph (Fin n)}
    {alive final : Vector Bool n} {as : List (Action n)} (h : Trace G alive as final)
    (s : ModuleExecution.Store n) (hs : s.alive=alive) (I : ModuleExecution.Interpretation G s) :
    (executeActions as s).alive=final ∧ Nonempty (ModuleExecution.Interpretation G (executeActions as s)) := by
  induction h generalizing s with
  | nil alive => exact ⟨hs,⟨I⟩⟩
  | @cons alive final a as valid rest ih =>
    have hv : Valid G s.alive a := hs ▸ valid
    have ha : (applyBag s a).alive=remove alive a := (applyBag_alive s a hv.2.2.1).trans (congrArg (fun x=>remove x a) hs)
    exact ih (applyBag s a) ha (applyBag_interpretation I a hv)

lemma interpretation_bag_size {n : ℕ} {G : SimpleGraph (Fin n)} {s : ModuleExecution.Store n}
    (I : ModuleExecution.Interpretation G s) (v : Fin n) (hv : s.alive[v.val]=true) : s.bags[v.val].size≤n := by
  let r : ModuleExecution.Live s := ⟨v,hv⟩
  have hc := Fintype.card_congr (I.representation.iso r).toEquiv
  rw [BagExpr.card_vertex] at hc
  have he := congrArg BagExpr.size (I.bags_eq r)
  dsimp only [r] at he
  have hb : Fintype.card (I.partition.Fiber r)≤n := by
    simpa only [Fintype.card_fin] using (Fintype.card_subtype_le (fun x : Fin n=>I.partition.place x=r))
  exact (le_of_eq (he.symm.trans hc)).trans hb

/-- All completed numerical bags, including frozen deleted slots, stay within
n vertices whenever the checked action program begins with singleton bags. -/
lemma applyBag_size_bound {n : ℕ} {G : SimpleGraph (Fin n)} {s : ModuleExecution.Store n}
    (I : ModuleExecution.Interpretation G s) (a : Action n) (h : Valid G s.alive a)
    (hb : ∀v : Fin n, s.bags[v.val].size≤n) : ∀v : Fin n, (applyBag s a).bags[v.val].size≤n := by
  have I' := applyBag_interpretation I a h
  intro v
  by_cases hv : v=a.keep
  · subst v
    apply interpretation_bag_size I'
    rw [applyBag_alive s a h.2.2.1,remove_alive]
    exact ⟨h.1,h.2.2.1⟩
  · rw [applyBag_other s a v hv]
    exact hb v

end HiddenCircuits.DH.Runtime.PruningModel
