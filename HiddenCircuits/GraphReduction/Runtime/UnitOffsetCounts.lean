import HiddenCircuits.GraphReduction.Runtime.CliqueDescriptor
import HiddenCircuits.GraphReduction.Runtime.UnitScalarOffsets

namespace HiddenCircuits.GraphReduction.Runtime
open UnitInterval

lemma enumeration_sum {V : Type*} [Fintype V] [DecidableEq V] (a : Enumeration V) (f : V → ℤ) :
    (a.labels.map f).sum=∑v,f v := by
  have he : a.labels.toFinset=Finset.univ := by ext v;simp [a.complete v]
  rw [←List.sum_toFinset f a.nodup,he]

lemma list_sum_prefix {α : Type*} (w : List α) (f : α → ℤ) (r : ℕ) :
    (∑i : Fin w.length, if i.val<r then f (w.get i) else 0)=((w.take r).map f).sum := by
  induction w generalizing r with
  | nil => simp
  | cons a w ih =>
    cases r with
    | zero => simp
    | succ r =>
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simpa using congrArg (fun z : ℤ=>f a+z) (ih r)

def descriptorScore (records : List VertexRecord) (layer track : ℕ) : ℤ :=
  (records.map (fun y=>if y.side && !y.probe && decide (y.layer<layer) && decide (y.track=0)
    then cutScore y.cut track else 0)).sum

lemma descriptorScore_unitRecords {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p)
    (s layer track : ℕ) (hp:0<2*p) :
    descriptorScore (unitRecords (fun i=>w.get i) S T s) layer track=prefixScore (w.take layer) track := by
  classical
  unfold descriptorScore unitRecords
  rw [List.map_map,enumeration_sum]
  simp only [Fintype.sum_sum_type,Function.comp_def,unitVertexRecord,Bool.false_and,
    Bool.not_true,Bool.and_false,Bool.false_eq_true,ite_false,Finset.sum_const_zero,add_zero,
    Bool.true_and,Bool.not_false]
  rw [Fintype.sum_prod_type]
  have hz : ∀i : Fin w.length,
      (∑j : Fin (2*p),if decide (i.val<layer) && decide (j.val=0) then cutScore (cutCode (w.get i)) track else 0)=
        if i.val<layer then cutScore (cutCode (w.get i)) track else 0 := by
    intro i
    by_cases hi:i.val<layer
    · simp only [hi,decide_true,Bool.true_and]
      have he : ∀j : Fin (2*p),j.val=0 ↔ j=⟨0,hp⟩ := by intro j;exact ⟨fun h=>Fin.ext h,fun h=>congrArg Fin.val h⟩
      simp only [decide_eq_true_eq,he]
      simp
    · simp [hi]
  simp_rw [hz]
  simpa [prefixScore] using list_sum_prefix w (fun P=>cutScore (cutCode P) track) layer
end HiddenCircuits.GraphReduction.Runtime
