import HiddenCircuits.GraphReduction.Runtime.DescriptorEvenPositive
import HiddenCircuits.Complexity.WordEncoding

/-! Fresh reconstruction of the exact canonical descriptor enumeration. This file
contains list equalities, rather than a supplied representation certificate. -/
namespace HiddenCircuits.GraphReduction.Runtime.DescriptorEnumeration
open Complexity
set_option maxHeartbeats 800000

lemma maskRow_ofFn (v : VertexRecord) {n : ℕ} (f : Fin n → Bool) :
    DescriptorMaskRow.records v (List.ofFn f) =
      (List.finRange n).flatMap (fun i => if f i then [{v with track := v.track+i.val}] else []) := by
  induction n generalizing v with
  | zero => simp [DescriptorMaskRow.records]
  | succ n ih =>
    rw [List.ofFn_succ, DescriptorMaskRow.records, ih, List.finRange_succ]
    simp only [List.flatMap_cons, List.flatMap_map, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply congrArg (fun f => (List.finRange n).flatMap f)
    funext i
    congr 2
    congr 1
    omega

lemma filtered_map_eq_flatMap {α β : Type*} (xs : List α) (p : α → Bool) (f : α → β) :
    (xs.filter p).map f = xs.flatMap (fun x => if p x then [f x] else []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx:p x <;> simp [hx,ih]

lemma row_eq_finRange (v : VertexRecord) (width : ℕ) :
    DescriptorRow.records v width =
      (List.finRange width).map (fun i => {v with track:=v.track+i.val}) := by
  rw [DescriptorRow.records, ←List.ofFn_const, maskRow_ofFn]
  simp only [ite_true,←List.map_eq_flatMap]

lemma rectangle_eq_finRange (v : VertexRecord) (width height : ℕ) :
    DescriptorRectangle.records v width height =
      (List.finRange height).flatMap (fun i =>
        (List.finRange width).map (fun j => {v with layer:=v.layer+i.val,track:=v.track+j.val})) := by
  induction height generalizing v with
  | zero => simp [DescriptorRectangle.records]
  | succ n ih =>
    rw [DescriptorRectangle.records, row_eq_finRange, ih, List.finRange_succ]
    simp only [List.flatMap_cons, List.flatMap_map, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply congrArg (fun f => (List.finRange n).flatMap f)
    funext i
    apply List.map_congr_left
    intro j hj
    congr 1
    omega

lemma subtype_labels_map {α β : Type*} (e : Enumeration α) (P : α → Prop) [DecidablePred P]
    (f : α → β) :
    ((e.subtype P).labels.map (fun x => f x.val)) = (e.labels.filter (fun x=>decide (P x))).map f := by
  simp [Enumeration.subtype,List.map_map,Function.comp_def]

lemma product_filtered_map {α β γ : Type*} (xs : List α) (ys : List β)
    (P : α × β → Bool) (f : α × β → γ) :
    ((xs.product ys).filter P).map f =
      xs.flatMap (fun x => (ys.filter (fun y=>P (x,y))).map (fun y=>f (x,y))) := by
  simp only [List.product, List.filter_flatMap, List.map_flatMap, List.filter_map, List.map_map]
  rfl

lemma zipWith_ofFn {α β γ : Type*} {n : ℕ} (f : α → β → γ) (a : Fin n → α) (b : Fin n → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun i=>f (a i) (b i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ,List.zipWith_cons_cons,ih]

def evenMask {p : ℕ} (S T : State (2*p) p) (height layer : ℕ) : BitString :=
  List.ofFn (fun i : Fin (2*p) => decide ((layer=0 → i∈S.val) ∧ (layer=height → i∉T.val)))

lemma evenMask_zero {p : ℕ} (S T : State (2*p) p) :
    evenMask S T 0 0 = DescriptorMaskDifference.difference (stateBits S) (stateBits T) := by
  simp [evenMask,stateBits,DescriptorMaskDifference.difference,zipWith_ofFn]

lemma evenMask_first {p h : ℕ} (S T : State (2*p) p) (hh : 0<h) :
    evenMask S T h 0 = stateBits S := by
  simp [evenMask,stateBits,Ne.symm (Nat.ne_of_gt hh)]

lemma evenMask_last {p h : ℕ} (S T : State (2*p) p) (hh : 0<h) :
    evenMask S T h h = DescriptorMaskDifference.difference (List.replicate (2*p) true) (stateBits T) := by
  unfold DescriptorMaskDifference.difference stateBits
  rw [←List.ofFn_const,zipWith_ofFn]
  simp [evenMask,Nat.ne_of_gt hh]

lemma evenMask_interior {p h layer : ℕ} (S T : State (2*p) p) (h0 : layer≠0) (hh : layer≠h) :
    evenMask S T h layer = List.replicate (2*p) true := by
  simp [evenMask,h0,hh]

lemma retained_even_rows {p h : ℕ} (S T : State (2*p) p) :
    (retainedEvenEnumeration (h:=h) S T).labels.map
      (fun x => (⟨false,false,x.val.1.val,x.val.2.val,backgroundCode⟩ : VertexRecord)) =
    (List.finRange (h+1)).flatMap (fun i =>
      DescriptorMaskRow.records (DescriptorEven.vertex i.val) (evenMask S T h i.val)) := by
  unfold retainedEvenEnumeration
  simp only [Enumeration.subtype,List.map_map,Function.comp_def]
  rw [List.attach_map_val (f := fun v : EvenVertex (2*p) h =>
    (⟨false,false,v.1.val,v.2.val,backgroundCode⟩ : VertexRecord))]
  change (((List.finRange (h+1)).product (List.finRange (2*p))).filter _).map _ = _
  rw [product_filtered_map]
  apply congrArg (fun f => (List.finRange (h+1)).flatMap f)
  funext i
  rw [filtered_map_eq_flatMap,evenMask,maskRow_ofFn]
  simp [DescriptorEven.vertex]

lemma retained_even_eq {p h : ℕ} (S T : State (2*p) p) :
    (retainedEvenEnumeration (h:=h) S T).labels.map
      (fun x => (⟨false,false,x.val.1.val,x.val.2.val,backgroundCode⟩ : VertexRecord)) =
    DescriptorEven.records (2*p) h (stateBits S) (stateBits T) := by
  rw [retained_even_rows]
  cases h with
  | zero => simp [List.finRange_succ,evenMask_zero,DescriptorEven.records]
  | succ n =>
    rw [List.finRange_succ]
    simp only [List.flatMap_cons,List.flatMap_map,Fin.val_zero]
    rw [evenMask_first S T (by omega), List.finRange_succ_last]
    simp only [List.flatMap_append,List.flatMap_map,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,Fin.val_succ,Fin.val_last]
    rw [evenMask_last S T (by omega)]
    rw [DescriptorEven.records,List.append_assoc]
    congr 1
    congr 1
    rw [rectangle_eq_finRange]
    apply congrArg (fun f => (List.finRange n).flatMap f)
    funext i
    rw [evenMask_interior S T (by omega) (by have:=i.isLt; simp only [Fin.val_castSucc]; omega)]
    rw [←DescriptorRow.records,row_eq_finRange]
    simp [DescriptorEven.vertex,Nat.add_comm]

lemma probe_labels_eq (side : Bool) (h s : ℕ) :
    (probeEnumeration h s).labels.map
      (fun x => (⟨side,true,x.1.val,x.2.val,backgroundCode⟩ : VertexRecord)) =
    DescriptorRectangle.records ⟨side,true,0,0,backgroundCode⟩ s h := by
  rw [rectangle_eq_finRange]
  simp [probeEnumeration,Enumeration.prod,Enumeration.fin,List.product,List.map_flatMap,List.map_map,Function.comp_def]

end HiddenCircuits.GraphReduction.Runtime.DescriptorEnumeration
