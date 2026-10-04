import HiddenCircuits.GraphReduction.Runtime.MonotoneOrderCorrect
import HiddenCircuits.GraphReduction.PermutationRankCompression

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
open Complexity
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000
set_option linter.unusedSimpArgs false

lemma enumeration_filter_length {V : Type*} [Fintype V] (a : Enumeration V) (q : V → Bool) :
    (a.labels.filter q).length=∑v : V,if q v then 1 else 0 := by
  classical
  rw [Finset.sum_boole]
  rw [←List.toFinset_card_of_nodup (a.nodup.filter q)]
  congr 1
  ext v
  simp [a.complete v]

@[simp] lemma side_inl {p h s : ℕ} (pairs : Fin h → CutPair p) {S T : State (2*p) p}
    (x : ProbePart (RetainedEven p h S T) (Fin h) s) :
    (vertexRecord pairs (.inl x)).side=false := by cases x <;> rfl
@[simp] lemma side_inr {p h s : ℕ} (pairs : Fin h → CutPair p) {S T : State (2*p) p}
    (x : ProbePart (OddVertex (2*p) h) (Fin h) s) :
    (vertexRecord pairs (S:=S) (T:=T) (.inr x)).side=true := by cases x <;> rfl

lemma leftRank_correct {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x : ProbePart (RetainedEven p h S T) (Fin h) s) :
    leftRank (monotoneRecords pairs S T s) (vertexRecord pairs (.inl x))=
      endpointCount (fun y => (retainedMonotoneDiagram pairs S T s).upper (.inl y))
        ((retainedMonotoneDiagram pairs S T s).upper (.inl x)) := by
  unfold leftRank monotoneRecords
  rw [List.filter_map,List.length_map,enumeration_filter_length]
  simp only [Function.comp_apply,MonotoneOrder.upperRecordLT_correct,Fintype.sum_sum_type,
    side_inl,side_inr,Bool.not_false,Bool.not_true,Bool.true_and,Bool.false_and,
    Bool.false_eq_true,ite_false,Finset.sum_const_zero,add_zero,decide_eq_true_eq]
  simp only [endpointCount,Fintype.sum_sum_type,decide_eq_true_eq]

lemma upperCount_correct {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x : ProbePart (RetainedEven p h S T) (Fin h) s) :
    upperCount (monotoneRecords pairs S T s) (vertexRecord pairs (.inl x))=
      endpointCount (fun y => (retainedMonotoneDiagram pairs S T s).upper (.inr y))
        ((retainedMonotoneDiagram pairs S T s).upper (.inl x)) := by
  unfold upperCount monotoneRecords
  rw [List.filter_map,List.length_map,enumeration_filter_length]
  simp only [Function.comp_apply,MonotoneOrder.upperRecordLT_correct,Fintype.sum_sum_type,
    side_inl,side_inr,Bool.true_and,Bool.false_and,Bool.false_eq_true,ite_false,
    Finset.sum_const_zero,zero_add,decide_eq_true_eq]
  simp only [endpointCount,Fintype.sum_sum_type,decide_eq_true_eq]

lemma lowerCount_correct {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x : ProbePart (RetainedEven p h S T) (Fin h) s) :
    lowerCount (monotoneRecords pairs S T s) (vertexRecord pairs (.inl x))=
      endpointCount (fun y => (retainedMonotoneDiagram pairs S T s).lower (.inr y))
        ((retainedMonotoneDiagram pairs S T s).lower (.inl x)) := by
  unfold lowerCount monotoneRecords
  rw [List.filter_map,List.length_map,enumeration_filter_length]
  simp only [Function.comp_apply,MonotoneOrder.lowerRecordLT_correct,Fintype.sum_sum_type,
    side_inl,side_inr,Bool.true_and,Bool.false_and,Bool.false_eq_true,ite_false,
    Finset.sum_const_zero,zero_add,decide_eq_true_eq]
  simp only [endpointCount,Fintype.sum_sum_type,decide_eq_true_eq]

lemma leftRank_row {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x : ProbePart (RetainedEven p h S T) (Fin h) s) :
    leftRank (monotoneRecords pairs S T s) (vertexRecord pairs (.inl x))=
      ((retainedMonotoneDiagram pairs S T s).rowOrder.symm x).val := by
  rw [leftRank_correct]
  exact (rankByOrder_eq_count
    ⟨fun y => (retainedMonotoneDiagram pairs S T s).upper (.inl y),
      (retainedMonotoneDiagram pairs S T s).upper.injective.comp Sum.inl_injective⟩ x).symm

lemma selected_row {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (i : Fin (leftCard p h s S T)) :
    (monotoneRecords pairs S T s).filter (fun x=>!x.side && decide (leftRank (monotoneRecords pairs S T s) x=i.val))=
      [vertexRecord pairs (.inl ((retainedMonotoneDiagram pairs S T s).rowOrder i))] := by
  classical
  letI : BEq (QueryVertex p h s S T) := ⟨fun a b=>decide (a=b)⟩
  haveI : LawfulBEq (QueryVertex p h s S T) := {
    eq_of_beq := of_decide_eq_true
    rfl := of_decide_eq_self_eq_true _ }
  unfold monotoneRecords
  rw [List.filter_map]
  have hp : (fun x : QueryVertex p h s S T =>
      !(vertexRecord pairs x).side && decide (leftRank ((monotoneEnumeration S T s).labels.map (vertexRecord pairs)) (vertexRecord pairs x)=i.val)) =
      fun x => decide (x=Sum.inl ((retainedMonotoneDiagram pairs S T s).rowOrder i)) := by
    funext x
    cases x with
    | inl x =>
      rw [side_inl]
      change (!false && decide (leftRank (monotoneRecords pairs S T s) (vertexRecord pairs (.inl x))=i.val))=_
      rw [leftRank_row]
      simp only [Bool.not_false,Bool.true_and,Sum.inl.injEq]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      rw [←Fin.ext_iff]
      exact (Equiv.symm_apply_eq _).trans Iff.rfl
    | inr x => simp
  change List.map (vertexRecord pairs) (List.filter _ (monotoneEnumeration S T s).labels)=_
  simp only [Function.comp_def]
  rw [hp,List.filter_eq,(monotoneEnumeration S T s).nodup.count]
  simp [(monotoneEnumeration S T s).complete]

lemma selected_row_above {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (k : ℕ) (hk : leftCard p h s S T≤k) :
    (monotoneRecords pairs S T s).filter (fun x=>!x.side && decide (leftRank (monotoneRecords pairs S T s) x=k))=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
  cases v with
  | inl v =>
    simp only [side_inl,Bool.not_false,Bool.true_and,decide_eq_true_eq,leftRank_row]
    have hv := ((retainedMonotoneDiagram pairs S T s).rowOrder.symm v).isLt
    change _<leftCard p h s S T at hv
    omega
  | inr v => simp

lemma scan_range {W : Type*} (n m : ℕ) (hm : n≤m) (g : Fin n → W) (f : ℕ → List W)
    (hf : ∀i : Fin n,f i.val=[g i]) (hz : ∀k,n≤k → f k=[]) :
    (List.range m).flatMap f=List.ofFn g := by
  have hm' : m=n+(m-n) := by omega
  rw [hm',List.range_add,List.flatMap_append]
  have ht : ((List.range (m-n)).map (n+·)).flatMap f=[] := by
    rw [List.flatMap_eq_nil_iff]
    intro k hk
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hk
    exact hz _ (by omega)
  rw [ht,List.append_nil,←List.map_coe_finRange_eq_range (n:=n),List.flatMap_map]
  rw [List.ofFn_eq_map]
  have he : (fun i : Fin n=>f i.val)=(fun i=>[g i]) := funext hf
  rw [he]
  exact List.map_eq_flatMap.symm

lemma orderedLeft_correct {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) :
    orderedLeft (monotoneRecords pairs S T s)=List.ofFn (fun i : Fin (leftCard p h s S T)=>
      vertexRecord pairs (.inl ((retainedMonotoneDiagram pairs S T s).rowOrder i))) := by
  apply scan_range
  · simp only [monotoneRecords,List.length_map,Enumeration.length_eq_card,Fintype.card_sum,leftCard]
    omega
  · exact selected_row pairs S T
  · exact selected_row_above pairs S T

private lemma rows_cast {X Y : Type} [Fintype X] [Fintype Y] {R R' : X → Y → Prop}
    (hR : R=R') (h : MonotoneOrdering R=MonotoneOrdering R') (O : MonotoneOrdering R) :
    (cast h O).rows=O.rows := by subst R'; rfl
private lemma lo_cast {X Y : Type} [Fintype X] [Fintype Y] {R R' : X → Y → Prop}
    (hR : R=R') (h : MonotoneOrdering R=MonotoneOrdering R') (O : MonotoneOrdering R) :
    (cast h O).lo=O.lo := by subst R'; rfl
private lemma hi_cast {X Y : Type} [Fintype X] [Fintype Y] {R R' : X → Y → Prop}
    (hR : R=R') (h : MonotoneOrdering R=MonotoneOrdering R') (O : MonotoneOrdering R) :
    (cast h O).hi=O.hi := by subst R'; rfl

lemma queryOrdering_rows {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    (monotoneQueryOrdering pairs S T s).rows=(retainedMonotoneDiagram pairs S T s).rowOrder := by
  unfold monotoneQueryOrdering
  simp only [id_eq,eq_mpr_eq_cast]
  rw [rows_cast]
  · rfl
  · funext x y
    rw [retainedMonotoneDiagram_graph]
    rfl
lemma queryOrdering_lo {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    (monotoneQueryOrdering pairs S T s).lo = fun i=>min
      ((retainedMonotoneDiagram pairs S T s).upperBefore i)
      ((retainedMonotoneDiagram pairs S T s).lowerBefore i) := by
  unfold monotoneQueryOrdering
  simp only [id_eq,eq_mpr_eq_cast]
  rw [lo_cast]
  · rfl
  · funext x y
    rw [retainedMonotoneDiagram_graph]
    rfl
lemma queryOrdering_hi {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    (monotoneQueryOrdering pairs S T s).hi = fun i=>max
      ((retainedMonotoneDiagram pairs S T s).upperBefore i)
      ((retainedMonotoneDiagram pairs S T s).lowerBefore i) := by
  unfold monotoneQueryOrdering
  simp only [id_eq,eq_mpr_eq_cast]
  rw [hi_cast]
  · rfl
  · funext x y
    rw [retainedMonotoneDiagram_graph]
    rfl

/-- Literal rank-selection agrees with the query's actual sorted row order. -/
theorem orderedLeft_rows {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) :
    orderedLeft (monotoneRecords pairs S T s)=List.ofFn (fun i : Fin (leftCard p h s S T)=>
      vertexRecord pairs (.inl ((monotoneQueryOrdering pairs S T s).rows i))) := by
  rw [queryOrdering_rows]
  exact orderedLeft_correct pairs S T

lemma lowValue_correct {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (i : Fin (leftCard p h s S T)) :
    lowValue (monotoneRecords pairs S T s)
      (vertexRecord pairs (.inl ((retainedMonotoneDiagram pairs S T s).rowOrder i)))=
        (monotoneQueryOrdering pairs S T s).lo i := by
  rw [lowValue,upperCount_correct,lowerCount_correct,queryOrdering_lo]
  rfl
lemma highValue_correct {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (i : Fin (leftCard p h s S T)) :
    highValue (monotoneRecords pairs S T s)
      (vertexRecord pairs (.inl ((retainedMonotoneDiagram pairs S T s).rowOrder i)))=
        (monotoneQueryOrdering pairs S T s).hi i := by
  rw [highValue,upperCount_correct,lowerCount_correct,queryOrdering_hi]
  rfl

/-- The scanner emits the native monotone endpoint encoding, with no order or
encoding certificate in its input. Only balancing requires positive height. -/
theorem bits_correct {p h s : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p) (S T : State (2*p) p) :
    bits (monotoneRecords pairs S T s)=MonotoneEndpointEncoding.encode
      ⟨leftCard p h s S T,monotoneQueryEndpoints hh pairs S T s⟩ := by
  simp only [bits,orderedLeft_correct,List.length_ofFn,List.map_ofFn,Function.comp_def,
    lowValue_correct,highValue_correct,MonotoneEndpointEncoding.encode,MonotoneEndpointEncoding.rows,
    monotoneQueryEndpoints,MonotoneOrdering.endpoints]

end HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
