import HiddenCircuits.GraphReduction.Runtime.UnitOrderSemantics
import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRoundsCorrect

/-! The physically accumulated original-label array is exactly the reverse
of the verified list recognizer's order. The result is a full umbrella order
precisely on ordinary unit-interval graphs. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitOrderSemantics
open Complexity DH.Runtime.PairCheck

lemma savedOrder_ofGraph {n : ℕ} (G : MatrixGraph n) (A : Vector Bool n)
    (b : UnitRecognitionRoots.Best n) :
    savedOrder (MatrixData.ofGraph G) A b =
      (b.map (fun r => (UnitIntervalBitRecognition.component G.graph A.toList r).reverse)).getD [] := by
  cases b with
  | none => rfl
  | some root => simp only [savedOrder,Option.map_some,Option.getD_some,
      UnitRecognitionComponent.component_order_ofGraph]

/-- Exact orientation for every successful search and every existing accumulator. -/
theorem run_search {n : ℕ} (G : MatrixGraph n) (fuel : ℕ) (A : Vector Bool n)
    (acc ls : List (Fin n))
    (h : UnitIntervalBitRecognition.search G.graph fuel A.toList = some ls) :
    (run (MatrixData.ofGraph G) fuel A acc).2 = ls.reverse ++ acc := by
  induction fuel generalizing A acc ls with
  | zero =>
    simp only [UnitIntervalBitRecognition.search] at h
    split at h
    · cases h; rfl
    · contradiction
  | succ fuel ih =>
    by_cases he : UnitIntervalBitMasks.count (n:=n) A.toList = 0
    · have hl : ls = [] := by
        simpa only [UnitIntervalBitRecognition.search,he,if_true,Option.some.injEq] using h.symm
      subst ls
      have hr : UnitRecognitionRoots.find (MatrixData.ofGraph G) A = none := by
        rw [UnitRecognitionRoots.find_ofGraph]
        exact UnitIntervalResidualRecognition.goodRoot_empty G.graph A.toList he
      rw [run_stuck _ _ _ _ hr]
      rfl
    · cases hr : UnitIntervalBitRecognition.goodRoot G.graph A.toList with
      | none => simp [UnitIntervalBitRecognition.search,he,hr] at h
      | some root =>
        simp only [UnitIntervalBitRecognition.search,he,if_false,hr] at h
        obtain ⟨rest,hrest,hls⟩ := Option.map_eq_some_iff.mp h
        subst ls
        have hfind : UnitRecognitionRoots.find (MatrixData.ofGraph G) A = some root :=
          (UnitRecognitionRoots.find_ofGraph G A).trans hr
        rw [run,hfind]
        have hres := UnitRecognitionComponent.component_remaining_ofGraph G A root
        have hh := ih (UnitRecognitionComponent.component (MatrixData.ofGraph G) A root).remaining
          (savedOrder (MatrixData.ofGraph G) A (some root) ++ acc) rest
          (by simpa only [hres] using hrest)
        simpa only [UnitRecognitionRoots.residual,savedOrder_ofGraph,Option.map_some,
          Option.getD_some,List.reverse_append,List.append_assoc] using hh

/-- Accepted output is the reverse of the ordinary list recognizer's output. -/
theorem recognize_ofGraph_eq {n : ℕ} (G : MatrixGraph n) :
    recognize (MatrixData.ofGraph G) =
      (UnitIntervalBitRecognition.recognize G.graph).map List.reverse := by
  have hacc : UnitRecognitionRounds.accepts (MatrixData.ofGraph G) = true ↔
      (UnitIntervalBitRecognition.recognize G.graph).isSome = true :=
    (UnitRecognitionRounds.accepts_ofGraph_iff G).trans
      (UnitIntervalBitRecognition.recognize_iff G.graph).symm
  cases hs : UnitIntervalBitRecognition.recognize G.graph with
  | none =>
    have ha : UnitRecognitionRounds.accepts (MatrixData.ofGraph G) = false := by
      cases hb : UnitRecognitionRounds.accepts (MatrixData.ofGraph G) with
      | false => rfl
      | true => have := hacc.mp hb; simp [hs] at this
    simp [recognize,ha]
  | some ls =>
    have ha : UnitRecognitionRounds.accepts (MatrixData.ofGraph G) = true :=
      hacc.mpr (by simp [hs])
    have hout : order (MatrixData.ofGraph G) = ls.reverse := by
      simpa only [order,List.append_nil] using
        run_search G n (Vector.replicate n true) [] ls hs
    simp [recognize,ha,hout]

/-- Soundness includes no duplicates, all original labels, and the umbrella law. -/
theorem recognize_ofGraph_sound {n : ℕ} (G : MatrixGraph n) (ls : List (Fin n))
    (h : recognize (MatrixData.ofGraph G) = some ls) :
    ls.Nodup ∧ (∀ v, v ∈ ls) ∧ UnitIntervalOrder.ListUmbrella G.graph ls := by
  rw [recognize_ofGraph_eq] at h
  obtain ⟨forward,hforward,rfl⟩ := Option.map_eq_some_iff.mp h
  change UnitIntervalBitRecognition.search G.graph n (List.replicate n true) = some forward at hforward
  rw [UnitIntervalBitRecognition.search_eq G.graph n _ (by simp),
    UnitIntervalBitRecognition.active_all] at hforward
  obtain ⟨hn,hcover,hu⟩ := UnitIntervalMaskedRecognition.search_sound G.graph n Finset.univ forward hforward
  refine ⟨by simpa using hn,?_,(UnitIntervalUmbrellaScan.listUmbrella_reverse_iff G.graph forward).mpr hu⟩
  intro v
  apply List.mem_reverse.mpr
  apply List.mem_toFinset.mp
  rw [hcover]
  exact Finset.mem_univ v

/-- The graph-to-order output succeeds exactly on the natural real class. -/
theorem recognize_ofGraph_iff {n : ℕ} (G : MatrixGraph n) :
    (recognize (MatrixData.ofGraph G)).isSome = true ↔
      RealUnitInterval.UnitIntervalGraph G.graph := by
  rw [recognize_ofGraph_eq,Option.isSome_map]
  exact UnitIntervalBitRecognition.recognize_iff G.graph

/-- Empty final residual suffices for a full umbrella order, including the
empty graph and arbitrary disconnected unit-interval graphs. -/
theorem order_ofGraph_sound {n : ℕ} (G : MatrixGraph n)
    (h : UnitRecognitionRounds.accepts (MatrixData.ofGraph G) = true) :
    (order (MatrixData.ofGraph G)).Nodup ∧
      (∀ v, v ∈ order (MatrixData.ofGraph G)) ∧
      UnitIntervalOrder.ListUmbrella G.graph (order (MatrixData.ofGraph G)) :=
  recognize_ofGraph_sound G _ (by simp [recognize,h])

/-- No supplied order, representation, or certificate: the original-n round
computation itself supplies a valid output on every graph in the class. -/
theorem order_ofGraph_correct {n : ℕ} (G : MatrixGraph n)
    (h : RealUnitInterval.UnitIntervalGraph G.graph) :
    (order (MatrixData.ofGraph G)).Nodup ∧
      (∀ v, v ∈ order (MatrixData.ofGraph G)) ∧
      UnitIntervalOrder.ListUmbrella G.graph (order (MatrixData.ofGraph G)) :=
  order_ofGraph_sound G ((UnitRecognitionRounds.accepts_ofGraph_iff G).mpr h)

/-- The validity of the computed output itself characterizes the graph class. -/
theorem order_ofGraph_spec_iff {n : ℕ} (G : MatrixGraph n) :
    ((order (MatrixData.ofGraph G)).Nodup ∧
      (∀ v, v ∈ order (MatrixData.ofGraph G)) ∧
      UnitIntervalOrder.ListUmbrella G.graph (order (MatrixData.ofGraph G))) ↔
      RealUnitInterval.UnitIntervalGraph G.graph := by
  constructor
  · rintro ⟨hn,hc,hu⟩
    exact ⟨(UnitIntervalOrder.representationOfList G.graph _ hn hc hu).toReal⟩
  · exact order_ofGraph_correct G

/-- The successful output has exactly one occurrence of each original label. -/
theorem order_ofGraph_length {n : ℕ} (G : MatrixGraph n)
    (h : UnitRecognitionRounds.accepts (MatrixData.ofGraph G) = true) :
    (order (MatrixData.ofGraph G)).length = n := by
  obtain ⟨hn,hcover,_⟩ := order_ofGraph_sound G h
  have he : (order (MatrixData.ofGraph G)).toFinset = Finset.univ := by
    ext v
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact hcover v
  rw [←List.toFinset_card_of_nodup hn,he]
  simp

/-- Direct statement at the accumulated machine state's final residual port. -/
theorem final_empty_order_sound {n : ℕ} (G : MatrixGraph n)
    (h : (run (MatrixData.ofGraph G) n (Vector.replicate n true) []).1.toList.all Bool.not = true) :
    (order (MatrixData.ofGraph G)).Nodup ∧
      (∀ v, v ∈ order (MatrixData.ofGraph G)) ∧
      UnitIntervalOrder.ListUmbrella G.graph (order (MatrixData.ofGraph G)) := by
  apply order_ofGraph_sound G
  simpa only [run_remaining,UnitRecognitionRounds.accepts] using h

end HiddenCircuits.GraphReduction.Runtime.UnitOrderSemantics
