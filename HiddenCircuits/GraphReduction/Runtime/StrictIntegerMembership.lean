import HiddenCircuits.GraphReduction.Runtime.StrictIntegerSemantics
import HiddenCircuits.GraphReduction.Runtime.CoordinateGraphProgram

/-! Machine-grounded #P membership for the literal strict integer-radius input.
The subtraction of one is executed on binary words before graph construction. -/
namespace HiddenCircuits.GraphReduction
open Complexity
namespace Runtime.StrictInteger
open OracleBlock Polynomial

noncomputable def program : OracleBlock 31 :=
  precompose (StrictIntegerHeader.program true) CoordinateGraph.program
noncomputable def time : Polynomial ℕ := precomposeTime (k:=31)
  StrictIntegerHeader.time CoordinateGraph.time StrictIntegerHeader.size
noncomputable def size : Polynomial ℕ := CoordinateGraph.size.comp StrictIntegerHeader.size

lemma program_executes (g : BitString → ℕ) (xs : BitString) :
    ∃s c,program.Executes g (Function.update (fun _=>[]) 0 xs) s c ∧s 0=bits xs ∧c≤time.eval xs.length := by
  apply precompose_executes _ _ g (StrictIntegerHeader.bits true) bits
    StrictIntegerHeader.time CoordinateGraph.time StrictIntegerHeader.size
  · intro x
    obtain ⟨c,hc,hb⟩ := StrictIntegerHeader.program_executes true g x
    exact ⟨_,c,hc,rfl,hb⟩
  · exact StrictIntegerHeader.size_bound true
  · intro x
    exact CoordinateGraph.program_executes g (StrictIntegerHeader.bits true x)

lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (StrictIntegerHeader.program_queryFree true)
    (seq_queryFree _ _ (cleanup_queryFree _) CoordinateGraph.program_queryFree)
lemma size_bound (xs : BitString) : (bits xs).length≤size.eval xs.length := by
  have h := (CoordinateGraph.size_bound (StrictIntegerHeader.bits true xs)).trans
    (polynomial_nat_eval_mono CoordinateGraph.size (StrictIntegerHeader.size_bound true xs))
  simpa only [size,eval_comp] using h
end Runtime.StrictInteger

/-- Total literal strict-distance counting on the bounded parser's labelled list.
On canonical positive-radius inputs this is exactly the paper's problem. -/
noncomputable def strictIntegerProblem : BitString → ℕ :=
  GraphInput.perfectMatchingProblem ∘ Runtime.StrictInteger.bits

theorem strictIntegerProblem_sharpP : SharpP strictIntegerProblem :=
  GraphVerifier.MatchingPullback.sharpP_of_graph_compiler Runtime.StrictInteger.program
    Runtime.StrictInteger.program_queryFree Runtime.StrictInteger.bits Runtime.StrictInteger.time Runtime.StrictInteger.size
    (Runtime.StrictInteger.program_executes (fun _=>0)) Runtime.StrictInteger.size_bound

theorem strictIntegerProblem_exact (xs : BitString) :
    strictIntegerProblem xs=perfectMatchingCount (Runtime.StrictInteger.graph xs).graph := by
  simp only [strictIntegerProblem,Function.comp_apply,Runtime.StrictInteger.bits_graph,
    GraphInput.perfectMatchingProblem,GraphInput.decode_encode,Runtime.StrictInteger.graphInput]

theorem strictIntegerProblem_oracle : StrictIntegerOracle strictIntegerProblem := by
  intro G R
  simp only [strictIntegerProblem,Function.comp_apply,Runtime.StrictInteger.bits_representation,
    GraphInput.perfectMatchingProblem,GraphInput.decode_encode]
/-- The raw extension has no perfect matching at a nonpositive radius unless
its decoded vertex list is empty. -/
theorem strictIntegerProblem_nonpositive_nonempty (xs : BitString)
    (hr : Runtime.StrictInteger.radius xs≤0)
    (hn : 0<(LooseWordList.words (Runtime.StrictInteger.data xs)).length) :
    strictIntegerProblem xs=0 := by
  rw [strictIntegerProblem_exact,perfectMatchingCount_eq_partners]
  letI : IsEmpty (PerfectPartner (Runtime.StrictInteger.graph xs).graph) := ⟨by
    intro p
    let v : Fin (LooseWordList.words (Runtime.StrictInteger.data xs)).length := ⟨0,hn⟩
    have h := p.property.2 v
    change Runtime.StrictInteger.edge xs v.val (p.val v).val=true at h
    rw [Runtime.StrictInteger.nonpositive_no_edges xs hr] at h
    contradiction⟩
  exact Fintype.card_of_isEmpty

/-- Direct literal interface: r is a positive integer supplied in the input,
coordinates are integers, and equality at distance r is excluded. -/
theorem strictIntegerProblem_on_integer_coordinates {n : ℕ} (r : ℤ) (hr:0<r) (x : Fin n → ℤ) :
    strictIntegerProblem (encodeBitList (BinaryArithmetic.signedBits r::
      List.ofFn (fun i=>BinaryArithmetic.signedBits (x i))))=
      perfectMatchingCount (strictIntegerGraph r x).graph :=
  strictIntegerProblem_oracle ⟨n,strictIntegerGraph r x⟩ (strictIntegerRepresentation r hr x)
end HiddenCircuits.GraphReduction
