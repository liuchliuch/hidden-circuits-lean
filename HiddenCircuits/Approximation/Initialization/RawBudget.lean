import HiddenCircuits.Approximation.Initialization.RawCoins
import HiddenCircuits.Approximation.SamplerRuntime.PartnerOutput

/-! Graph-only finite-tape initial matching, on the exact raw algorithm compiled
by the outer loop. The polynomial tape budget tolerates arbitrary extra padding. -/
namespace HiddenCircuits.Approximation.Initialization.RawExtraction
open Complexity SelfReduction SamplerRuntime

lemma ofFn_takeTape {a M : ℕ} (h : a≤M) (r : CoinTape M) :
    List.ofFn (ResidualTest.takeTape h r)=(List.ofFn r).take a := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left h]
  · intro i hi hi'
    simp only [List.getElem_ofFn,List.getElem_take,ResidualTest.takeTape,CoinLists.restrictTape]

lemma blocks_append {d m : ℕ} (r : Fin d → CoinTape m) (tail : BitString) :
    blocks r tail=blocks r []++tail := by simp [blocks]

lemma blocks_prefix {d m M : ℕ} (h : d*m≤M) (r : CoinTape M) :
    blocks (splitBlocks d m (ResidualTest.takeTape h r)) ((List.ofFn r).drop (d*m))=List.ofFn r := by
  rw [blocks_append,blocks_split,ofFn_takeTape,List.take_append_drop]

theorem run_prefix {b : ℕ} (G : MatrixGraph (b+1)) (k d fuel M : ℕ)
    (U : {U : Finset (Fin (b+1)) // U.card=2*d}) (r : CoinTape M)
    (π : Equiv.Perm (Fin (b+1))) (hf : d≤fuel) (hM : d*ResidualTest.bits b k≤M) :
    run G (b+1+k) fuel U.val (List.ofFn r) π=
      ForwardExtraction.run G.graph k d ⟨d,some U⟩
        (splitBlocks d (ResidualTest.bits b k) (ResidualTest.takeTape hM r)) π := by
  simpa only [blocks_prefix] using run_blocks G k d fuel U
    (splitBlocks d (ResidualTest.bits b k) (ResidualTest.takeTape hM r))
    ((List.ofFn r).drop (d*ResidualTest.bits b k)) π hf

theorem run_prefix_failure {b : ℕ} (G : MatrixGraph (b+1)) (k d fuel M : ℕ)
    (U : {U : Finset (Fin (b+1)) // U.card=2*d}) (π : Equiv.Perm (Fin (b+1)))
    (hf : d≤fuel) (hM : d*ResidualTest.bits b k≤M)
    (hU : 0<perfectMatchingCount (G.graph.induce (U.val : Set (Fin (b+1))))) :
    coinProbability M (fun r => run G (b+1+k) fuel U.val (List.ofFn r) π=none)≤(d:ℚ)/(2^k:ℚ) := by
  have he : coinProbability M (fun r => run G (b+1+k) fuel U.val (List.ofFn r) π=none)=
      coinProbability (d*ResidualTest.bits b k) (fun r => MatchingExtraction.runCoins G.graph k d ⟨d,some U⟩ r=none) := by
    simp only [run_prefix G k d fuel M U _ π hf hM,ForwardExtraction.run_none_iff]
    exact ResidualTest.probability_prefix hM (fun r => MatchingExtraction.runCoins G.graph k d ⟨d,some U⟩ r=none)
  rw [he]
  exact MatchingExtraction.runCoins_failure G.graph k d ⟨d,some U⟩ hU rfl

def randomBits (n k : ℕ) : ℕ := n^3*(2*n+k)

noncomputable def initialPermutation {n : ℕ} (G : MatrixGraph n) (k : ℕ) (source : BitString) :
    Option (Equiv.Perm (Fin n)) := run G (2*n+k) n Finset.univ source (Equiv.refl (Fin n))

theorem initialPermutation_valid {n : ℕ} (G : MatrixGraph n) (k : ℕ) (source : BitString)
    {π : Equiv.Perm (Fin n)} (h : initialPermutation G k source=some π) : PartialPartners.Valid G.graph ∅ π :=
  run_valid G _ _ _ _ _ _ (PartialPartners.initial G.graph) h

noncomputable def initialPartner {n : ℕ} (G : MatrixGraph n) (k : ℕ) (source : BitString) : Option (PerfectPartner G.graph) :=
  match h : initialPermutation G k source with
  | none => none
  | some π => some (PartialPartners.finish (initialPermutation_valid G k source h))

@[simp] theorem initialPartner_none_iff {n : ℕ} (G : MatrixGraph n) (k : ℕ) (source : BitString) :
    initialPartner G k source=none ↔ initialPermutation G k source=none := by
  unfold initialPartner
  split <;> simp_all

theorem initialPartner_empty {n : ℕ} (G : MatrixGraph n) (k : ℕ) (source : BitString)
    (h : ¬Nonempty (PerfectMatching G.graph)) : initialPartner G k source=none := by
  rw [initialPartner_none_iff]
  exact run_zero G _ _ source h

theorem initialPermutation_failure {n : ℕ} (G : MatrixGraph n) (k M : ℕ)
    (hM : randomBits n k≤M) (hG : Nonempty (PerfectMatching G.graph)) :
    coinProbability M (fun r => initialPermutation G k (List.ofFn r)=none)≤1/(2^k:ℚ) := by
  cases n with
  | zero =>
    have hu : (Finset.univ : Finset (Fin 0))=∅ := by ext i;exact Fin.elim0 i
    simp [initialPermutation,hu]
  | succ b =>
    obtain ⟨P⟩ := hG
    have hn := P.property.even_card
    simp only [Fintype.card_fin] at hn
    obtain ⟨d,hd⟩ := hn
    have hcard : (Finset.univ : Finset (Fin (b+1))).card=2*d := by simp;omega
    let U : {U : Finset (Fin (b+1)) // U.card=2*d} := ⟨Finset.univ,hcard⟩
    have hdepth : d≤b+1 := by omega
    have hcount : 0<perfectMatchingCount (G.graph.induce (U.val : Set (Fin (b+1)))) := by
      let Q := P.toPartner
      let Q' : PerfectPartner (G.graph.induce (U.val : Set (Fin (b+1)))) :=
        ⟨fun i => ⟨Q.val i.val,Finset.mem_univ _⟩,⟨by
          intro i;apply Subtype.ext;exact Q.property.1 i.val,by
          intro i;exact Q.property.2 i.val⟩⟩
      exact Fintype.card_pos_iff.mpr ⟨Q'.toMatching⟩
    have hneed : d*ResidualTest.bits b (b+1+k)≤M := by
      have hh := Nat.mul_le_mul_right (ResidualTest.bits b (b+1+k)) hdepth
      have he : (b+1)*ResidualTest.bits b (b+1+k)=randomBits (b+1) k := by
        unfold ResidualTest.bits randomBits;ring
      rw [he] at hh
      exact hh.trans hM
    have hh := run_prefix_failure G (b+1+k) d (b+1) M U (Equiv.refl _) hdepth hneed hcount
    have he : b+1+(b+1+k)=2*(b+1)+k := by omega
    rw [he] at hh
    refine hh.trans ?_
    have hp : (d:ℚ)≤(2:ℚ)^(b+1) := by
      have ha : (d:ℚ)≤(b+1:ℕ) := by exact_mod_cast hdepth
      have hb : ((b+1:ℕ):ℚ)≤(2:ℚ)^(b+1) := by exact_mod_cast (b+1).lt_two_pow_self.le
      exact ha.trans hb
    rw [pow_add]
    calc
      (d:ℚ)/(2^(b+1)*2^k)≤2^(b+1)/(2^(b+1)*2^k) := by gcongr
      _=1/(2^k:ℚ) := by field_simp

theorem initialPartner_failure {n : ℕ} (G : MatrixGraph n) (k M : ℕ)
    (hM : randomBits n k≤M) (hG : Nonempty (PerfectMatching G.graph)) :
    coinProbability M (fun r => initialPartner G k (List.ofFn r)=none)≤1/(2^k:ℚ) := by
  simpa only [initialPartner_none_iff] using initialPermutation_failure G k M hM hG

end HiddenCircuits.Approximation.Initialization.RawExtraction
