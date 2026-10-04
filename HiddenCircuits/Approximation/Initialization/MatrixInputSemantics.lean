import HiddenCircuits.Approximation.Initialization.MatrixInputProgram

/-! Polynomial size and clean work-bank interface of actual raw Tutte
matrix input construction. Bounds use bit width, never integer magnitude. -/
namespace HiddenCircuits.Approximation.Initialization.MatrixInputProgram
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

theorem number_length (B : ℕ) (source : BitString) (i : ℕ) :
    (Computability.encodeNat (TutteInteger.number B source i)).length ≤ B := by
  unfold TutteInteger.number
  rw [←normalize_eq_encode]
  exact (TapeWords.normalize_length _).trans (by rw [SamplerRuntime.TapeRead.prefix_length])

theorem entry_length {n : ℕ} (G : MatrixGraph n) (B : ℕ) (source : BitString) (i j : Fin n) :
    (signedBits (TutteInteger.matrix G.graph B source i j)).length ≤ B+1 := by
  have hb (s : Bool) (e : Fin (n*n)) :
      (signedBits (signedNat s (TutteInteger.number B source e.val))).length ≤ B+1 :=
    (TutteMatrixEmitter.signedNat_length s _).trans (Nat.add_le_add_right (number_length B source e.val) 1)
  by_cases ha : G.graph.Adj i j
  · by_cases hij : i<j
    · simpa [TutteInteger.matrix,TuttePolynomial.matrix,ha,hij,signedNat] using hb false (TuttePolynomial.index i j)
    · simpa [TutteInteger.matrix,TuttePolynomial.matrix,ha,hij,signedNat] using hb true (TuttePolynomial.index j i)
  · simp only [TutteInteger.matrix,TuttePolynomial.matrix,if_neg ha]
    change 1 ≤ B+1
    omega

theorem matrix_length {n : ℕ} (G : MatrixGraph n) (B : ℕ) (source : BitString) :
    (DeterminantRuntime.matrixInput (TutteInteger.matrix G.graph B source)).length ≤
      2*n+1+n*n*(2*(B+1)+2) := by
  let x : Fin (n*n) → ℕ := fun e => TutteInteger.number B source e.val
  have he : DeterminantRuntime.matrixInput (TutteInteger.matrix G.graph B source) =
      WordMatrixEmitter.queryBits n (TutteMatrixEmitter.entry G x) := (TutteMatrixEmitter.query_eq G x).symm
  rw [he]
  have hh := WordMatrixEmitter.query_length_bound n (B+1) (TutteMatrixEmitter.entry G x) (by
    intro i j hi hj
    simpa only [TutteMatrixEmitter.entry,dif_pos hi,dif_pos hj] using entry_length G B source ⟨i,hi⟩ ⟨j,hj⟩)
  omega

theorem timeBound_mono {n N B D T S L K : ℕ} (hn : n ≤ N) (hB : B ≤ D)
    (hT : T ≤ S) (hL : L ≤ K) : timeBound n B T L ≤ timeBound N D S K := by
  unfold timeBound TutteMatrixEmitter.timeBound
  gcongr

noncomputable def on {k : ℕ} (φ : Fin 23 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k n : ℕ} (φ : Fin 23 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (G : MatrixGraph n) (B : ℕ) (tape : BitString) (hs : s ∘ φ = state n G.bits tape B [] [] [] [] []) :
    ∃ t, (on φ).Executes g s (Function.update s (φ 4)
      (DeterminantRuntime.matrixInput (TutteInteger.matrix G.graph B tape))) t ∧
      t ≤ timeBound n B tape.length (n*n*(2*B+2)) := by
  obtain ⟨t,ht,hb⟩ := program_executes g G B tape
  refine ⟨t,?_,hb.trans (timeBound_mono le_rfl le_rfl le_rfl (TapeWords.encoded_length B (n*n) tape))⟩
  apply rename_executes_to program φ g ht hs
  · funext r
    simp only [Function.comp_apply,Function.update_apply,φ.injective.eq_iff]
    have hh := congrFun hs r
    simp only [Function.comp_apply] at hh
    rw [hh]
    fin_cases r <;> rfl
  · intro r hr
    exact Function.update_of_ne (hr 4).symm _ _

theorem on_queryFree {k : ℕ} (φ : Fin 23 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.Initialization.MatrixInputProgram
