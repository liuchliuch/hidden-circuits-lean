import HiddenCircuits.Approximation.Initialization.TutteEntry
import HiddenCircuits.Approximation.Initialization.WordMatrixEmitter
import HiddenCircuits.Complexity.DeterminantRuntime.Encoding
import HiddenCircuits.Complexity.MatrixEmitterGraph

/-! Signed integer Tutte matrix bytes emitted by the actual finite
entry callback and row-major serializer, in the determinant evaluator's format. -/
namespace HiddenCircuits.Approximation.Initialization.TutteMatrixEmitter
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

def entry {n : ℕ} (G : MatrixGraph n) (x : Fin (n*n) → ℕ) (i j : ℕ) : BitString :=
  if hi : i<n then if hj : j<n then
    signedBits (TuttePolynomial.matrix G.graph (fun e => (x e : ℤ)) ⟨i,hi⟩ ⟨j,hj⟩)
  else [false] else [false]

theorem signedNat_length (sign : Bool) (a : ℕ) :
    (signedBits (signedNat sign a)).length ≤ (Computability.encodeNat a).length+1 := by
  rw [←finishSigned_encode]
  unfold finishSigned
  split_ifs <;> simp_all

theorem entry_length {n : ℕ} (G : MatrixGraph n) (x : Fin (n*n) → ℕ) (i j : Fin n) :
    (entry G x i.val j.val).length ≤ (encodeBitList (TutteEntry.randomWords x)).length+1 := by
  have hb (sign : Bool) (e : Fin (n*n)) :
      (signedBits (signedNat sign (x e))).length ≤ (encodeBitList (TutteEntry.randomWords x)).length+1 :=
    (signedNat_length sign _).trans (Nat.add_le_add_right
      (member_length_le_encodeBitList (xs := TutteEntry.randomWords x)
        (show Computability.encodeNat (x e) ∈ TutteEntry.randomWords x from List.mem_ofFn.mpr ⟨e,rfl⟩)) 1)
  simp only [entry,dif_pos i.isLt,dif_pos j.isLt]
  by_cases ha : G.graph.Adj i j
  · by_cases hij : i<j
    · simpa [TuttePolynomial.matrix,ha,hij,signedNat] using hb false (TuttePolynomial.index i j)
    · simpa [TuttePolynomial.matrix,ha,hij,signedNat] using hb true (TuttePolynomial.index j i)
  · simp only [TuttePolynomial.matrix,if_neg ha]
    change 1 ≤ _+1
    omega

theorem words_eq {n : ℕ} (G : MatrixGraph n) (x : Fin (n*n) → ℕ) :
    WordMatrixEmitter.matrixWords n (entry G x) =
      DeterminantRuntime.matrixWords (TuttePolynomial.matrix G.graph (fun e => (x e : ℤ))) := by
  have he : (List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => entry G x i.val j.val) =
      (List.ofFn fun i : Fin n => List.ofFn fun j : Fin n =>
        signedBits (TuttePolynomial.matrix G.graph (fun e => (x e : ℤ)) i j)) := by
    congr 1
    funext i
    congr 1
    funext j
    simp [entry,i.isLt,j.isLt]
  unfold DeterminantRuntime.matrixWords
  rw [←he]
  simp_rw [MatrixEmitter.ofFn_nat]
  rw [MatrixEmitter.ofFn_nat n (fun i => (List.range n).map (entry G x i))]
  rfl

theorem query_eq {n : ℕ} (G : MatrixGraph n) (x : Fin (n*n) → ℕ) :
    WordMatrixEmitter.queryBits n (entry G x) =
      DeterminantRuntime.matrixInput (TuttePolynomial.matrix G.graph (fun e => (x e : ℤ))) := by
  simp only [WordMatrixEmitter.queryBits,DeterminantRuntime.matrixInput,words_eq]

def initial {n : ℕ} (G : MatrixGraph n) (x : Fin (n*n) → ℕ) : Store 20 :=
  MatrixEmitter.store n 0 0 [] [] [] [] (TutteEntry.params G.bits (encodeBitList (TutteEntry.randomWords x)))

noncomputable def program : OracleBlock 20 := WordMatrixEmitter.block TutteEntry.program

def timeBound (n L : ℕ) : ℕ := n*n*(500*(n+L+1)^3+10*(L+1)+24)+40*n+30

theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixGraph n) (x : Fin (n*n) → ℕ) :
    ∃ t, program.Executes g (initial G x)
      (Function.update (initial G x) 7
        (DeterminantRuntime.matrixInput (TuttePolynomial.matrix G.graph (fun e => (x e : ℤ))))) t ∧
      t ≤ timeBound n (encodeBitList (TutteEntry.randomWords x)).length := by
  have hB : ∀ g i j out inner outer, i<n → j<n → ∃ t,
      TutteEntry.program.Executes g
        (MatrixEmitter.store n i j [] out inner outer
          (TutteEntry.params G.bits (encodeBitList (TutteEntry.randomWords x))))
        (MatrixEmitter.store n i j (entry G x i j) out inner outer
          (TutteEntry.params G.bits (encodeBitList (TutteEntry.randomWords x)))) t ∧
      t ≤ 500*(n+(encodeBitList (TutteEntry.randomWords x)).length+1)^3 := by
    intro g i j out inner outer hi hj
    obtain ⟨t,ht,hb⟩ := TutteEntry.program_executes g G x ⟨i,hi⟩ ⟨j,hj⟩ out inner outer
    refine ⟨t,?_,hb⟩
    convert ht using 1 <;> funext r <;> fin_cases r <;>
      simp [TutteEntry.state,TutteEntry.params,MatrixEmitter.store,MatrixEmitter.port,entry,hi,hj]
  have hW : ∀ i j, i<n → j<n →
      (entry G x i j).length ≤ (encodeBitList (TutteEntry.randomWords x)).length+1 :=
    fun i j hi hj => entry_length G x ⟨i,hi⟩ ⟨j,hj⟩
  simpa only [query_eq] using WordMatrixEmitter.block_executes TutteEntry.program (entry G x) n
    (500*(n+(encodeBitList (TutteEntry.randomWords x)).length+1)^3)
    ((encodeBitList (TutteEntry.randomWords x)).length+1)
    (TutteEntry.params G.bits (encodeBitList (TutteEntry.randomWords x))) hB hW g

theorem program_queryFree : program.QueryFree :=
  WordMatrixEmitter.block_queryFree _ TutteEntry.program_queryFree

noncomputable def on {k : ℕ} (φ : Fin 21 ↪ Fin (k+1)) : OracleBlock k := rename program φ
theorem on_executes {k n : ℕ} (φ : Fin 21 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (G : MatrixGraph n) (x : Fin (n*n) → ℕ) (hs : s ∘ φ = initial G x) :
    ∃ t, (on φ).Executes g s (Function.update s (φ 7)
      (DeterminantRuntime.matrixInput (TuttePolynomial.matrix G.graph (fun e => (x e : ℤ))))) t ∧
      t ≤ timeBound n (encodeBitList (TutteEntry.randomWords x)).length := by
  obtain ⟨t,ht,hb⟩ := program_executes g G x
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · funext r
    simp only [Function.comp_apply,Function.update_apply,φ.injective.eq_iff]
    have hh := congrFun hs r
    simp only [Function.comp_apply] at hh
    rw [hh]
  · intro r hr
    exact Function.update_of_ne (hr 7).symm _ _
theorem on_queryFree {k : ℕ} (φ : Fin 21 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.Initialization.TutteMatrixEmitter
