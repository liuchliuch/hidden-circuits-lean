import HiddenCircuits.Complexity.DeterminantRuntime.GatherSemantics
import HiddenCircuits.Complexity.DeterminantRuntime.GatherBounds
import Mathlib.Algebra.BigOperators.Fin

/-! A literal diagonal-gather and signed-sum trace evaluator. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.Trace
open OracleBlock BinaryArithmetic Polynomial

def state (n : ℕ) (array result stride stream : BitString) : Store 15 := fun q =>
  if q.val = 0 then List.replicate n true else if q.val = 1 then array else
  if q.val = 2 then result else if q.val = 4 then stride else if q.val = 5 then stream else []

def store (n : ℕ) (array result : BitString) : Store 15 := state n array result [] []

def gatherPorts : Fin 14 ↪ Fin 16 where
  toFun := ![1,3,4,0,5,6,7,8,9,10,11,12,13,14]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def sumPorts : Fin 8 ↪ Fin 16 where
  toFun := ![2,6,7,8,9,10,11,5]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def setup : OracleBlock 15 := seq
  (copyOn 0 4 15 (by decide) (by decide) (by decide)) (push 4 true)
noncomputable def sumBlock : OracleBlock 15 := rename sumAccumulator sumPorts
noncomputable def program : OracleBlock 15 := seq setup (seq (Gather.on gatherPorts)
  (seq (clear 4) (seq (push 2 false) sumBlock)))

theorem setup_executes (g : BitString → ℕ) (n : ℕ) (array : BitString) :
    setup.Executes g (store n array [])
      (state n array [] (List.replicate (n+1) true) []) (5*n+5) := by
  have h1 : (copyOn (0 : Fin 16) 4 15 (by decide) (by decide) (by decide)).Executes g
      (store n array []) (state n array [] (List.replicate n true) []) (5*n+2) := by
    have h := copyOn_executes g (0 : Fin 16) 4 15 (by decide) (by decide) (by decide)
      (store n array []) rfl
    have he : Function.update (store n array []) 4 (List.replicate n true) =
        state n array [] (List.replicate n true) [] := by funext i; fin_cases i <;> rfl
    simpa only [show store n array [] 0 = List.replicate n true from rfl,
      show store n array [] 4 = [] from rfl, List.append_nil, List.length_replicate, he] using h
  have h2 : (push (4 : Fin 16) true).Executes g (state n array [] (List.replicate n true) [])
      (state n array [] (List.replicate (n+1) true) []) 1 := by
    convert push_executes g (4 : Fin 16) true (state n array [] (List.replicate n true) []) using 1
    funext i; fin_cases i <;> rfl
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

theorem gather_executes (g : BitString → ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    ∃ t, (Gather.on gatherPorts).Executes g
      (state n (encodeBitList (matrixWords A)) [] (List.replicate (n+1) true) [])
      (state n (encodeBitList (matrixWords A)) [] (List.replicate (n+1) true)
        (encodeBitList (List.ofFn fun i => signedBits (A i i)))) t ∧
      t ≤ Gather.timeBound (encodeBitList (matrixWords A)).length 0 (n+1) n := by
  obtain ⟨t,ht,hb⟩ := Gather.on_executes gatherPorts g (matrixWords A) 0 (n+1) n []
    (state n (encodeBitList (matrixWords A)) [] (List.replicate (n+1) true) [])
    (by funext i; fin_cases i <;> rfl)
  rw [gather_diagonal, List.append_nil] at ht
  have he : Function.update (state n (encodeBitList (matrixWords A)) [] (List.replicate (n+1) true) [])
      (gatherPorts 4) (encodeBitList (List.ofFn fun i => signedBits (A i i))) =
      state n (encodeBitList (matrixWords A)) [] (List.replicate (n+1) true)
        (encodeBitList (List.ofFn fun i => signedBits (A i i))) := by
    funext i; fin_cases i <;> rfl
  rw [he] at ht
  exact ⟨t,ht,hb⟩

theorem sum_executes (g : BitString → ℕ) (n : ℕ) (array : BitString) (zs : List ℤ) :
    ∃ t, sumBlock.Executes g (state n array (signedBits 0) [] (encodeBitList (zs.map signedBits)))
      (store n array (signedBits zs.sum)) t ∧
      t ≤ sumAccumulatorTime.eval (1+(encodeBitList (zs.map signedBits)).length) := by
  obtain ⟨t,ht,hb⟩ := sumAccumulator_polynomial g zs 0
  refine ⟨t,?_,?_⟩
  · apply rename_executes_to sumAccumulator sumPorts g ht
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [store,state,sumPorts,sumStore]
    · intro i hi; fin_cases i <;> first | exact (hi 0 rfl).elim | exact (hi 7 rfl).elim | rfl
  · simpa [operandStreamLength, signedBits, negative] using hb

noncomputable def timePolynomial : Polynomial ℕ := Gather.timePolynomial +
  sumAccumulatorTime.comp (2*X^2+1) + 10*X+30

theorem executes (g : BitString → ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    ∃ t, program.Executes g (store n (encodeBitList (matrixWords A)) [])
      (store n (encodeBitList (matrixWords A)) (signedBits A.trace)) t ∧
      t ≤ timePolynomial.eval (n+(encodeBitList (matrixWords A)).length+1) := by
  let arr := encodeBitList (matrixWords A)
  let zs := List.ofFn (fun i => A i i)
  let ds := encodeBitList (List.ofFn (fun i => signedBits (A i i)))
  obtain ⟨a,ha,hab⟩ := gather_executes g A
  have hc : (clear (4 : Fin 16)).Executes g (state n arr [] (List.replicate (n+1) true) ds)
      (state n arr [] [] ds) (n+2) := by
    have h := clear_executes g (4 : Fin 16) (state n arr [] (List.replicate (n+1) true) ds)
    have he : Function.update (state n arr [] (List.replicate (n+1) true) ds) 4 [] =
        state n arr [] [] ds := by funext i; fin_cases i <;> rfl
    simpa only [show state n arr [] (List.replicate (n+1) true) ds 4 = List.replicate (n+1) true from rfl,
      List.length_replicate, he] using h
  have hp : (push (2 : Fin 16) false).Executes g (state n arr [] [] ds)
      (state n arr (signedBits 0) [] ds) 1 := by
    convert push_executes g (2 : Fin 16) false (state n arr [] [] ds) using 1
    funext i; fin_cases i <;> rfl
  obtain ⟨b,hb,hbb⟩ := sum_executes g n arr zs
  have hz : zs.map signedBits = List.ofFn (fun i => signedBits (A i i)) := by
    simp [zs, Function.comp_def]
  have hsum : zs.sum = A.trace := by simp [zs, Matrix.trace, Matrix.diag_apply, List.sum_ofFn]
  rw [hz,hsum] at hb
  rw [hz] at hbb
  have h := seq_executes _ _ g (setup_executes g n arr)
    (seq_executes _ _ g ha (seq_executes _ _ g hc (seq_executes _ _ g hp hb)))
  refine ⟨_,h,?_⟩
  let N := n+arr.length+1
  have hga := Gather.timeBound_le_eval arr.length 0 (n+1) n N (by dsimp [N];omega)
    (by omega) (by dsimp [N];omega) (by dsimp [N];omega)
  have hd := Gather.encoded_words_length (matrixWords A) 0 (n+1) n
  rw [gather_diagonal] at hd
  have hdb : 1+ds.length ≤ 2*N^2+1 := by dsimp [N,ds,arr] at *;nlinarith
  have hsb := polynomial_nat_eval_mono sumAccumulatorTime hdb
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one]
  dsimp [N,ds,arr] at *
  omega

theorem queryFree : program.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (push_queryFree _ _))
  (seq_queryFree _ _ (Gather.on_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (push_queryFree _ _) (rename_queryFree _ _ sumAccumulator_queryFree))))

noncomputable def on {k : ℕ} (φ : Fin 16 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 16 ↪ Fin (k+1)) (g : BitString → ℕ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (s : Store k)
    (hs : s ∘ φ = store n (encodeBitList (matrixWords A)) []) :
    ∃ t, (on φ).Executes g s (Function.update s (φ 2) (signedBits A.trace)) t ∧
      t ≤ timePolynomial.eval (n+(encodeBitList (matrixWords A)).length+1) := by
  obtain ⟨t,ht,hb⟩ := executes g A
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update s (φ 2) (signedBits A.trace)) ∘ φ =
        Function.update (s ∘ φ) 2 (signedBits A.trace) := by
      funext i; simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i; fin_cases i <;> rfl
  · intro i hi; exact Function.update_of_ne (hi 2).symm _ _

theorem on_queryFree {k : ℕ} (φ : Fin 16 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ queryFree

end HiddenCircuits.Complexity.DeterminantRuntime.Trace
