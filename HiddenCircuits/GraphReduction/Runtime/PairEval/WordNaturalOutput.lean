import HiddenCircuits.GraphReduction.Runtime.PairEval.WordSolver
import HiddenCircuits.Circuit.Runtime.WordEvalHardness

/-! Convert the signed WordEval result into its natural oracle code. Only
positive signed zero loses its one redundant zero bit; nonzero codes survive. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.WordNaturalOutput
open Complexity OracleBlock BinaryArithmetic Polynomial
open Circuit.Runtime.WordEvalOracle
set_option maxHeartbeats 700000
noncomputable def restore (sign bit : Bool) : OracleBlock 0 := seq (push 0 bit) (push 0 sign)
noncomputable def magnitude (sign : Bool) : OracleBlock 0 := branchPop 0 skip (restore sign false) (restore sign true)
noncomputable def normalize : OracleBlock 0 := branchPop 0 skip (magnitude false) (magnitude true)
def store (xs : BitString) : Store 0 := fun _=>xs
lemma restore_executes (g : BitString→ℕ) (sign bit : Bool) (xs : BitString) :
    (restore sign bit).Executes g (store xs) (store (sign::bit::xs)) 4 := by
  have h1:(push (0:Fin 1) bit).Executes g (store xs) (store (bit::xs)) 1 := by
    convert push_executes g (0:Fin 1) bit (store xs) using 1;funext i;fin_cases i;rfl
  have h2:(push (0:Fin 1) sign).Executes g (store (bit::xs)) (store (sign::bit::xs)) 1 := by
    convert push_executes g (0:Fin 1) sign (store (bit::xs)) using 1;funext i;fin_cases i;rfl
  exact seq_executes _ _ g h1 h2
lemma pop_store (b : Bool) (xs : BitString) : Function.update (store (b::xs)) (0:Fin 1) xs=store xs := by
  funext i;fin_cases i;rfl
lemma magnitude_cons (g : BitString→ℕ) (sign bit : Bool) (xs : BitString) :
    (magnitude sign).Executes g (store (bit::xs)) (store (sign::bit::xs)) 6 := by
  cases bit
  · exact branchPop_false 0 _ _ _ g rfl (by rw [pop_store];exact restore_executes g sign false xs)
  · exact branchPop_true 0 _ _ _ g rfl (by rw [pop_store];exact restore_executes g sign true xs)
lemma normalize_executes (g : BitString→ℕ) (z : ℤ) :
    ∃c,normalize.Executes g (store (signedBits z)) (store (Computability.encodeNat (signedCode z))) c ∧ c≤8 := by
  rw [code_encode]
  by_cases hz:z=0
  · subst z
    refine ⟨5,?_,by decide⟩
    apply branchPop_false 0 _ _ _ g rfl
    have he:Function.update (store (signedBits 0)) (0:Fin 1) (Computability.encodeNat (Int.natAbs 0))=store [] := by
      funext i;fin_cases i;rfl
    rw [he,if_pos rfl]
    exact branchPop_empty 0 _ _ _ g rfl (skip_executes g (store []))
  · rw [if_neg hz]
    have hm:Computability.encodeNat z.natAbs≠[]:=by
      intro h
      exact hz (Int.natAbs_eq_zero.mp ((encodeNat_eq_nil_iff _).mp h))
    cases he:Computability.encodeNat z.natAbs with
    | nil => exact (hm he).elim
    | cons b bs =>
      cases hs:negative z
      · refine ⟨8,?_,by decide⟩
        simp only [signedBits,he,hs]
        exact branchPop_false 0 _ _ _ g rfl (by rw [pop_store];exact magnitude_cons g false b bs)
      · refine ⟨8,?_,by decide⟩
        simp only [signedBits,he,hs]
        exact branchPop_true 0 _ _ _ g rfl (by rw [pop_store];exact magnitude_cons g true b bs)

def embedding : Fin 1 ↪ Fin 98 where
  toFun _:=0
  inj' := by intro i j h;exact Subsingleton.elim i j
noncomputable def program : OracleBlock 97 := seq WordSolver.program (rename normalize embedding)
noncomputable def time : Polynomial ℕ := WordSolver.time+10

theorem program_executes (g : BitString→ℕ) (hg : WordCell.oracleSpec g) (w : WordInstance) :
    ∃c,program.Executes g (Function.update (fun _=>[]) 0 (wordBits w))
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (signedCode w.value.num))) c ∧ c≤time.eval (wordBits w).length := by
  obtain ⟨z,a,ha,hz,hab⟩:=WordSolver.program_executes g hg w
  have hn:w.value.num=z:=by rw [hz];simp
  obtain ⟨b,hb,hbb⟩:=normalize_executes g z
  have hnorm:(rename normalize embedding).Executes g (Function.update (fun _=>[]) 0 (signedBits z))
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (signedCode z))) b := by
    apply rename_executes_to normalize embedding g hb
    · funext i;fin_cases i;rfl
    · funext i;fin_cases i;rfl
    · intro i hi
      have h0:i≠0:=fun h=>hi 0 h.symm
      simp only [Function.update_of_ne h0]
  rw [hn]
  refine ⟨_,seq_executes _ _ g ha hnorm,?_⟩
  simp only [time,eval_add,eval_ofNat]
  omega
end HiddenCircuits.GraphReduction.Runtime.PairEval.WordNaturalOutput
