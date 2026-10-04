import HiddenCircuits.Approximation.Initialization.OuterLoop.Data
import HiddenCircuits.Complexity.OracleCleanup

/-! A real mask scan distinguishes a completed
permutation from an unfinished residual search, followed by literal cleanup. -/
namespace HiddenCircuits.Approximation.Initialization.OuterLoop.Finish
open Complexity Complexity.OracleBlock SamplerRuntime SelfReduction.Runtime
set_option maxHeartbeats 2000000

def work (N : ℕ) (payload mask source : BitString) (B : ℕ) (data : BitString)
    (L p : ℕ) (ok : BitString) : Store 51 :=
  Function.update (state N payload mask source B data L 0 ok) 8 (unary p)

def code {N : ℕ} : Option (Equiv.Perm (Fin N)) → BitString
  | none => []
  | some π => true::Output.witness π

def storageBound (N B L T : ℕ) : ℕ := 2*N^2+3*N+T+B+L+1

def timeBound (N B L T : ℕ) : ℕ :=
  8*N+9+(2*N^2+2*N+3)+5*(storageBound N B L T+3)+5

def ports : Fin 5 ↪ Fin 52 where
  toFun i := ![2,8,9,7,10] i
  inj' := by decide +kernel
noncomputable def detect : OracleBlock 51 := firstTrueOn ports
noncomputable def decideResult : OracleBlock 51 := branchPop 7 (push 5 true) (push 5 true) (clear 5)
noncomputable def cleanup : OracleBlock 51 := clearList [2,3,4,6,8]
noncomputable def program : OracleBlock 51 := seq detect (seq decideResult cleanup)

lemma detect_executes (g : BitString → ℕ) (N : ℕ) (payload mask source : BitString)
    (B : ℕ) (data : BitString) (L : ℕ) :
    ∃ t,detect.Executes g (state N payload mask source B data L 0 [])
      (work N payload mask source B data L (seekPos mask) [seekFound mask]) t ∧
      t≤8*mask.length+9 := by
  apply firstTrueOn_executes ports g _ _ mask
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 1 rfl) | exact False.elim (hi 3 rfl)

lemma decideResult_executes (g : BitString → ℕ) (N : ℕ) (payload mask source : BitString)
    (B : ℕ) (data : BitString) (L p : ℕ) (b : Bool) :
    ∃ t,decideResult.Executes g (work N payload mask source B data L p [b])
      (work N payload mask source B (if b then [] else true::data) L p []) t ∧
      t≤data.length+3 := by
  have hpop : ∀ b,Function.update (work N payload mask source B data L p [b]) (7:Fin 52) []=
      work N payload mask source B data L p [] := by
    intro b;funext i;fin_cases i <;> rfl
  cases b with
  | false =>
    have hp : (push (5:Fin 52) true).Executes g (work N payload mask source B data L p [])
        (work N payload mask source B (true::data) L p []) 1 := by
      convert push_executes g (5:Fin 52) true _ using 1
      funext i;fin_cases i <;> rfl
    refine ⟨3,branchPop_false (7:Fin 52) _ _ _ g rfl ?_,by omega⟩
    rw [hpop];exact hp
  | true =>
    have hp : (clear (5:Fin 52)).Executes g (work N payload mask source B data L p [])
        (work N payload mask source B [] L p []) (data.length+1) := by
      convert clear_executes g (5:Fin 52) _ using 1
      funext i;fin_cases i <;> rfl
    refine ⟨data.length+3,branchPop_true (7:Fin 52) _ _ _ g rfl ?_,by omega⟩
    rw [hpop];exact hp

lemma cleanup_executes (g : BitString → ℕ) (N : ℕ) (payload mask source data : BitString)
    (B L p T : ℕ) (hpayload : payload.length≤N^2) (hmask : mask.length≤N)
    (hsource : source.length≤T) (hdata : data.length≤2*N^2+2*N+1) (hp : p≤N) :
    ∃ t,cleanup.Executes g (work N payload mask source B data L p [])
      (state N payload [] [] 0 data 0 0 []) t ∧
      t≤5*(storageBound N B L T+3)+1 := by
  obtain ⟨t,ht,hb⟩ := clearList_executes g [2,3,4,6,8]
    (work N payload mask source B data L p []) (storageBound N B L T)
    (by intro i;fin_cases i <;> simp [work,state,storageBound] <;> omega)
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext i;fin_cases i <;> simp [eraseStore,work,state]

lemma code_result {N : ℕ} (U : Finset (Fin N)) (π : Equiv.Perm (Fin N)) :
    (if seekFound (MaskEnumerationSemantics.mask U) then [] else true::Output.witness π)=code (result U π) := by
  classical
  by_cases hU : U.Nonempty
  · have hf : seekFound (MaskEnumerationSemantics.mask U)=true := seekFound_retainedMask U hU
    rw [hf]
    simp [result,code,Finset.nonempty_iff_ne_empty.mp hU]
  · have he : U=∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    subst U
    simp [seekFound_eq_any,MaskEnumerationSemantics.mask,result,code]

/-- Every branch is total, including the empty zero-vertex witness. -/
theorem program_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N)
    (U : Finset (Fin N)) (source : BitString) (B : ℕ) (π : Equiv.Perm (Fin N)) (L T : ℕ)
    (hsource : source.length≤T) :
    ∃ t,program.Executes g
      (state N G.bits (MaskEnumerationSemantics.mask U) source B (Output.witness π) L 0 [])
      (state N G.bits [] [] 0 (code (result U π)) 0 0 []) t ∧ t≤timeBound N B L T := by
  let mask := MaskEnumerationSemantics.mask U
  obtain ⟨a,ha,hab⟩ := detect_executes g N G.bits mask source B (Output.witness π) L
  obtain ⟨b,hb,hbb⟩ := decideResult_executes g N G.bits mask source B (Output.witness π) L
    (seekPos mask) (seekFound mask)
  have hw := witness_length_le π
  have hm : mask.length=N := by simp [mask,MaskEnumerationSemantics.mask]
  have hp : seekPos mask≤N := by simpa only [hm] using seekPos_le_length mask
  have hdata : (if seekFound mask then [] else true::Output.witness π).length≤2*N^2+2*N+1 := by
    split <;> simp <;> omega
  obtain ⟨c,hc,hcb⟩ := cleanup_executes g N G.bits mask source
    (if seekFound mask then [] else true::Output.witness π) B L (seekPos mask) T
    (by simpa [pow_two] using G.length_bits.le) hm.le hsource hdata hp
  rw [code_result] at hc hb
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb hc),?_⟩
  rw [hm] at hab
  unfold timeBound
  omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (rename_queryFree _ _ firstTrueMask_queryFree)
  (seq_queryFree _ _ (branchPop_queryFree _ _ _ _ (push_queryFree _ _)
    (push_queryFree _ _) (clear_queryFree _)) (clearList_queryFree _))
end HiddenCircuits.Approximation.Initialization.OuterLoop.Finish
