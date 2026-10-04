import HiddenCircuits.Complexity.FinalCountRuntime
import HiddenCircuits.Complexity.BinaryArithmetic.RationalAccumulator
import HiddenCircuits.Complexity.OracleMove
import HiddenCircuits.Complexity.PolynomialBounds

/-! Exact division of the actual source accumulator,
followed by full physical register cleanup and canonical natural output. -/
namespace HiddenCircuits.Circuit.Runtime.SourceFinalization
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial

def port (k : ℕ) (i : Fin 64) : Fin (k+70) := ⟨i.val,by omega⟩
def divisionEmbedding (k : ℕ) : Fin 9 ↪ Fin (k+70) where
  toFun i := port k ((![11,12,24,25,26,27,28,29,30] : Fin 9→Fin 64) i)
  inj' := by
    intro i j h
    have hv:=congrArg Fin.val h
    fin_cases i <;> fin_cases j <;> simp_all [port]
noncomputable def division (k : ℕ) : OracleBlock (k+69) := rename FinalCountRuntime.program (divisionEmbedding k)
noncomputable def cleanup (k : ℕ) : OracleBlock (k+69) := cleanResult (port k 11) (port k 24)
  (by intro h;have h':=congrArg Fin.val h;norm_num [port] at h')
  (by intro h;have h':=congrArg Fin.val h;norm_num [port] at h')
noncomputable def program (k : ℕ) : OracleBlock (k+69) := seq (division k) (cleanup k)
noncomputable def divisionTime : Polynomial ℕ := FinalCountRuntime.time.comp (2*X)
noncomputable def time (k : ℕ) : Polynomial ℕ := divisionTime+(C (k+74))*(X+divisionTime+3)+3

theorem executes (k : ℕ) (g : BitString → ℕ) (s : Store (k+69)) (acc : ℤ×ℤ) (z B : ℕ)
    (hs : s∘divisionEmbedding k=binaryStore (signedBits acc.1) (signedBits acc.2))
    (hbound : ∀i,(s i).length≤B) (hne : acc.2≠0)
    (hvalue : RationalAccumulator.value acc=(z:ℚ)) :
    ∃c, (program k).Executes g s (Function.update (fun _ : Fin (k+70)=>[]) 0 (Computability.encodeNat z)) c ∧
      c≤(time k).eval B := by
  have hd : (acc.2:ℚ)≠0 := by exact_mod_cast hne
  have hratio : (acc.1:ℚ)=(z:ℚ)*(acc.2:ℚ) := (div_eq_iff hd).mp hvalue
  have ha : acc.1=(z:ℤ)*acc.2 := by exact_mod_cast hratio
  obtain ⟨c,hc,hcb⟩ := FinalCountRuntime.program_executes g acc.1 acc.2 z hne ha
  have hr := rename_binary_executes FinalCountRuntime.program (divisionEmbedding k) g s
    (signedBits acc.1) (signedBits acc.2) (Computability.encodeNat z) c hc hs
  have h0 := congrFun hs 0
  have h1 := congrFun hs 1
  change s (divisionEmbedding k 0)=signedBits acc.1 at h0
  change s (divisionEmbedding k 1)=signedBits acc.2 at h1
  have haB : (signedBits acc.1).length≤B := by rw [←h0];exact hbound _
  have hbB : (signedBits acc.2).length≤B := by rw [←h1];exact hbound _
  have hmono := polynomial_nat_eval_mono FinalCountRuntime.time (show (signedBits acc.1).length+(signedBits acc.2).length≤2*B by omega)
  dsimp only at hmono
  have hcB : c≤divisionTime.eval B := by
    simp only [divisionTime,eval_comp,eval_mul,eval_ofNat,eval_X]
    exact hcb.trans hmono
  have hsize := hr.stack_bound hbound
  dsimp only [config] at hsize
  obtain ⟨d,hd,hdb⟩ := cleanResult_executes g (port k 11) (port k 24)
    (by intro h;have h':=congrArg Fin.val h;norm_num [port] at h')
    (by intro h;have h':=congrArg Fin.val h;norm_num [port] at h')
    (by intro h;have h':=congrArg Fin.val h;norm_num [port] at h')
    _ (B+c) hsize
  have hout : (Function.update (Function.update s (divisionEmbedding k 0) (Computability.encodeNat z))
      (divisionEmbedding k 1) []) (port k 11)=Computability.encodeNat z := by
    simp [divisionEmbedding,port,Fin.ext_iff]
  rw [hout] at hd
  refine ⟨c+d+2,seq_executes _ _ g hr hd,?_⟩
  have hk : k+69+5=k+74 := by omega
  rw [hk] at hdb
  have hm := Nat.mul_le_mul_left (k+74) (show B+c+3≤B+divisionTime.eval B+3 by omega)
  simp only [time,eval_add,eval_mul,eval_C,eval_X,eval_ofNat]
  omega
end HiddenCircuits.Circuit.Runtime.SourceFinalization
