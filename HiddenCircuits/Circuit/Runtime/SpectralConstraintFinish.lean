import HiddenCircuits.Circuit.Runtime.SpectralDeltaItems
import HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalizeRuntime

/-! Concrete ratio serialization, complete work cleanup and canonical rational
normalization for the native two-spectral circuit evaluator. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralConstraint
open Complexity OracleBlock BinaryArithmetic Polynomial

def initial (xs : BitString) : Store 67:=Function.update (fun _=>[]) 0 xs
def ratioBits (z : RationalAccumulator.Ratio) : BitString:=pairBits (signedBits z.1) (signedBits z.2)
def pairMap : Fin 3 ↪ Fin 68 := ⟨fun i=>![12,11,24] i,by decide +kernel⟩
noncomputable def pair : OracleBlock 67:=PairSerialization.on pairMap
noncomputable def cleanup : OracleBlock 67:=cleanResult 12 24 (by decide) (by decide)
noncomputable def finishRatio : OracleBlock 67:=seq pair cleanup
noncomputable def finishTime : Polynomial ℕ:=10*X+9+72*(X+(10*X+9)+3)+3

def normalizationMap : Fin 16 ↪ Fin 68:=⟨fun i=>⟨i.val,by omega⟩,
  by intro i j h;exact Fin.ext (congrArg (fun z : Fin 68=>z.val) h)⟩
noncomputable def normalize : OracleBlock 67:=rename RationalNormalize.rawProgram normalizationMap
noncomputable def finish : OracleBlock 67:=seq finishRatio normalize
noncomputable def timeFinish : Polynomial ℕ:=finishTime+RationalNormalize.rawTime.comp (X+finishTime)+2

lemma initial_bound (xs : BitString) : ∀i,(initial xs i).length ≤ xs.length := by
  intro i;simp only [initial,Function.update_apply];split_ifs <;> simp
lemma finishRatio_executes (g : BitString→ℕ) (s : Store 67) (z : RationalAccumulator.Ratio) (B : ℕ)
    (h₁:s 11=signedBits z.1) (h₂:s 12=signedBits z.2) (h₃:s 24=[])
    (hB:∀i,(s i).length ≤ B) :
    ∃c,finishRatio.Executes g s (initial (ratioBits z)) c ∧ c ≤ finishTime.eval B := by
  have hp:=PairSerialization.on_executes pairMap g s (signedBits z.1) (signedBits z.2)
    (by funext i;fin_cases i <;> simp [pairMap,PairSerialization.state,Function.comp_def,h₁,h₂,h₃])
  let t:=Function.update (Function.update s (pairMap 1) []) (pairMap 0) (ratioBits z)
  change pair.Executes g s t (10*(signedBits z.1).length+9) at hp
  have ht:t 12=ratioBits z:=by simp [t,pairMap]
  obtain ⟨c,hc,hcb⟩:=cleanResult_executes g (12:Fin 68) 24 (by decide) (by decide) (by decide)
    t (B+(10*(signedBits z.1).length+9)) (hp.stack_bound hB)
  rw [ht] at hc
  refine ⟨_,seq_executes _ _ g hp hc,?_⟩
  have hlen:(signedBits z.1).length ≤ B:=by simpa only [h₁] using hB 11
  simp only [finishTime,eval_add,eval_mul,eval_X,eval_ofNat]
  nlinarith
lemma normalize_executes (g : BitString→ℕ) (z : RationalAccumulator.Ratio) :
    ∃c,normalize.Executes g (initial (ratioBits z))
      (initial (RationalOracleEncoding.bits (RationalAccumulator.value z))) c ∧
      c ≤ RationalNormalize.rawTime.eval (ratioBits z).length := by
  obtain ⟨c,hc,hb⟩:=RationalNormalize.on_executes normalizationMap g (initial (ratioBits z)) (ratioBits z)
    (by funext i;fin_cases i <;> rfl)
  refine ⟨c,?_,hb⟩
  simpa only [ratioBits,RationalNormalize.rawValue_pair,show normalizationMap 0=0 from rfl,initial,Function.update_idem,RationalAccumulator.value] using hc
lemma finish_executes (g : BitString→ℕ) (s : Store 67) (z : RationalAccumulator.Ratio) (B : ℕ)
    (h₁:s 11=signedBits z.1) (h₂:s 12=signedBits z.2) (h₃:s 24=[])
    (hB:∀i,(s i).length ≤ B) :
    ∃c,finish.Executes g s (initial (RationalOracleEncoding.bits (RationalAccumulator.value z))) c ∧
      c ≤ timeFinish.eval B := by
  obtain ⟨a,ha,hab⟩:=finishRatio_executes g s z B h₁ h₂ h₃ hB
  obtain ⟨b,hb,hbb⟩:=normalize_executes g z
  have hs:=ha.stack_bound hB (0:Fin 68)
  change (ratioBits z).length ≤ B+a at hs
  have hm:=polynomial_nat_eval_mono RationalNormalize.rawTime (hs.trans (Nat.add_le_add_left hab B))
  dsimp only at hm
  refine ⟨a+b+2,seq_executes _ _ g ha hb,?_⟩
  simp only [timeFinish,eval_add,eval_comp,eval_X,eval_ofNat]
  omega
end HiddenCircuits.Circuit.Runtime.SpectralConstraint
