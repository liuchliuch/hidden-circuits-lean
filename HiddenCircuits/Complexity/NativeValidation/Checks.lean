import HiddenCircuits.Complexity.NativeValidation.Fields
import HiddenCircuits.Complexity.GraphVerifier.ReadOnlyLength

/-! Both native boundary masks are checked for exact header length, without
imposing a particle cardinality condition. Zero wires are permitted. -/
namespace HiddenCircuits.Complexity.NativeValidation.Checks
open OracleBlock GraphVerifier GraphVerifier.Runtime EvalValidation.Core
set_option maxHeartbeats 1000000
def headerPorts : Fin 4 ↪ Fin 32 where
  toFun i:=![5,10,11,6] i
  inj' := by decide +kernel
def lengthPorts (target : Bool) : Fin 6 ↪ Fin 32 where
  toFun i:=![if target then 3 else 2,5,6,8,9,10] i
  inj' := by cases target <;> decide +kernel
noncomputable def allHeader : OracleBlock 31 := seq (headerOn headerPorts) (seq (clear 10) collect)
noncomputable def lengthCheck (target : Bool) : OracleBlock 31 := seq (readLengthOn (lengthPorts target)) collect
noncomputable def tidy : OracleBlock 31 := seq (clear 2) (seq (clear 3) (moveOn 5 3 7 (by decide) (by decide) (by decide)))
noncomputable def program : OracleBlock 31 := seq allHeader (seq (lengthCheck false) (seq (lengthCheck true) tidy))
lemma allHeader_executes (g : BitString→ℕ) (input data source target flags hdr : BitString) :
    allHeader.Executes g (state input data source target flags hdr [])
      (state input data source target (hdr.all id::flags) hdr []) (6*hdr.length+11) := by
  let st:=state input data source target flags hdr []
  let mid:=Function.update (state input data source target flags hdr [hdr.all id]) (10:Fin 32) (List.replicate hdr.length true)
  have hh:(headerOn headerPorts).Executes g st mid (5*hdr.length+3) := by
    convert headerOn_executes headerPorts g st hdr (by funext i;fin_cases i <;> rfl) using 1
    funext i;fin_cases i <;> rfl
  have hz:(clear (10:Fin 32)).Executes g mid (state input data source target flags hdr [hdr.all id]) (hdr.length+1) := by
    convert clear_executes g (10:Fin 32) mid using 1
    · funext i;fin_cases i <;> rfl
    · simp [mid]
  convert seq_executes _ _ g hh (seq_executes _ _ g hz (collect_executes g input data source target flags hdr _)) using 1 <;> omega
lemma lengthCheck_executes (g : BitString→ℕ) (t : Bool) (input data source target flags hdr : BitString) :
    ∃c,(lengthCheck t).Executes g (state input data source target flags hdr [])
      (state input data source target (decide ((if t then target else source).length=hdr.length)::flags) hdr []) c ∧
      c≤13*((if t then target else source).length+hdr.length)+28 := by
  let st:=state input data source target flags hdr []
  obtain ⟨c,hc,hb⟩:=readLengthOn_executes (lengthPorts t) g st (if t then target else source) hdr
    (by funext i;cases t <;> fin_cases i <;> rfl)
  have he:Function.update st (lengthPorts t 2) [decide ((if t then target else source).length=hdr.length)]=
      state input data source target flags hdr [decide ((if t then target else source).length=hdr.length)] := by
    funext i;cases t <;> fin_cases i <;> rfl
  rw [he] at hc
  exact ⟨_,seq_executes _ _ g hc (collect_executes g input data source target flags hdr _),by omega⟩
lemma tidy_executes (g : BitString→ℕ) (input data source target flags hdr : BitString) :
    tidy.Executes g (state input data source target flags hdr []) (state input data [] hdr flags [] [])
      (source.length+target.length+6*hdr.length+11) := by
  have hs:(clear (2:Fin 32)).Executes g (state input data source target flags hdr [])
      (state input data [] target flags hdr []) (source.length+1) := by
    convert clear_executes g (2:Fin 32) (state input data source target flags hdr []) using 1
    funext i;fin_cases i <;> rfl
  have ht:(clear (3:Fin 32)).Executes g (state input data [] target flags hdr [])
      (state input data [] [] flags hdr []) (target.length+1) := by
    convert clear_executes g (3:Fin 32) (state input data [] target flags hdr []) using 1
    funext i;fin_cases i <;> rfl
  have hm:(moveOn (5:Fin 32) 3 7 (by decide) (by decide) (by decide)).Executes g
      (state input data [] [] flags hdr []) (state input data [] hdr flags [] []) (6*hdr.length+5) := by
    convert moveOn_executes g (5:Fin 32) 3 7 (by decide) (by decide) (by decide) (state input data [] [] flags hdr []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  convert seq_executes _ _ g hs (seq_executes _ _ g ht hm) using 1 <;> omega

def flags (source target hdr bs : BitString) : BitString :=
  decide (target.length=hdr.length)::decide (source.length=hdr.length)::hdr.all id::bs
theorem program_executes (g : BitString→ℕ) (input data source target bs hdr : BitString) :
    ∃c,program.Executes g (state input data source target bs hdr [])
      (state input data [] hdr (flags source target hdr bs) [] []) c ∧ c≤100*(source.length+target.length+hdr.length+1) := by
  have hh:=allHeader_executes g input data source target bs hdr
  obtain ⟨a,ha,hab⟩:=lengthCheck_executes g false input data source target (hdr.all id::bs) hdr
  obtain ⟨b,hb,hbb⟩:=lengthCheck_executes g true input data source target (decide (source.length=hdr.length)::hdr.all id::bs) hdr
  have ht:=tidy_executes g input data source target (flags source target hdr bs) hdr
  refine ⟨_,seq_executes _ _ g hh (seq_executes _ _ g ha (seq_executes _ _ g hb ht)),?_⟩
  simp only [Bool.false_eq_true,if_false,if_true] at hab hbb
  omega
end HiddenCircuits.Complexity.NativeValidation.Checks
