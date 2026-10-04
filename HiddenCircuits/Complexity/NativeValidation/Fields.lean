import HiddenCircuits.Complexity.NativeValidation.Semantics
import HiddenCircuits.Complexity.EvalValidation.Header

/-! Preserve and parse the native source mask, target mask and unary wire
header by three actual self-delimiting pair parsers. -/
namespace HiddenCircuits.Complexity.NativeValidation.Fields
open OracleBlock GraphVerifier GraphVerifier.Runtime EvalValidation.Core
set_option maxHeartbeats 1000000
def targetPorts : Fin 4 ↪ Fin 32 where
  toFun i:=![1,3,7,6] i
  inj' := by decide +kernel
def headerPorts : Fin 4 ↪ Fin 32 where
  toFun i:=![1,5,7,6] i
  inj' := by decide +kernel
noncomputable def target : OracleBlock 31 := seq (unpairOn targetPorts) collect
noncomputable def header : OracleBlock 31 := seq (unpairOn headerPorts) collect
noncomputable def program : OracleBlock 31 := seq EvalValidation.Header.readHeader (seq target header)
def parsedFlags (xs : BitString) : BitString := [(Semantics.third xs).ok,(Semantics.second xs).ok,(Semantics.first xs).ok]
def output (xs : BitString) : Store 31 := state xs (Semantics.payload xs) (Semantics.source xs)
  (Semantics.target xs) (parsedFlags xs) (Semantics.header xs) []
lemma target_executes (g : BitString→ℕ) (input data source flags : BitString) :
    ∃c,target.Executes g (state input data source [] flags [] [])
      (state input (parse data).right source (parse data).left ((parse data).ok::flags) [] []) c ∧ c≤3*data.length+10 := by
  have hp:(unpairOn targetPorts).Executes g (state input data source [] flags [] [])
      (state input (parse data).right source (parse data).left flags [] [(parse data).ok])
      (parseCost data+2*(parse data).left.length+1) := by
    apply unpairOn_executes targetPorts g _ _ data
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have h1:i.val≠1:=by intro h;exact hi 0 (Fin.ext h.symm)
      have h3:i.val≠3:=by intro h;exact hi 1 (Fin.ext h.symm)
      have h6:i.val≠6:=by intro h;exact hi 3 (Fin.ext h.symm)
      simp only [state,h1,h3,h6,if_false]
  refine ⟨_,seq_executes _ _ g hp (collect_executes g input (parse data).right source (parse data).left flags [] _),?_⟩
  have h:=unpair_cost_bound data
  omega
lemma header_executes (g : BitString→ℕ) (input data source target flags : BitString) :
    ∃c,header.Executes g (state input data source target flags [] [])
      (state input (parse data).right source target ((parse data).ok::flags) (parse data).left []) c ∧ c≤3*data.length+10 := by
  have hp:(unpairOn headerPorts).Executes g (state input data source target flags [] [])
      (state input (parse data).right source target flags (parse data).left [(parse data).ok])
      (parseCost data+2*(parse data).left.length+1) := by
    apply unpairOn_executes headerPorts g _ _ data
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have h1:i.val≠1:=by intro h;exact hi 0 (Fin.ext h.symm)
      have h5:i.val≠5:=by intro h;exact hi 1 (Fin.ext h.symm)
      have h6:i.val≠6:=by intro h;exact hi 3 (Fin.ext h.symm)
      simp only [state,h1,h5,h6,if_false]
  refine ⟨_,seq_executes _ _ g hp (collect_executes g input (parse data).right source target flags (parse data).left _),?_⟩
  have h:=unpair_cost_bound data
  omega
lemma lengths (xs : BitString) :
    (Semantics.source xs).length≤xs.length ∧ (Semantics.target xs).length≤xs.length ∧
    (Semantics.header xs).length≤xs.length ∧ (Semantics.payload xs).length≤xs.length := by
  have h1:=parse_lengths xs
  have h2:=parse_lengths (Semantics.first xs).right
  have h3:=parse_lengths (Semantics.second xs).right
  exact ⟨h1.1,h2.1.trans h1.2,h3.1.trans (h2.2.trans h1.2),h3.2.trans (h2.2.trans h1.2)⟩
theorem program_executes (g : BitString→ℕ) (xs : BitString) :
    ∃c,program.Executes g (Function.update (fun _=>[]) 0 xs) (output xs) c ∧ c≤20*xs.length+100 := by
  obtain ⟨a,ha,hab⟩:=EvalValidation.Header.readHeader_executes g xs
  obtain ⟨b,hb,hbb⟩:=target_executes g xs (Semantics.first xs).right (Semantics.source xs) [(Semantics.first xs).ok]
  obtain ⟨c,hc,hcb⟩:=header_executes g xs (Semantics.second xs).right (Semantics.source xs) (Semantics.target xs)
    [(Semantics.second xs).ok,(Semantics.first xs).ok]
  have hs:state xs [] [] [] [] [] []=Function.update (fun _=>[]) 0 xs:=by funext i;fin_cases i <;> rfl
  rw [hs] at ha
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb hc),?_⟩
  have h1: (Semantics.first xs).right.length≤xs.length:=(parse_lengths xs).2
  have h2: (Semantics.second xs).right.length≤xs.length:=(parse_lengths (Semantics.first xs).right).2.trans h1
  omega
end HiddenCircuits.Complexity.NativeValidation.Fields
