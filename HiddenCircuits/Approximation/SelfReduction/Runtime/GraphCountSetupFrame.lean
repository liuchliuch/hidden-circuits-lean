import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetupFront
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetupParameters
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetupHalve

/-! Seventy-three actual bit stacks shared with the count-loop core. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetup
open Complexity OracleBlock GraphVerifier GraphVerifier.Runtime
set_option maxHeartbeats 1500000

def input (raw : BitString) : Store 72 := fun i => if i.val=0 then raw else []
def parsed (raw : BitString) : Store 72 := fun i =>
  if i.val=0 then coins raw else if i.val=65 then graph raw
  else if i.val=72 then List.replicate (size raw) true
  else if i.val=36 then [(parse raw).ok] else if i.val=38 then [(parse (request raw)).ok] else []
def dimension (raw : BitString) : BitString := (parse (graph raw)).left

def validated (raw : BitString) : Store 72 := fun i =>
  if i.val=67 then dimension raw else if i.val=70 then [(GraphInput.decode (graph raw)).isSome]
  else if i.val=3 then (parse (graph raw)).right else parsed raw i

def validatedClean (raw : BitString) : Store 72 := fun i =>
  if i.val=67 then dimension raw else if i.val=70 then [(GraphInput.decode (graph raw)).isSome] else parsed raw i

def depth (raw : BitString) : ℕ := (dimension raw).length/2
def even (raw : BitString) : Bool := decide ((dimension raw).length%2=0)
def halved (raw : BitString) : Store 72 := fun i =>
  if i.val=67 then [] else if i.val=71 then List.replicate (depth raw) true
  else if i.val=68 then [even raw] else validatedClean raw i
def depthCopied (raw : BitString) : Store 72 :=
  Function.update (halved raw) 67 (List.replicate (depth raw) true)

def frontPorts : Fin 9 ↪ Fin 73 where
  toFun i := ![0,71,72,36,40,3,65,38,37] i
  inj' := by decide +kernel
def graphPorts : Fin 39 ↪ Fin 73 where
  toFun i := if i.val=0 then 65 else if i.val=1 then 70 else if i.val=2 then 3
    else if i.val=3 then 67 else if i.val=36 then 40 else if i.val=38 then 43
    else ⟨i.val,by omega⟩
  inj' := by decide +kernel
def halvePorts : Fin 3 ↪ Fin 73 where
  toFun i := ![67,71,68] i
  inj' := by decide +kernel

def globalPorts : Fin 12 ↪ Fin 73 where
  toFun i := ![72,2,59,62,63,64,66,39,42,3,4,5] i
  inj' := by decide +kernel

noncomputable def generated (raw : BitString) : Store 72 := fun i =>
  if i.val=2 then List.replicate ((parameterPolynomial 0).eval (size raw)) true
  else if i.val=59 then List.replicate ((parameterPolynomial 1).eval (size raw)) true
  else if i.val=62 then List.replicate ((parameterPolynomial 2).eval (size raw)) true
  else if i.val=63 then List.replicate ((parameterPolynomial 3).eval (size raw)) true
  else if i.val=64 then List.replicate ((parameterPolynomial 4).eval (size raw)) true
  else if i.val=66 then List.replicate ((parameterPolynomial 5).eval (size raw)) true
  else if i.val=39 then List.replicate ((parameterPolynomial 6).eval (size raw)) true
  else if i.val=42 then List.replicate ((parameterPolynomial 7).eval (size raw)) true
  else depthCopied raw i

noncomputable def tapeLong (raw : BitString) : Bool :=
  decide (SelfReduction.GraphCount.randomBitsPolynomial.eval (size raw)≤(coins raw).length)
noncomputable def guarded (raw : BitString) : Store 72 :=
  Function.update (Function.update (generated raw) 39 []) 41 [tapeLong raw]
noncomputable def hCleared (raw : BitString) : Store 72 := Function.update (guarded raw) 42 []
noncomputable def ready (raw : BitString) : Bool :=
  (parse raw).ok && (parse (request raw)).ok && (GraphInput.decode (graph raw)).isSome && tapeLong raw && even raw
noncomputable def output (raw : BitString) : Store 72 := fun i =>
  if i.val=69 then [ready raw] else if i.val=70 then [true]
  else if i.val=36 ∨ i.val=38 ∨ i.val=41 ∨ i.val=68 then [] else hCleared raw i

def tapePorts : Fin 5 ↪ Fin 73 where
  toFun i := ![0,39,3,4,41] i
  inj' := by decide +kernel
def allFive : List Bool → Bool
  | [a,b,c,d,e] => a&&b&&c&&d&&e
  | _ => false
noncomputable def parseBlock : OracleBlock 72 := rename front frontPorts
noncomputable def validateBlock : OracleBlock 72 := seq (rename SamplerRuntime.GraphParser.program graphPorts) (clear 3)
noncomputable def halveBlock : OracleBlock 72 := rename Halve.program halvePorts
noncomputable def depthBlock : OracleBlock 72 :=
  seq halveBlock (copyOn 71 67 3 (by decide) (by decide) (by decide))
noncomputable def parametersBlock : OracleBlock 72 := rename parameters globalPorts
noncomputable def guardBlock : OracleBlock 72 := rename tapeGuard tapePorts
noncomputable def finishBlock : OracleBlock 72 := seq (clear 42)
  (seq (decision 69 [36,38,70,41,68] allFive) (push 70 true))
noncomputable def program : OracleBlock 72 := seq parseBlock (seq validateBlock
  (seq depthBlock (seq parametersBlock (seq guardBlock finishBlock))))

lemma parseBlock_executes (g : BitString → ℕ) (raw : BitString) :
    ∃c,parseBlock.Executes g (input raw) (parsed raw) c ∧ c≤40*raw.length+100 := by
  obtain ⟨c,hc,hb⟩ := front_executes g raw
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ _ g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim | exact (hi 6 rfl).elim | exact (hi 7 rfl).elim

lemma validateBlock_executes (g : BitString → ℕ) (raw : BitString) :
    ∃c,validateBlock.Executes g (parsed raw) (validatedClean raw) c ∧
      c≤SamplerRuntime.GraphParser.time.eval (graph raw).length+(graph raw).length+3 := by
  obtain ⟨c,hc,hb⟩ := SamplerRuntime.GraphParser.program_executes g (graph raw)
  have hv : (rename SamplerRuntime.GraphParser.program graphPorts).Executes g (parsed raw) (validated raw) c := by
    apply rename_executes_to _ _ g hc
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim
  have h₁ := clear_executes g (3:Fin 73) (validated raw)
  have ho : Function.update (validated raw) (3:Fin 73) []=validatedClean raw := by
    funext i;fin_cases i <;> rfl
  rw [ho] at h₁
  refine ⟨_,seq_executes _ _ g hv h₁,?_⟩
  have hl := parse_lengths (graph raw)
  change c+((parse (graph raw)).right.length+1)+2≤_
  omega

lemma halveBlock_executes (g : BitString → ℕ) (raw : BitString) :
    halveBlock.Executes g (validatedClean raw) (halved raw)
      ((dimension raw).length+depth raw+2) := by
  apply rename_executes_to _ _ g (Halve.program_executes g (dimension raw))
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim

lemma depthBlock_executes (g : BitString → ℕ) (raw : BitString) :
    depthBlock.Executes g (validatedClean raw) (depthCopied raw)
      ((dimension raw).length+6*depth raw+6) := by
  have hc : (copyOn (71:Fin 73) 67 3 (by decide) (by decide) (by decide)).Executes g
      (halved raw) (depthCopied raw) (5*depth raw+2) := by
    simpa [depthCopied,halved,validatedClean,parsed] using copyOn_executes g (71:Fin 73) 67 3
      (by decide) (by decide) (by decide) (halved raw) rfl
  convert seq_executes _ _ g (halveBlock_executes g raw) hc using 1
  omega

lemma parametersBlock_executes (g : BitString → ℕ) (raw : BitString) :
    parametersBlock.Executes g (depthCopied raw) (generated raw) (parametersTime.eval (size raw)) := by
  apply rename_executes_to _ _ g (parameters_executes g (size raw))
  · funext i;fin_cases i <;> simp [globalPorts,depthCopied,halved,validatedClean,parsed,parameterState]
  · funext i;fin_cases i <;> simp [globalPorts,generated,depthCopied,halved,validatedClean,parsed,parameterState]
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim | exact (hi 4 rfl).elim | exact (hi 5 rfl).elim | exact (hi 6 rfl).elim | exact (hi 7 rfl).elim | exact (hi 8 rfl).elim

lemma guardBlock_executes (g : BitString → ℕ) (raw : BitString) :
    ∃c,guardBlock.Executes g (generated raw) (guarded raw) c ∧
      c≤30*((coins raw).length+SelfReduction.GraphCount.randomBitsPolynomial.eval (size raw)+1) := by
  obtain ⟨c,hc,hb⟩ := tapeGuard_executes g (coins raw)
    (List.replicate (SelfReduction.GraphCount.randomBitsPolynomial.eval (size raw)) true)
  refine ⟨c,?_,by simpa using hb⟩
  apply rename_executes_to _ _ g hc
  · funext i;fin_cases i <;> simp [tapePorts,generated,parameterPolynomial,depthCopied,halved,validatedClean,parsed,guardStore]
  · funext i;fin_cases i <;> simp [tapePorts,guarded,generated,parameterPolynomial,depthCopied,halved,validatedClean,parsed,guardStore,tapeLong]
  · intro i hi
    have h₄ : i≠(41:Fin 73) := (hi 4).symm
    have h₁ : i≠(39:Fin 73) := (hi 1).symm
    simp [guarded,h₄,h₁]
end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetup
