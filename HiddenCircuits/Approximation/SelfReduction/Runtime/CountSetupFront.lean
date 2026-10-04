import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserProgram
import HiddenCircuits.Approximation.Schemes

/-! The real raw pair/request parser. The ignored precision payload is discarded
only after the original request length has been measured independently of coins. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetup
open Complexity OracleBlock GraphVerifier GraphVerifier.Runtime
set_option maxHeartbeats 800000

def request (raw : BitString) : BitString := (parse raw).left
def coins (raw : BitString) : BitString := (parse raw).right
def graph (raw : BitString) : BitString := (parse (request raw)).left
def size (raw : BitString) : ℕ := (request raw).length

def frontInput (raw : BitString) : Store 8 := fun i => if i.val=0 then raw else []
def frontParsed (raw : BitString) : Store 8 := fun i =>
  if h:i.val<8 then twoParseResult raw ⟨i.val,h⟩ else []
def frontMeasured (raw : BitString) : Store 8 :=
  Function.update (Function.update (frontParsed raw) 2 (List.replicate (size raw) true)) 8 [(request raw).all id]
def frontOutput (raw : BitString) : Store 8 := fun i =>
  if i.val=0 then coins raw else if i.val=2 then List.replicate (size raw) true
  else if i.val=3 then [(parse raw).ok] else if i.val=6 then graph raw
  else if i.val=7 then [(parse (request raw)).ok] else []
def frontPairPorts : Fin 8 ↪ Fin 9 where
  toFun i := i.castAdd 1
  inj' := by intro i j h; exact Fin.ext (congrArg (fun i : Fin 9 => i.val) h)
def frontLengthPorts : Fin 4 ↪ Fin 9 where
  toFun i := ![1,2,5,8] i
  inj' := by decide +kernel
noncomputable def front : OracleBlock 8 := seq (rename twoParseBlock frontPairPorts)
  (seq (headerOn frontLengthPorts) (seq (clear 1) (seq (clear 4) (clear 8))))

lemma front_parse (g : BitString → ℕ) (raw : BitString) :
    (rename twoParseBlock frontPairPorts).Executes g (frontInput raw) (frontParsed raw) (twoParseCost raw) := by
  apply rename_executes_to _ _ g (twoParse_executes g raw)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 3 rfl).elim | exact (hi 4 rfl).elim | exact (hi 6 rfl).elim | exact (hi 7 rfl).elim

lemma front_measure (g : BitString → ℕ) (raw : BitString) :
    (headerOn frontLengthPorts).Executes g (frontParsed raw) (frontMeasured raw) (5*size raw+3) := by
  exact headerOn_executes frontLengthPorts g (frontParsed raw) (request raw)
    (by funext i;fin_cases i <;> rfl)

lemma front_executes (g : BitString → ℕ) (raw : BitString) :
    ∃c, front.Executes g (frontInput raw) (frontOutput raw) c ∧ c≤40*raw.length+100 := by
  let s₁ := Function.update (frontMeasured raw) (1:Fin 9) []
  let s₂ := Function.update s₁ (4:Fin 9) []
  have h₁ := clear_executes g (1:Fin 9) (frontMeasured raw)
  have h₂ := clear_executes g (4:Fin 9) s₁
  have h₃ := clear_executes g (8:Fin 9) s₂
  have ho : Function.update s₂ (8:Fin 9) []=frontOutput raw := by
    funext i;fin_cases i <;> rfl
  rw [ho] at h₃
  refine ⟨_,seq_executes _ _ g (front_parse g raw) (seq_executes _ _ g (front_measure g raw)
    (seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃))),?_⟩
  have hb := twoParse_cost_bound raw
  have hl := parse_lengths raw
  have hq := parse_lengths (request raw)
  simp only [s₁,s₂,frontMeasured,frontParsed,frontPairPorts,twoParseResult,parse8Store,
    Function.update_apply,Fin.reduceEq,ite_true,ite_false,List.length_cons,List.length_nil]
  dsimp [size,request] at *
  omega
lemma front_queryFree : front.QueryFree := seq_queryFree _ _ (rename_queryFree _ _ twoParse_queryFree)
  (seq_queryFree _ _ (headerOn_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))

@[simp] lemma request_pair (req tape : BitString) : request (pairBits req tape)=req := by simp [request]
@[simp] lemma coins_pair (req tape : BitString) : coins (pairBits req tape)=tape := by simp [coins]
@[simp] lemma graph_estimate (x tape : BitString) (r k : ℕ) :
    graph (pairBits (estimateInput x r k) tape)=x := by simp [graph,estimateInput]
@[simp] lemma size_pair (req tape : BitString) : size (pairBits req tape)=req.length := by simp [size]
lemma canonical_precision_bounds (x tape : BitString) (r k : ℕ) :
    r≤size (pairBits (estimateInput x r k) tape) ∧
    k≤size (pairBits (estimateInput x r k) tape) ∧
    x.length≤size (pairBits (estimateInput x r k) tape) := by
  simp only [size_pair,estimateInput_length]
  omega
end HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetup
