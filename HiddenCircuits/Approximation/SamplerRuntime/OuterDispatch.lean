import HiddenCircuits.Approximation.SamplerRuntime.OuterPrepare
import HiddenCircuits.GraphReduction.MonotoneEndpointDecode
import HiddenCircuits.Complexity.PolynomialBounds

/-! Charged finite-program composition with a canonical endpoint parser. The
parser interface is discharged by the concrete `EndpointParser` program. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Outer
open Complexity Complexity.OracleBlock GraphReduction.MonotoneEndpointEncoding Polynomial

structure ParserShape (raw : BitString) (s : Store 35) : Prop where
  source : s 0=raw
  valid : s 4=[(decode raw).isSome]
  decoded : ∀E,decode raw=some E → s 1=unary E.1 ∧
    s 2=encodeBitList (rows E.2.lo) ∧ s 3=encodeBitList (rows E.2.hi)
  empty : ∀i : Fin 36,5 ≤ i.val → s i=[]

structure ParserSpec (B : OracleBlock 35) (p : Polynomial ℕ) : Prop where
  queryFree : B.QueryFree
  executes : ∀(g : BitString → ℕ) raw,∃s : Store 35,∃c,
    B.Executes g (Function.update (fun _ : Fin 36 => ([]:BitString)) 0 raw) s c ∧
    ParserShape raw s ∧ c≤p.eval raw.length

def parserPorts : Fin 36 ↪ Fin 45 where
  toFun i := ⟨if i.val=0 then 4 else i.val+9,by split_ifs <;> omega⟩
  inj' := by intro i j h;apply Fin.ext;have hh := congrArg Fin.val h;dsimp at hh;split_ifs at hh <;> omega

def corePorts : Fin 27 ↪ Fin 45 where
  toFun := ![11,12,7,10,14,0,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,6,34]
  inj' := by decide +kernel

noncomputable def parser (B : OracleBlock 35) : OracleBlock 44 := rename B parserPorts
noncomputable def core : OracleBlock 44 := rename Core.program corePorts
noncomputable def choose (B : OracleBlock 35) : OracleBlock 44 := seq (parser B) (branchPop 13 skip skip core)
noncomputable def dispatch (B : OracleBlock 35) : OracleBlock 44 := branchPop 8 skip skip (choose B)
noncomputable def work (B : OracleBlock 35) : OracleBlock 44 := seq prepare (dispatch B)

def beforeParser (raw : BitString) : Store 44 := store (tape raw) [] [] [] (graph raw) [] (unary (inputSize raw)) [] [] []

def postParser (raw : BitString) (s : Store 35) : Store 44 := fun i =>
  if i.val=4 then s 0 else if h : 10 ≤ i.val then s ⟨i.val-9,by omega⟩ else beforeParser raw i

def afterValid (raw : BitString) (s : Store 35) : Store 44 := Function.update (postParser raw s) 13 []

lemma pop_prepared (raw : BitString) : Function.update (prepared raw) 8 []=beforeParser raw := by
  funext i;fin_cases i <;> rfl

lemma parser_executes (B : OracleBlock 35) (p : Polynomial ℕ) (hB : ParserSpec B p)
    (g : BitString → ℕ) (raw : BitString) :
    ∃s : Store 35,∃c,(parser B).Executes g (beforeParser raw) (postParser raw s) c ∧
      ParserShape (graph raw) s ∧ c≤p.eval (graph raw).length := by
  obtain ⟨s,c,hc,hs,hb⟩ := hB.executes g (graph raw)
  refine ⟨s,c,?_,hs,hb⟩
  apply rename_executes_to B parserPorts g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h4 : i.val≠4 := by intro h;apply hi 0;apply Fin.ext;exact h.symm
    have h10 : ¬10 ≤ i.val := by
      intro h
      let j : Fin 36 := ⟨i.val-9,by omega⟩
      apply hi j
      apply Fin.ext
      simp [parserPorts,j,show i.val-9≠0 by omega]
      omega
    simp [postParser,h4,h10]

lemma core_entry (raw : BitString) (s : Store 35) (hs : ParserShape (graph raw) s)
    (E : Input) (he : decode (graph raw)=some E) :
    afterValid raw s∘corePorts=Core.state (encodeBitList (rows E.2.lo)) (encodeBitList (rows E.2.hi))
      E.1 (inputSize raw) (tape raw) [] [] [] [] := by
  obtain ⟨h1,h2,h3⟩ := hs.decoded E he
  funext i
  fin_cases i <;> simp [afterValid,postParser,beforeParser,store,corePorts,Core.state,h1,h2,h3,hs.empty]

lemma core_executes (g : BitString → ℕ) (raw : BitString) (s : Store 35)
    (hs : ParserShape (graph raw) s) (E : Input) (he : decode (graph raw)=some E) :
    ∃t : Store 44,∃c,core.Executes g (afterValid raw s) t c ∧
      t 7=Core.evaluate E.2 (inputSize raw) (tape raw) ∧ t 2=[] ∧ c≤Core.timePolynomial.eval (inputSize raw) := by
  have hn : E.1 ≤ inputSize raw := (size_le_of_decode he).trans (graph_length raw)
  obtain ⟨inner,c,hc,ho,hb⟩ := Core.program_executes g E.2 (inputSize raw) hn (tape raw)
  have hh := rename_executes Core.program corePorts g (afterValid raw s)
    (by rw [core_entry raw s hs E he];exact hc)
  refine ⟨_,c,hh,?_,?_,hb⟩
  · have h := install_image corePorts (afterValid raw s) inner 2
    exact h.trans ho
  · rw [install_off]
    · rfl
    · intro i;fin_cases i <;> decide

def chosenValue (raw : BitString) : BitString :=
  match decode (graph raw) with
  | none => []
  | some E => Core.evaluate E.2 (inputSize raw) (tape raw)

lemma choose_executes (B : OracleBlock 35) (p : Polynomial ℕ) (hB : ParserSpec B p)
    (g : BitString → ℕ) (raw : BitString) :
    ∃t : Store 44,∃c,(choose B).Executes g (beforeParser raw) t c ∧
      t 7=chosenValue raw ∧ t 2=[] ∧ c≤p.eval (graph raw).length+Core.timePolynomial.eval (inputSize raw)+5 := by
  obtain ⟨s,a,ha,hs,hba⟩ := parser_executes B p hB g raw
  cases he : decode (graph raw) with
  | none =>
    have hv : postParser raw s (13:Fin 45)=[false] := by simpa [postParser,he] using hs.valid
    have hb := branchPop_false (13:Fin 45) skip skip core g hv
      (skip_executes g (afterValid raw s))
    refine ⟨afterValid raw s,a+3+2,seq_executes _ _ g ha hb,?_,rfl,by omega⟩
    simp [afterValid,postParser,beforeParser,store,chosenValue,he]
  | some E =>
    have hv : postParser raw s (13:Fin 45)=[true] := by simpa [postParser,he] using hs.valid
    obtain ⟨t,b,hb,ho,hzero,hbb⟩ := core_executes g raw s hs E he
    have hh := branchPop_true (13:Fin 45) skip skip core g hv hb
    refine ⟨t,a+(b+2)+2,seq_executes _ _ g ha hh,?_,hzero,by omega⟩
    simpa only [chosenValue,he] using ho

lemma dispatch_executes (B : OracleBlock 35) (p : Polynomial ℕ) (hB : ParserSpec B p)
    (g : BitString → ℕ) (raw : BitString) :
    ∃t : Store 44,∃c,(dispatch B).Executes g (prepared raw) t c ∧
      t 7=Functional.evaluate raw ∧ t 2=[] ∧
      c≤p.eval (graph raw).length+Core.timePolynomial.eval (inputSize raw)+7 := by
  cases hv : preValid raw with
  | false =>
    have hs : prepared raw (8:Fin 45)=[false] := by simp [prepared,store,hv]
    have hh := branchPop_false (8:Fin 45) skip skip (choose B) g hs
      (by rw [pop_prepared];exact skip_executes g (beforeParser raw))
    refine ⟨beforeParser raw,3,hh,?_,rfl,by omega⟩
    rw [evaluate_eq,hv]
    rfl
  | true =>
    obtain ⟨t,c,hc,ho,hzero,hb⟩ := choose_executes B p hB g raw
    have hs : prepared raw (8:Fin 45)=[true] := by simp [prepared,store,hv]
    have hh := branchPop_true (8:Fin 45) skip skip (choose B) g hs (by rw [pop_prepared];exact hc)
    
    refine ⟨t,c+2,hh,?_,hzero,by omega⟩
    rw [evaluate_eq,hv]
    exact ho

/-- Polynomial bound for the actual outer preparation and dispatch. -/
noncomputable def workTime (p : Polynomial ℕ) : Polynomial ℕ :=
  50*(X+1)^2+p+Core.timePolynomial+10

theorem work_executes (B : OracleBlock 35) (p : Polynomial ℕ) (hB : ParserSpec B p)
    (g : BitString → ℕ) (raw : BitString) :
    ∃s : Store 44,∃c,(work B).Executes g
      (Function.update (fun _ : Fin 45 => ([]:BitString)) 0 raw) s c ∧
      s 7=Functional.evaluate raw ∧ s 2=[] ∧ c≤(workTime p).eval raw.length := by
  obtain ⟨a,ha,hab⟩ := prepare_executes g raw
  obtain ⟨s,b,hb,ho,hzero,hbb⟩ := dispatch_executes B p hB g raw
  refine ⟨s,_,seq_executes _ _ g ha hb,ho,hzero,?_⟩
  have hp := polynomial_nat_eval_mono p ((graph_length raw).trans (inputSize_le raw))
  have hc := polynomial_nat_eval_mono Core.timePolynomial (inputSize_le raw)
  dsimp only at hp hc
  simp only [workTime,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
  omega

lemma work_queryFree (B : OracleBlock 35) (p : Polynomial ℕ) (hB : ParserSpec B p) :
    (work B).QueryFree := seq_queryFree _ _ prepare_queryFree
  (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree
    (seq_queryFree _ _ (rename_queryFree _ _ hB.queryFree)
      (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree
        (rename_queryFree _ _ Core.program_queryFree))))
end HiddenCircuits.Approximation.SamplerRuntime.Outer
