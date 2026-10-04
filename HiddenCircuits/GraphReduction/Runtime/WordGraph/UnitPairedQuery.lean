import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliquePairedSize
import HiddenCircuits.GraphReduction.Runtime.UnitSuppliedQuery

/-! Actual paired-stream frontend followed by supplied-coordinate
serialization in a disjoint extension of the established paired register bank. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.UnitPairedQuery
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 1000000

def state (width height samples count : ℕ) (source target pairs descriptor out : BitString) : Store 114 := fun i=>
  if h:i.val<77 then PairedQuery.state width height samples count source target pairs descriptor out ⟨i.val,h⟩ else []
def frontMap : Fin 77 ↪ Fin 115 where
  toFun i:=⟨i.val,by omega⟩
  inj':=by intro i j h;exact Fin.ext (congrArg (fun q:Fin 115=>q.val) h)
def suppliedMap : Fin 97 ↪ Fin 115 where
  toFun i:=if h:i.val<57 then ⟨i.val,by omega⟩ else if i.val=57 then 65 else if i.val=58 then 67 else ⟨i.val+18,by omega⟩
  inj':=by decide +kernel
noncomputable def program : OracleBlock 114 := seq (rename (CliquePairedQuery.program false) frontMap)
  (seq (clear 7) (rename UnitSuppliedQuery.program suppliedMap))
noncomputable def time : Polynomial ℕ := CliquePairedQuery.time+
  UnitSuppliedQuery.timePolynomial.comp (400*(X+1)^3)+150*(X+1)^4+5

theorem program_executes {p : ℕ} (g : BitString → ℕ) (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    ∃c,program.Executes g (state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] [])
      (state (2*p) ps.length s (unitGraphInput (fun i=>ps.get i) S T s).1 (stateBits S) (stateBits T)
        (pairStream ps) (unitDescriptor (fun i=>ps.get i) S T s) (UnitSuppliedQuery.bits ps S T s)) c ∧
      c≤time.eval (p+ps.length+s) := by
  let G:=unitGraphInput (fun i=>ps.get i) S T s
  let D:=unitDescriptor (fun i=>ps.get i) S T s
  let start:=state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] []
  let middle:=state (2*p) ps.length s G.1 (stateBits S) (stateBits T) (pairStream ps) D []
  let emitted:=state (2*p) ps.length s G.1 (stateBits S) (stateBits T) (pairStream ps) D G.encode
  let finish:=state (2*p) ps.length s G.1 (stateBits S) (stateBits T) (pairStream ps) D (UnitSuppliedQuery.bits ps S T s)
  obtain ⟨a,ha,hba⟩:=CliquePairedQuery.program_polynomial g false ps S T s
  have h1 : (rename (CliquePairedQuery.program false) frontMap).Executes g start emitted a := by
    apply rename_executes_to _ frontMap g ha
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · clear ha hba;intro i hi
      have hn:¬i.val<77:=by intro h;exact hi ⟨i.val,h⟩ (Fin.ext rfl)
      simp [start,emitted,state,hn]
  have h2 : (clear (7:Fin 115)).Executes g emitted middle (G.encode.length+1) := by
    convert clear_executes g (7:Fin 115) emitted using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨b,hb,hbb⟩:=UnitSuppliedQuery.program_executes ps S T s g
  have h3 : (rename UnitSuppliedQuery.program suppliedMap).Executes g middle finish b := by
    apply rename_executes_to _ suppliedMap g hb
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · clear ha hb h1 h2 hba hbb
      intro i hi
      have h7:i.val≠7:=by intro h;exact hi 7 (Fin.ext h.symm)
      by_cases hn:i.val<77
      · simp only [middle,finish,state,hn,↓reduceDIte,PairedQuery.state,h7,if_false]
      · simp [middle,finish,state,hn]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  let M:=p+ps.length+s
  have hp:p≤M:=by dsimp [M];omega
  have hh:ps.length≤M:=by dsimp [M];omega
  have hs:s≤M:=by dsimp [M];omega
  obtain ⟨hn,hd,hw⟩:=CliquePairedQuery.data_size_bounds false ps S T s M hp hh hs
  change G.1≤10*(M+1)^2 at hn
  change D.length≤380*(M+1)^3 at hd
  have hpow:(M+1)^2≤(M+1)^3:=by nlinarith [Nat.mul_le_mul_left ((M+1)*(M+1)) (show 1≤M+1 by omega)]
  have hinput:G.1+D.length+2*p+ps.length≤400*(M+1)^3:=by nlinarith
  have hbytes:G.encode.length≤150*(M+1)^4 := by
    rw [GraphInput.encode_length]
    calc
      _≤2*(10*(M+1)^2)+(10*(M+1)^2)*(10*(M+1)^2)+1 := by gcongr
      _≤150*(M+1)^4 := by ring_nf;omega
  have hm:=polynomial_nat_eval_mono UnitSuppliedQuery.timePolynomial hinput
  dsimp only at hm
  change a≤CliquePairedQuery.time.eval M at hba
  change b≤UnitSuppliedQuery.timePolynomial.eval (G.1+D.length+2*p+ps.length) at hbb
  change _≤time.eval M
  simp only [time,eval_add,eval_comp,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
  omega
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (rename_queryFree _ _ (CliquePairedQuery.program_queryFree false))
  (seq_queryFree _ _ (clear_queryFree _) (rename_queryFree _ _ UnitSuppliedQuery.program_queryFree))
end HiddenCircuits.GraphReduction.Runtime.WordGraph.UnitPairedQuery
