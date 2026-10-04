import HiddenCircuits.Complexity.FPSharpPCount
import HiddenCircuits.Complexity.GraphVerifier.TwoParse
import HiddenCircuits.Complexity.OracleResult

/-! Fixed five-stack oracle verifier: parse the actual certificate pair, query
f on its input, binary-subtract witness−f(input), and test final borrow plus
parse validity. No running-time verifier is supplied. -/
namespace HiddenCircuits.Complexity.FPSharpP
open OracleBlock BinaryArithmetic GraphVerifier GraphVerifier.Runtime Polynomial

def store (a b c d e : BitString) : Store 4:=fun i=>
  if i.val=0 then a else if i.val=1 then b else if i.val=2 then c else if i.val=3 then d else e
def initial (xs : BitString) : Store 4:=Function.update (fun _=>[]) 0 xs
def parseMap : Fin 4 ↪ Fin 5:=⟨fun i=>![0,1,2,4] i,by decide +kernel⟩
def subMap : Fin 4 ↪ Fin 5:=⟨fun i=>⟨i.val,by omega⟩,by intro i j h;exact Fin.ext (congrArg (fun z : Fin 5=>z.val) h)⟩
noncomputable def parseProgram : OracleBlock 4:=unpairOn parseMap
noncomputable def subtract : OracleBlock 4:=rename subBlock subMap
noncomputable def reject : OracleBlock 4:=seq (clear 3) (push 4 false)
noncomputable def andProgram : OracleBlock 4:=branchPop 4 reject reject
  (branchPop 3 (push 4 false) (push 4 false) (push 4 true))
noncomputable def core : OracleBlock 4:=seq parseProgram (seq (query 1 1) (seq subtract andProgram))
noncomputable def program : OracleBlock 4:=seq core (cleanResult 4 2 (by decide) (by decide))
noncomputable def coreTime (p : Polynomial ℕ) : Polynomial ℕ:=10*X+6*p+30
noncomputable def time (p : Polynomial ℕ) : Polynomial ℕ:=coreTime p+9*(X+coreTime p+3)+3

lemma parse_executes (f : BitString→ℕ) (xs : BitString) :
    parseProgram.Executes f (initial xs)
      (store (parse xs).right (parse xs).left [] [] [(parse xs).ok]) (parseCost xs+2*(parse xs).left.length+1) := by
  apply unpairOn_executes parseMap f _ _ xs
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i
    · exact (hi 0 rfl).elim
    · exact (hi 1 rfl).elim
    · exact (hi 2 rfl).elim
    · rfl
    · exact (hi 3 rfl).elim
lemma subtract_executes (f : BitString→ℕ) (xs ys : BitString) (ok : Bool) :
    subtract.Executes f (store xs ys [] [] [ok])
      (store (subtractBits xs ys) [] [] [(subRaw xs ys false).2] [ok]) (subCost xs ys) := by
  apply rename_executes_to _ subMap f (subBlock_executes f xs ys)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i
    · exact (hi 0 rfl).elim
    · exact (hi 1 rfl).elim
    · exact (hi 2 rfl).elim
    · exact (hi 3 rfl).elim
    · rfl
lemma reject_executes (f : BitString→ℕ) (xs : BitString) (b : Bool) :
    reject.Executes f (store xs [] [] [b] []) (store xs [] [] [] [false]) 5 := by
  have hc:(clear (3:Fin 5)).Executes f (store xs [] [] [b] []) (store xs [] [] [] []) 2 := by
    convert clear_executes f (3:Fin 5) (store xs [] [] [b] []) using 1
    funext i;fin_cases i <;> rfl
  have hp:(push (4:Fin 5) false).Executes f (store xs [] [] [] []) (store xs [] [] [] [false]) 1 := by
    convert push_executes f (4:Fin 5) false (store xs [] [] [] []) using 1
    funext i;fin_cases i <;> rfl
  exact seq_executes _ _ f hc hp
lemma and_executes (f : BitString→ℕ) (xs : BitString) (ok b : Bool) :
    ∃c,andProgram.Executes f (store xs [] [] [b] [ok]) (store xs [] [] [] [ok&&b]) c ∧ c ≤ 7 := by
  cases ok with
  | false=>
    refine ⟨7,branchPop_false 4 _ _ _ f rfl ?_,by decide⟩
    convert reject_executes f xs b using 1
    funext i;fin_cases i <;> rfl
  | true=>
    have hp (q : Bool) : (push (4:Fin 5) q).Executes f (store xs [] [] [] []) (store xs [] [] [] [q]) 1 := by
      convert push_executes f (4:Fin 5) q (store xs [] [] [] []) using 1
      funext i;fin_cases i <;> rfl
    refine ⟨5,branchPop_true 4 _ _ _ f rfl ?_,by decide⟩
    cases b
    · apply branchPop_false 3 _ _ _ f rfl
      convert hp false using 1 <;> funext i <;> fin_cases i <;> rfl
    · apply branchPop_true 3 _ _ _ f rfl
      convert hp true using 1 <;> funext i <;> fin_cases i <;> rfl
lemma borrow_eq (xs ys : BitString) : (subRaw xs ys false).2=decide (value xs<value ys) := by
  apply Bool.eq_iff_iff.mpr
  simp only [subRaw_borrow,decide_eq_true_eq]

theorem core_executes (f : BitString→ℕ) (p : Polynomial ℕ)
    (hp : ∀x,(Computability.encodeNat (f x)).length ≤ p.eval x.length) (xs : BitString) :
    ∃c,core.Executes f (initial xs)
      (store (subtractBits (parse xs).right (Computability.encodeNat (f (parse xs).left))) [] [] [] [verifier f xs]) c ∧
      c ≤ (coreTime p).eval xs.length := by
  have hparse:=parse_executes f xs
  have hquery:(query (1:Fin 5) 1).Executes f (store (parse xs).right (parse xs).left [] [] [(parse xs).ok])
      (store (parse xs).right (Computability.encodeNat (f (parse xs).left)) [] [] [(parse xs).ok])
      (1+(parse xs).left.length+(Computability.encodeNat (f (parse xs).left)).length) := by
    convert query_executes f (1:Fin 5) 1 (store (parse xs).right (parse xs).left [] [] [(parse xs).ok]) using 1
    funext i;fin_cases i <;> rfl
  have hsub:=subtract_executes f (parse xs).right (Computability.encodeNat (f (parse xs).left)) (parse xs).ok
  obtain ⟨a,ha,hab⟩:=and_executes f (subtractBits (parse xs).right (Computability.encodeNat (f (parse xs).left)))
    (parse xs).ok (subRaw (parse xs).right (Computability.encodeNat (f (parse xs).left)) false).2
  rw [borrow_eq,value_encodeNat,←verifier_parse] at ha
  rw [borrow_eq,value_encodeNat] at hsub
  refine ⟨_,seq_executes _ _ f hparse (seq_executes _ _ f hquery (seq_executes _ _ f hsub ha)),?_⟩
  have hparseb:=unpair_cost_bound xs
  obtain ⟨hl,hr⟩:=parse_lengths xs
  have hlen:=(hp (parse xs).left).trans (polynomial_nat_eval_mono p hl)
  dsimp only at hlen
  have hsubb:=subCost_bound (parse xs).right (Computability.encodeNat (f (parse xs).left))
  have hmax:max (parse xs).right.length (Computability.encodeNat (f (parse xs).left)).length ≤ xs.length+p.eval xs.length:=by omega
  have hsubBound : subCost (parse xs).right (Computability.encodeNat (f (parse xs).left)) ≤ 5*(xs.length+p.eval xs.length)+4 := hsubb.trans (by omega)
  simp only [coreTime,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

theorem program_executes (f : BitString→ℕ) (p : Polynomial ℕ)
    (hp : ∀x,(Computability.encodeNat (f x)).length ≤ p.eval x.length) (xs : BitString) :
    ∃c,program.Executes f (initial xs) (initial (Computability.encodeBool (verifier f xs))) c ∧
      c ≤ (time p).eval xs.length := by
  obtain ⟨a,ha,hab⟩:=core_executes f p hp xs
  have hi:∀i,(initial xs i).length ≤ xs.length:=by intro i;simp [initial,Function.update_apply];split_ifs <;> simp
  obtain ⟨b,hb,hbb⟩:=cleanResult_executes f (4:Fin 5) 2 (by decide) (by decide) (by decide)
    _ (xs.length+a) (ha.stack_bound hi)
  refine ⟨a+b+2,seq_executes _ _ f ha hb,?_⟩
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat]
  omega
end HiddenCircuits.Complexity.FPSharpP
