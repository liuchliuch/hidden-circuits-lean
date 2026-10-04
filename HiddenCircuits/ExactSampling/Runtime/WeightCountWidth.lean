import HiddenCircuits.ExactSampling.Runtime.WeightCore
import HiddenCircuits.Complexity.BinaryArithmetic.SubtractionMachine

/-! Literal binary-count and rejection-width preparation. The total DH counter
runs on raw bytes; width is obtained by physical subtraction and bit counting,
not by a unit-cost arithmetic instruction. -/
namespace HiddenCircuits.ExactSampling.Runtime.CountWidth
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 1800000

abbrev unary (n : ℕ) : BitString := List.replicate n true

def count (raw : BitString) : ℕ := Computability.decodeNat (DH.BinaryRuntime.function raw)
def width (raw : BitString) : ℕ := Nat.size (count raw-1)

def state (raw total flag width temporary unit : BitString) : Store 60 := fun r =>
  if r.val=0 then raw else if r.val=4 then total else if r.val=5 then flag
  else if r.val=6 then width else if r.val=7 then temporary else if r.val=8 then unit else []
def input (raw : BitString) : Store 60 := state raw [] [] [] [] []
def output (raw : BitString) : Store 60 := state raw (DH.BinaryRuntime.function raw) [] (unary (width raw)) [] []

def counterPorts : Fin 54 ↪ Fin 61 where
  toFun i := if i.val=0 then 7 else ⟨i.val+7,by omega⟩
  inj' := by decide +kernel

def subPorts : Fin 4 ↪ Fin 61 := ⟨fun i => ![7,8,9,5] i,by decide +kernel⟩
noncomputable def copyGraph : OracleBlock 60 := copyOn 0 7 9 (by decide) (by decide) (by decide)
noncomputable def counter : OracleBlock 60 := rename DH.BinaryRuntime.program counterPorts
noncomputable def moveCount : OracleBlock 60 := moveOn 7 4 9 (by decide) (by decide) (by decide)
noncomputable def computeCount : OracleBlock 60 := seq copyGraph (seq counter moveCount)
noncomputable def copyCount : OracleBlock 60 := copyOn 4 7 9 (by decide) (by decide) (by decide)
noncomputable def subtractOne : OracleBlock 60 := rename subBlock subPorts
noncomputable def lengthLoop : OracleBlock 60 := whilePop 7 (push 6 true) (push 6 true)
noncomputable def deriveWidth : OracleBlock 60 := seq copyCount
  (seq (push 8 true) (seq subtractOne (seq (clear 5) lengthLoop)))
noncomputable def program : OracleBlock 60 := seq computeCount deriveWidth

lemma count_canonical (raw : BitString) : DH.BinaryRuntime.function raw=Computability.encodeNat (count raw) := by
  simp [count,DH.BinaryRuntime.function,DH.Runtime.BinaryModel.function,Computability.decode_encodeNat]

lemma computeCount_executes (g : BitString→ℕ) (raw : BitString) :
    ∃t,computeCount.Executes g (input raw) (state raw (DH.BinaryRuntime.function raw) [] [] [] []) t ∧
      t≤11*raw.length+7*DH.BinaryRuntime.time.eval raw.length+11 := by
  have hc : copyGraph.Executes g (input raw) (state raw [] [] [] raw []) (5*raw.length+2) := by
    convert copyOn_executes g (0:Fin 61) 7 9 (by decide) (by decide) (by decide) (input raw) rfl using 1
    funext i;fin_cases i <;> simp [input,state]
  obtain ⟨a,ha,hab⟩ := DH.BinaryRuntime.executes g raw
  have hcounter : counter.Executes g (state raw [] [] [] raw [])
      (state raw [] [] [] (DH.BinaryRuntime.function raw) []) a := by
    apply rename_executes_to DH.BinaryRuntime.program counterPorts g ha
    · funext i;fin_cases i <;> simp [state,counterPorts]
    · funext i;fin_cases i <;> simp [state,counterPorts]
    · intro i hi
      have h7 : i.val≠7 := by intro h;apply hi 0;apply Fin.ext;exact h.symm
      simp [state,h7]
  have hm : moveCount.Executes g (state raw [] [] [] (DH.BinaryRuntime.function raw) [])
      (state raw (DH.BinaryRuntime.function raw) [] [] [] []) (6*(DH.BinaryRuntime.function raw).length+5) := by
    convert moveOn_executes g (7:Fin 61) 4 9 (by decide) (by decide) (by decide)
      (state raw [] [] [] (DH.BinaryRuntime.function raw) []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hcounter hm),?_⟩
  have hl := WeightCompiler.function_length raw
  omega

lemma lengthLoop_executes (g : BitString→ℕ) (raw total xs acc : BitString) :
    lengthLoop.Executes g (state raw total [] acc xs [])
      (state raw total [] (unary xs.length++acc) [] []) (3*xs.length+1) := by
  apply whilePop_executes
  induction xs generalizing acc with
  | nil => simpa using (WhileExecution.empty
      (stack:=(7:Fin 61)) (B:=push 6 true) (C:=push 6 true) (g:=g) (state raw total [] acc [] []) rfl)
  | cons b xs ih =>
    have he : Function.update (state raw total [] acc (b::xs) []) 7 xs=state raw total [] acc xs [] := by
      funext i;fin_cases i <;> simp [state]
    have hp : (push (6:Fin 61) true).Executes g (state raw total [] acc xs [])
        (state raw total [] (true::acc) xs []) 1 := by
      convert push_executes g (6:Fin 61) true (state raw total [] acc xs []) using 1
      funext i;fin_cases i <;> simp [state]
    have ht := ih (true::acc)
    have hu : unary xs.length++true::acc=unary (xs.length+1)++acc := by
      change List.replicate xs.length true++true::acc=List.replicate (xs.length+1) true++acc
      rw [List.replicate_succ',List.append_assoc];rfl
    cases b
    · have hh := WhileExecution.zero (stack:=(7:Fin 61)) (s:=state raw total [] acc (false::xs) []) rfl (by rw [he];exact hp) ht
      convert hh using 1 <;> simp [hu] <;> omega
    · have hh := WhileExecution.one (stack:=(7:Fin 61)) (s:=state raw total [] acc (true::xs) []) rfl (by rw [he];exact hp) ht
      convert hh using 1 <;> simp [hu] <;> omega

lemma deriveWidth_executes (g : BitString→ℕ) (raw : BitString) (n : ℕ) :
    ∃t,deriveWidth.Executes g (state raw (Computability.encodeNat n) [] [] [] [])
      (state raw (Computability.encodeNat n) [] (unary (Nat.size (n-1))) [] []) t ∧
      t≤20*(Computability.encodeNat n).length+30 := by
  let w := Computability.encodeNat n
  let pred := Computability.encodeNat (n-1)
  have hc : copyCount.Executes g (state raw w [] [] [] []) (state raw w [] [] w []) (5*w.length+2) := by
    convert copyOn_executes g (4:Fin 61) 7 9 (by decide) (by decide) (by decide)
      (state raw w [] [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  have hp : (push (8:Fin 61) true).Executes g (state raw w [] [] w []) (state raw w [] [] w [true]) 1 := by
    convert push_executes g (8:Fin 61) true (state raw w [] [] w []) using 1
    funext i;fin_cases i <;> simp [state]
  have hs : subtractOne.Executes g (state raw w [] [] w [true])
      (state raw w [decide (n<1)] [] pred []) (subCost w (Computability.encodeNat 1)) := by
    apply rename_executes_to subBlock subPorts g (subBlock_encode g n 1)
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have h5 : i.val≠5 := by intro h;apply hi 3;apply Fin.ext;exact h.symm
      have h7 : i.val≠7 := by intro h;apply hi 0;apply Fin.ext;exact h.symm
      have h8 : i.val≠8 := by intro h;apply hi 1;apply Fin.ext;exact h.symm
      simp [state,h5,h7,h8]
  have hf : (clear (5:Fin 61)).Executes g (state raw w [decide (n<1)] [] pred [])
      (state raw w [] [] pred []) 2 := by
    convert clear_executes g (5:Fin 61) (state raw w [decide (n<1)] [] pred []) using 1
    funext i;fin_cases i <;> simp [state]
  have hl := lengthLoop_executes g raw w pred []
  simp only [List.append_nil,show pred.length=Nat.size (n-1) from encodeNat_length _] at hl
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hp (seq_executes _ _ g hs (seq_executes _ _ g hf hl))),?_⟩
  have hb := subCost_bound w (Computability.encodeNat 1)
  have he : (Computability.encodeNat 1).length=1 := rfl
  rw [he] at hb
  have hw : Nat.size (n-1)≤w.length := by
    rw [show w.length=Nat.size n from encodeNat_length _]
    exact Nat.size_le_size (by omega)
  have hmax : max w.length 1≤w.length+1 := max_le (by omega) (by omega)
  change 5*w.length+2+(1+(subCost w (Computability.encodeNat 1)+(2+(3*Nat.size (n-1)+1)+2)+2)+2)+2≤20*w.length+30
  omega

open Polynomial
noncomputable def timePolynomial : Polynomial ℕ := 100*(X+DH.BinaryRuntime.time+1)

/-- Total all-raw execution. There is no supplied graph parser result,
hereditary proof, count, width, or runtime certificate in this premise. -/
theorem program_executes (g : BitString→ℕ) (raw : BitString) :
    ∃t,program.Executes g (input raw) (output raw) t ∧t≤timePolynomial.eval raw.length := by
  obtain ⟨a,ha,hab⟩ := computeCount_executes g raw
  obtain ⟨b,hb,hbb⟩ := deriveWidth_executes g raw (count raw)
  rw [←count_canonical] at hb hbb
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  have hl := WeightCompiler.function_length raw
  simp only [timePolynomial,eval_mul,eval_add,eval_ofNat,eval_X,eval_one]
  omega

lemma queryFree : program.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ DH.BinaryRuntime.queryFree) (moveOn_queryFree _ _ _ _ _ _)))
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (push_queryFree _ _)
      (seq_queryFree _ _ (rename_queryFree _ _ subBlock_queryFree)
        (seq_queryFree _ _ (clear_queryFree _) (whilePop_queryFree _ _ _ (push_queryFree _ _) (push_queryFree _ _))))))

lemma input_eq (raw : BitString) : input raw=Function.update (fun _=>[]) 0 raw := by
  funext i;fin_cases i <;> simp [input,state]
lemma output_graph (raw : BitString) : output raw 0=raw := rfl
lemma output_count (raw : BitString) : output raw 4=DH.BinaryRuntime.function raw := rfl
lemma output_width (raw : BitString) : output raw 6=unary (Nat.size (count raw-1)) := rfl
lemma output_scratch (raw : BitString) (i : Fin 61) (h0:i≠0) (h4:i≠4) (h6:i≠6) : output raw i=[] := by
  have h0' : i.val≠0 := by intro h;apply h0;exact Fin.ext h
  have h4' : i.val≠4 := by intro h;apply h4;exact Fin.ext h
  have h6' : i.val≠6 := by intro h;apply h6;exact Fin.ext h
  simp [output,state,h0',h4',h6']

noncomputable def programOn {k : ℕ} (φ : Fin 61 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem programOn_executes {k : ℕ} (φ : Fin 61 ↪ Fin (k+1)) (g : BitString→ℕ)
    (s : Store k) (raw : BitString) (hs:s∘φ=input raw) :
    ∃t,(programOn φ).Executes g s
      (Function.update (Function.update s (φ 4) (DH.BinaryRuntime.function raw)) (φ 6) (unary (width raw))) t ∧
      t≤timePolynomial.eval raw.length := by
  obtain ⟨t,ht,hb⟩ := program_executes g raw
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · funext i
    simp only [Function.comp_apply,Function.update_apply,φ.injective.eq_iff]
    have hh := congrFun hs i
    simp only [Function.comp_apply] at hh
    rw [hh]
    fin_cases i <;> rfl
  · intro i hi
    rw [Function.update_of_ne (hi 6).symm,Function.update_of_ne (hi 4).symm]

lemma programOn_queryFree {k : ℕ} (φ : Fin 61 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ queryFree

end HiddenCircuits.ExactSampling.Runtime.CountWidth
