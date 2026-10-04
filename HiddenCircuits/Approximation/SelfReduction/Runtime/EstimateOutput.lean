import HiddenCircuits.Approximation.SelfReduction.Runtime.EstimateOutputSerialize

/-! A fixed finite clean estimator-output compiler. Its public ports contain
unary M, unary original depth, an encoded unary count list and an alive bit.
The zero arm ignores partial observations; the successful arm computes every
binary digit using unary conversion, multiplication, exponentiation and subtraction. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.EstimateOutput
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic Polynomial

def state (base depth stream alive : BitString) : Store 20 := fun i =>
  if i.val=0 then base else if i.val=1 then depth else if i.val=2 then stream else if i.val=3 then alive else []
def inputStore (M d : ℕ) (xs : List ℕ) (alive : BitString) : Store 20 :=
  state (List.replicate M true) (List.replicate d true) (encodeBitList (unaryWords xs)) alive

def denominatorPorts : Fin 7 ↪ Fin 21 where
  toFun i := ![2,4,5,6,7,8,9] i
  inj' := by decide +kernel

def numeratorPorts : Fin 17 ↪ Fin 21 where
  toFun i := ⟨if i.val<2 then i.val else i.val+2,by split_ifs <;> omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; split_ifs at this <;> omega

def serializePorts : Fin 5 ↪ Fin 21 where
  toFun i := ![0,2,4,5,6] i
  inj' := by decide +kernel

noncomputable def arithmetic : OracleBlock 20 := seq (rename denominator denominatorPorts)
  (rename numerator numeratorPorts)
noncomputable def success : OracleBlock 20 := seq arithmetic (rename serialize serializePorts)
noncomputable def zero : OracleBlock 20 := seq (clearList (List.finRange 21)) (push 0 false)
noncomputable def program : OracleBlock 20 := branchPop 3 zero zero success

noncomputable def successTime : Polynomial ℕ := denominatorTime+numeratorTime+
  serializeTime.comp (2*(X+denominatorTime+numeratorTime+2))+4
noncomputable def zeroTime : Polynomial ℕ := 21*(X+3)+4
noncomputable def time : Polynomial ℕ := successTime+zeroTime+2

def inputSize (M d : ℕ) (xs : List ℕ) : ℕ := M+d+(encodeBitList (unaryWords xs)).length

 theorem state_bound (a b c e : BitString) : ∀ i, (state a b c e i).length ≤ a.length+b.length+c.length+e.length := by
  intro i; unfold state; split_ifs <;> (try simp only [List.length_nil]) <;> omega

 theorem success_executes (g : BitString → ℕ) (M d : ℕ) (xs : List ℕ)
    (hp : 0<xs.prod) :
    ∃ t, success.Executes g (inputStore M d xs []) (clean (encodeRatio (M^d) xs.prod)) t ∧
      t ≤ successTime.eval (inputSize M d xs) := by
  let stream := encodeBitList (unaryWords xs)
  let N := inputSize M d xs
  let s0 := inputStore M d xs []
  let s1 := state (List.replicate M true) (List.replicate d true) (signedBits (xs.prod:ℤ)) []
  let s2 := state (signedBits ((M^d:ℕ):ℤ)) [] (signedBits (xs.prod:ℤ)) []
  obtain ⟨a,ha,hab⟩ := denominator_executes g xs
  have h1 : (rename denominator denominatorPorts).Executes g s0 s1 a := by
    have h := rename_clean_executes denominator denominatorPorts g s0 stream (signedBits (xs.prod:ℤ)) a ha
      (by funext i; fin_cases i <;> rfl)
    convert h using 1
    funext i; fin_cases i <;> rfl
  obtain ⟨b,hb,hbb⟩ := numerator_executes g M d
  have h2 : (rename numerator numeratorPorts).Executes g s1 s2 b := by
    apply rename_executes_to numerator numeratorPorts g hb
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro i hi
      have hi0 : i.val≠0 := by intro h; exact hi 0 (Fin.ext h.symm)
      have hi1 : i.val≠1 := by intro h; exact hi 1 (Fin.ext h.symm)
      simp [s1,s2,state,hi0,hi1]
  have hArith : arithmetic.Executes g s0 s2 (a+b+2) := seq_executes _ _ g h1 h2
  obtain ⟨c,hc,hcb⟩ := serialize_executes g (M^d) xs.prod hp
  have h3 : (rename serialize serializePorts).Executes g s2 (clean (encodeRatio (M^d) xs.prod)) c := by
    apply rename_executes_to serialize serializePorts g hc
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro i hi
      have hi0 : i.val≠0 := by intro h; exact hi 0 (Fin.ext h.symm)
      have hi2 : i.val≠2 := by intro h; exact hi 1 (Fin.ext h.symm)
      simp [s2,state,clean,hi0,hi2,show i≠0 by simpa using hi0]
  refine ⟨a+b+2+c+2,seq_executes _ _ g hArith h3,?_⟩
  have ha' : a ≤ denominatorTime.eval N := hab.trans (polynomial_nat_eval_mono denominatorTime (by dsimp [N,inputSize]; omega))
  have hb' : b ≤ numeratorTime.eval N := hbb.trans (polynomial_nat_eval_mono numeratorTime (by dsimp [N,inputSize]; omega))
  have hs0 : ∀ i, (s0 i).length ≤ N := by
    simpa [stream,s0,inputStore,N,inputSize] using state_bound (List.replicate M true) (List.replicate d true) stream []
  have hn := hArith.stack_bound hs0 (0:Fin 21)
  have hd := hArith.stack_bound hs0 (2:Fin 21)
  have hl : (signedBits ((M^d:ℕ):ℤ)).length+(signedBits (xs.prod:ℤ)).length ≤ 
      2*(N+denominatorTime.eval N+numeratorTime.eval N+2) := by
    change (signedBits ((M^d:ℕ):ℤ)).length ≤ N+(a+b+2) at hn
    change (signedBits (xs.prod:ℤ)).length ≤ N+(a+b+2) at hd
    omega
  have hc' := hcb.trans (polynomial_nat_eval_mono serializeTime hl)
  dsimp only at hc'
  simp only [successTime,eval_add,eval_comp,eval_mul,eval_X,eval_ofNat]
  change a+b+2+c+2 ≤ denominatorTime.eval N+numeratorTime.eval N+
    serializeTime.eval (2*(N+denominatorTime.eval N+numeratorTime.eval N+2))+4
  omega

 theorem zero_executes (g : BitString → ℕ) (s : Store 20) (N : ℕ)
    (hs : ∀ i, (s i).length ≤ N) :
    ∃ t, zero.Executes g s (clean (encodeRatio 0 0)) t ∧ t ≤ zeroTime.eval N := by
  obtain ⟨a,ha,hab⟩ := clearList_executes g (List.finRange 21) s N hs
  have he : eraseStore (List.finRange 21) s=(fun _ => []) := by
    funext i; simp [eraseStore]
  rw [he] at ha
  have hb : (push (0:Fin 21) false).Executes g (fun _ => []) (clean (encodeRatio 0 0)) 1 := by
    simpa only [clean,encodeRatio,ite_true] using push_executes g (0:Fin 21) false (fun _ => [])
  refine ⟨a+1+2,seq_executes _ _ g ha hb,?_⟩
  simp only [List.length_finRange] at hab
  simp only [zeroTime,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

 theorem program_success (g : BitString → ℕ) (M d : ℕ) (xs : List ℕ)
    (hlen : xs.length=d) (hpos : ∀ c∈xs, 0<c) :
    ∃ t, program.Executes g (inputStore M d xs [true]) (clean (reciprocalProductOutput M xs)) t ∧
      t ≤ time.eval (inputSize M d xs+1) := by
  have hp : 0<xs.prod := List.prod_pos hpos
  obtain ⟨t,ht,hb⟩ := success_executes g M d xs hp
  have hupdate : Function.update (inputStore M d xs [true]) (3:Fin 21) []=inputStore M d xs [] := by
    funext i; fin_cases i <;> rfl
  have h := branchPop_true (3:Fin 21) zero zero success g (s:=inputStore M d xs [true]) rfl
    (by rw [hupdate]; exact ht)
  refine ⟨t+2,?_,?_⟩
  · simpa [reciprocalProductOutput,hlen] using h
  · have hm := polynomial_nat_eval_mono successTime (show inputSize M d xs ≤ inputSize M d xs+1 by omega)
    dsimp only at hm
    simp only [time,eval_add,eval_ofNat]
    omega

 theorem program_zero (g : BitString → ℕ) (M d : ℕ) (xs : List ℕ) :
    ∃ t, program.Executes g (inputStore M d xs []) (clean (encodeRatio 0 0)) t ∧
      t ≤ time.eval (inputSize M d xs+1) := by
  have hs : ∀ i, (inputStore M d xs [] i).length ≤ inputSize M d xs := by
    simpa [inputStore,inputSize] using state_bound (List.replicate M true) (List.replicate d true)
      (encodeBitList (unaryWords xs)) []
  obtain ⟨t,ht,hb⟩ := zero_executes g (inputStore M d xs []) (inputSize M d xs) hs
  refine ⟨t+2,branchPop_empty _ _ _ _ g rfl ht,?_⟩
  have hm := polynomial_nat_eval_mono zeroTime (show inputSize M d xs ≤ inputSize M d xs+1 by omega)
  dsimp only at hm
  simp only [time,eval_add,eval_ofNat]
  omega

 theorem program_zero_raw (g : BitString → ℕ) (M d : ℕ) (stream : BitString) :
    ∃ t, program.Executes g
      (state (List.replicate M true) (List.replicate d true) stream [])
      (clean (encodeRatio 0 0)) t ∧ t ≤ time.eval (M+d+stream.length+1) := by
  let s := state (List.replicate M true) (List.replicate d true) stream []
  have hs : ∀ i, (s i).length ≤ M+d+stream.length := by
    simpa [s] using state_bound (List.replicate M true) (List.replicate d true) stream []
  obtain ⟨t,ht,hb⟩ := zero_executes g s (M+d+stream.length) hs
  refine ⟨t+2,branchPop_empty _ _ _ _ g rfl ht,?_⟩
  have hm := polynomial_nat_eval_mono zeroTime
    (show M+d+stream.length ≤ M+d+stream.length+1 by omega)
  dsimp only at hm
  simp only [time,eval_add,eval_ofNat]
  omega

 theorem program_queryFree : program.QueryFree := by
  have hz : zero.QueryFree := seq_queryFree _ _ (clearList_queryFree _) (push_queryFree _ _)
  have hs : success.QueryFree := seq_queryFree _ _ (seq_queryFree _ _
    (rename_queryFree _ _ denominator_queryFree) (rename_queryFree _ _ numerator_queryFree))
    (rename_queryFree _ _ serialize_queryFree)
  exact branchPop_queryFree _ _ _ _ hz hz hs

end HiddenCircuits.Approximation.SelfReduction.Runtime.EstimateOutput
