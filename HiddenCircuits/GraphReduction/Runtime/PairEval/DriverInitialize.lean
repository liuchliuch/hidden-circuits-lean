import HiddenCircuits.GraphReduction.Runtime.PairEval.Input
import HiddenCircuits.GraphReduction.Runtime.PairEval.DriverState
import HiddenCircuits.Complexity.UnaryArithmetic

/-! Fresh reconstruction of physical unary degree clocks and rational accumulator
initialization. No dimension or coefficient is supplied as a certificate. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.Driver
open Complexity OracleBlock BinaryArithmetic WordGraph
set_option maxHeartbeats 1200000

def initState (w : PairInput) (width degree clock work square : ℕ) (source target letters rest num den : BitString) : Store 97 := fun i =>
  if i.val=0 then pairInputBits w else if i.val=1 then List.replicate w.particles true
  else if i.val=2 then List.replicate w.pairs.length true else if i.val=3 then List.replicate width true
  else if i.val=4 then List.replicate degree true else if i.val=5 then List.replicate clock true
  else if i.val=10 then num else if i.val=11 then den else if i.val=15 then rest
  else if i.val=16 then source else if i.val=17 then target else if i.val=18 then letters
  else if i.val=20 then List.replicate work true else if i.val=21 then List.replicate square true else []
noncomputable def initializeWidth : OracleBlock 97 := seq (copyOn 1 3 23 (by decide) (by decide) (by decide))
  (copyOn 1 3 23 (by decide) (by decide) (by decide))
noncomputable def initializeDegree : OracleBlock 97 := seq (copyOn 2 20 23 (by decide) (by decide) (by decide))
  (repeatCopy 20 3 4 23 (by decide) (by decide) (by decide))
noncomputable def initializeClock : OracleBlock 97 := seq (copyOn 4 5 23 (by decide) (by decide) (by decide)) (push 5 true)
noncomputable def initializeClear : OracleBlock 97 := clearList [16,17,18,15]
noncomputable def initializeAccumulator : OracleBlock 97 := seq (push 10 false) (seq (push 11 true) (push 11 false))
noncomputable def initializeProgram : OracleBlock 97 := seq initializeWidth (seq initializeDegree
  (seq initializeClock (seq initializeClear initializeAccumulator)))

lemma initializeWidth_executes (g : BitString → ℕ) (w : PairInput) (S T L R : BitString) :
    initializeWidth.Executes g (initState w 0 0 0 0 0 S T L R [] [])
      (initState w (2*w.particles) 0 0 0 0 S T L R [] []) (10*w.particles+6) := by
  let st := fun width => initState w width 0 0 0 0 S T L R [] []
  have h1 : (copyOn (1:Fin 98) 3 23 (by decide) (by decide) (by decide)).Executes g
      (st 0) (st w.particles) (5*w.particles+2) := by
    convert copyOn_executes g (1:Fin 98) 3 23 (by decide) (by decide) (by decide) (st 0) rfl using 1
    · funext i;fin_cases i <;> simp [st,initState]
    · simp [st,initState]
  have h2 : (copyOn (1:Fin 98) 3 23 (by decide) (by decide) (by decide)).Executes g
      (st w.particles) (st (2*w.particles)) (5*w.particles+2) := by
    convert copyOn_executes g (1:Fin 98) 3 23 (by decide) (by decide) (by decide) (st w.particles) rfl using 1
    · funext i;fin_cases i <;> simp [st,initState,←List.replicate_add,two_mul]
    · simp [st,initState]
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

lemma initializeDegree_executes (g : BitString → ℕ) (w : PairInput) (S T L R : BitString) :
    initializeDegree.Executes g (initState w (2*w.particles) 0 0 0 0 S T L R [] [])
      (initState w (2*w.particles) (degree w) 0 0 0 S T L R [] [])
      (5*w.pairs.length+(10*w.particles+4)*w.pairs.length+5) := by
  let st := fun d a => initState w (2*w.particles) d 0 a 0 S T L R [] []
  have h1 : (copyOn (2:Fin 98) 20 23 (by decide) (by decide) (by decide)).Executes g
      (st 0 0) (st 0 w.pairs.length) (5*w.pairs.length+2) := by
    convert copyOn_executes g (2:Fin 98) 20 23 (by decide) (by decide) (by decide) (st 0 0) rfl using 1
    · funext i;fin_cases i <;> simp [st,initState]
    · simp [st,initState]
  have h2 : (repeatCopy (20:Fin 98) 3 4 23 (by decide) (by decide) (by decide)).Executes g
      (st 0 w.pairs.length) (st (degree w) 0) ((10*w.particles+4)*w.pairs.length+1) := by
    convert unaryMultiply_executes g (20:Fin 98) 3 4 23 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (st 0 w.pairs.length) w.pairs.length (2*w.particles) rfl rfl rfl using 1
    · funext i;fin_cases i <;> simp [st,initState,workStore,degree,Nat.mul_comm]
    · ring
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

lemma initializeClock_executes (g : BitString → ℕ) (w : PairInput) (S T L R : BitString) :
    initializeClock.Executes g (initState w (2*w.particles) (degree w) 0 0 0 S T L R [] [])
      (initState w (2*w.particles) (degree w) (degree w+1) 0 0 S T L R [] [])
      (5*degree w+5) := by
  let st := fun clock => initState w (2*w.particles) (degree w) clock 0 0 S T L R [] []
  have h1 : (copyOn (4:Fin 98) 5 23 (by decide) (by decide) (by decide)).Executes g
      (st 0) (st (degree w)) (5*degree w+2) := by
    convert copyOn_executes g (4:Fin 98) 5 23 (by decide) (by decide) (by decide) (st 0) rfl using 1
    · funext i;fin_cases i <;> simp [st,initState]
    · simp [st,initState]
  have h2 : (push (5:Fin 98) true).Executes g (st (degree w)) (st (degree w+1)) 1 := by
    convert push_executes g (5:Fin 98) true (st (degree w)) using 1
    funext i;fin_cases i <;> simp [st,initState,List.replicate_succ]
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

lemma initializeClear_executes (g : BitString → ℕ) (w : PairInput) (S T L R : BitString) :
    initializeClear.Executes g
      (initState w (2*w.particles) (degree w) (degree w+1) 0 0 S T L R [] [])
      (initState w (2*w.particles) (degree w) (degree w+1) 0 0 [] [] [] [] [] [])
      (S.length+T.length+L.length+R.length+13) := by
  let st := fun S T L R => initState w (2*w.particles) (degree w) (degree w+1) 0 0 S T L R [] []
  have h1 : (clear (16:Fin 98)).Executes g (st S T L R) (st [] T L R) (S.length+1) := by
    convert clear_executes g (16:Fin 98) (st S T L R) using 1
    funext i;fin_cases i <;> rfl
  have h2 : (clear (17:Fin 98)).Executes g (st [] T L R) (st [] [] L R) (T.length+1) := by
    convert clear_executes g (17:Fin 98) (st [] T L R) using 1
    funext i;fin_cases i <;> rfl
  have h3 : (clear (18:Fin 98)).Executes g (st [] [] L R) (st [] [] [] R) (L.length+1) := by
    convert clear_executes g (18:Fin 98) (st [] [] L R) using 1
    funext i;fin_cases i <;> rfl
  have h4 : (clear (15:Fin 98)).Executes g (st [] [] [] R) (st [] [] [] []) (R.length+1) := by
    convert clear_executes g (15:Fin 98) (st [] [] [] R) using 1
    funext i;fin_cases i <;> rfl
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (skip_executes g (st [] [] [] []))))) using 1 <;> omega

lemma initializeAccumulator_executes (g : BitString → ℕ) (w : PairInput) :
    initializeAccumulator.Executes g
      (initState w (2*w.particles) (degree w) (degree w+1) 0 0 [] [] [] [] [] [])
      (state w (degree w+1) 0 (0,1) [] [] []) 7 := by
  let st := initState w (2*w.particles) (degree w) (degree w+1) 0 0 [] [] [] [] [] []
  have h1 := push_executes g (10:Fin 98) false st
  have h2 := push_executes g (11:Fin 98) true (Function.update st 10 [false])
  have h3 := push_executes g (11:Fin 98) false (Function.update (Function.update st 10 [false]) 11 [true])
  have hh := seq_executes _ _ g h1 (seq_executes _ _ g h2 h3)
  convert hh using 1
  funext i;fin_cases i <;> rfl

def parserEmbedding : Fin 18 ↪ Fin 98 where
  toFun i := ![0,1,16,17,18,2,6,7,8,9,10,11,12,13,14,15,19,20] i
  inj' := by decide +kernel
noncomputable def parse : OracleBlock 97 := rename Input.program parserEmbedding
lemma parse_executes (g : BitString → ℕ) (w : PairInput) :
    ∃c, parse.Executes g (Function.update (fun _=>[]) 0 (pairInputBits w))
      (initState w 0 0 0 0 0 (stateBits w.source) (stateBits w.target) (pairStream w.pairs) [] [] []) c ∧
      c ≤ 40*(pairInputBits w).length+100 := by
  obtain ⟨c,hc,hb⟩ := Input.program_executes g w 0
  refine ⟨c,?_,hb⟩
  apply rename_executes_to Input.program parserEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := by intro h;exact hi 0 h.symm
    have h0v : i.val ≠ 0 := by intro h;exact h0 (Fin.ext h)
    have h1 : i.val ≠ 1 := by intro h;exact hi 1 (Fin.ext h.symm)
    have h2 : i.val ≠ 2 := by intro h;exact hi 5 (Fin.ext h.symm)
    have h16 : i.val ≠ 16 := by intro h;exact hi 2 (Fin.ext h.symm)
    have h17 : i.val ≠ 17 := by intro h;exact hi 3 (Fin.ext h.symm)
    have h18 : i.val ≠ 18 := by intro h;exact hi 4 (Fin.ext h.symm)
    simp [initState,Function.update_of_ne h0,h0v,h1,h2,h16,h17,h18]

noncomputable def setup : OracleBlock 97 := seq parse initializeProgram
noncomputable def initializeTime : Polynomial ℕ := 1000*(Polynomial.X+1)^3

theorem initialize_executes (g : BitString → ℕ) (w : PairInput) :
    ∃c, setup.Executes g (Function.update (fun _=>[]) 0 (pairInputBits w))
      (state w (degree w+1) 0 (0,1) [] [] []) c ∧
      c ≤ initializeTime.eval (pairInputBits w).length := by
  let S := stateBits w.source
  let T := stateBits w.target
  let L := pairStream w.pairs
  obtain ⟨a,ha,hab⟩ := parse_executes g w
  have hh := seq_executes _ _ g (initializeWidth_executes g w S T L [])
    (seq_executes _ _ g (initializeDegree_executes g w S T L [])
      (seq_executes _ _ g (initializeClock_executes g w S T L [])
        (seq_executes _ _ g (initializeClear_executes g w S T L []) (initializeAccumulator_executes g w))))
  refine ⟨_,seq_executes _ _ g ha hh,?_⟩
  clear hh ha
  have hl := pairInputBits_length_lower w
  have hL : L.length ≤ (pairInputBits w).length := by simp [L,pairInputBits,pairStream];omega
  dsimp [S,T]
  simp only [stateBits_length,List.length_nil]
  simp only [initializeTime,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  dsimp [degree]
  have hp : w.particles ≤ (pairInputBits w).length := by omega
  have hn : w.pairs.length ≤ (pairInputBits w).length := by omega
  have hm := Nat.mul_le_mul hp hn
  nlinarith [Nat.zero_le ((pairInputBits w).length^3),Nat.zero_le ((pairInputBits w).length^2)]
end HiddenCircuits.GraphReduction.Runtime.PairEval.Driver
