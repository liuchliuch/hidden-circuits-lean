import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverDimensions
import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverState
import HiddenCircuits.Complexity.UnaryArithmetic

/-! Fresh reconstruction of physical unary degree clocks and rational accumulator
initialization. No dimension or coefficient is supplied as a certificate. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 1200000

def initState (w : WordInstance) (width degree clock work square : ℕ) (source target letters rest num den : BitString) : Store 97 := fun i =>
  if i.val=0 then wordBits w else if i.val=1 then List.replicate w.particles true
  else if i.val=2 then List.replicate w.word.length true else if i.val=3 then List.replicate width true
  else if i.val=4 then List.replicate degree true else if i.val=5 then List.replicate clock true
  else if i.val=10 then num else if i.val=11 then den else if i.val=15 then rest
  else if i.val=16 then source else if i.val=17 then target else if i.val=18 then letters
  else if i.val=20 then List.replicate work true else if i.val=21 then List.replicate square true else []
noncomputable def initializeWidth : OracleBlock 97 := seq (copyOn 1 3 23 (by decide) (by decide) (by decide))
  (copyOn 1 3 23 (by decide) (by decide) (by decide))
noncomputable def initializeDegree : OracleBlock 97 := seq (copyOn 2 20 23 (by decide) (by decide) (by decide))
  (seq (repeatCopy 20 1 21 23 (by decide) (by decide) (by decide))
    (repeatCopy 21 1 4 23 (by decide) (by decide) (by decide)))
noncomputable def initializeClock : OracleBlock 97 := seq (copyOn 4 5 23 (by decide) (by decide) (by decide)) (push 5 true)
noncomputable def initializeClear : OracleBlock 97 := clearList [16,17,18,15]
noncomputable def initializeAccumulator : OracleBlock 97 := seq (push 10 false) (seq (push 11 true) (push 11 false))
noncomputable def initializeProgram : OracleBlock 97 := seq initializeWidth (seq initializeDegree
  (seq initializeClock (seq initializeClear initializeAccumulator)))

lemma initializeWidth_executes (g : BitString → ℕ) (w : WordInstance) (S T L R : BitString) :
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

lemma initializeDegree_executes (g : BitString → ℕ) (w : WordInstance) (S T L R : BitString) :
    initializeDegree.Executes g (initState w (2*w.particles) 0 0 0 0 S T L R [] [])
      (initState w (2*w.particles) (Recovery.degree w) 0 0 0 S T L R [] [])
      (5*w.word.length+(5*w.particles+4)*w.word.length+(5*w.particles+4)*(w.word.length*w.particles)+8) := by
  let st := fun d a b => initState w (2*w.particles) d 0 a b S T L R [] []
  have h1 : (copyOn (2:Fin 98) 20 23 (by decide) (by decide) (by decide)).Executes g
      (st 0 0 0) (st 0 w.word.length 0) (5*w.word.length+2) := by
    convert copyOn_executes g (2:Fin 98) 20 23 (by decide) (by decide) (by decide) (st 0 0 0) rfl using 1
    · funext i;fin_cases i <;> simp [st,initState]
    · simp [st,initState]
  have h2 : (repeatCopy (20:Fin 98) 1 21 23 (by decide) (by decide) (by decide)).Executes g
      (st 0 w.word.length 0) (st 0 0 (w.word.length*w.particles)) ((5*w.particles+4)*w.word.length+1) := by
    convert unaryMultiply_executes g (20:Fin 98) 1 21 23 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (st 0 w.word.length 0) w.word.length w.particles rfl rfl rfl using 1
    funext i;fin_cases i <;> simp [st,initState,workStore]
  have h3 : (repeatCopy (21:Fin 98) 1 4 23 (by decide) (by decide) (by decide)).Executes g
      (st 0 0 (w.word.length*w.particles)) (st (Recovery.degree w) 0 0)
      ((5*w.particles+4)*(w.word.length*w.particles)+1) := by
    convert unaryMultiply_executes g (21:Fin 98) 1 4 23 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (st 0 0 (w.word.length*w.particles)) (w.word.length*w.particles) w.particles rfl rfl rfl using 1
    funext i;fin_cases i <;> simp [st,initState,workStore,Recovery.degree,pow_two,Nat.mul_assoc]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1 <;> omega


lemma initializeClock_executes (g : BitString → ℕ) (w : WordInstance) (S T L R : BitString) :
    initializeClock.Executes g (initState w (2*w.particles) (Recovery.degree w) 0 0 0 S T L R [] [])
      (initState w (2*w.particles) (Recovery.degree w) (Recovery.degree w+1) 0 0 S T L R [] [])
      (5*Recovery.degree w+5) := by
  let st := fun clock => initState w (2*w.particles) (Recovery.degree w) clock 0 0 S T L R [] []
  have h1 : (copyOn (4:Fin 98) 5 23 (by decide) (by decide) (by decide)).Executes g
      (st 0) (st (Recovery.degree w)) (5*Recovery.degree w+2) := by
    convert copyOn_executes g (4:Fin 98) 5 23 (by decide) (by decide) (by decide) (st 0) rfl using 1
    · funext i;fin_cases i <;> simp [st,initState]
    · simp [st,initState]
  have h2 : (push (5:Fin 98) true).Executes g (st (Recovery.degree w)) (st (Recovery.degree w+1)) 1 := by
    convert push_executes g (5:Fin 98) true (st (Recovery.degree w)) using 1
    funext i;fin_cases i <;> simp [st,initState,List.replicate_succ]
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

lemma initializeClear_executes (g : BitString → ℕ) (w : WordInstance) (S T L R : BitString) :
    initializeClear.Executes g
      (initState w (2*w.particles) (Recovery.degree w) (Recovery.degree w+1) 0 0 S T L R [] [])
      (initState w (2*w.particles) (Recovery.degree w) (Recovery.degree w+1) 0 0 [] [] [] [] [] [])
      (S.length+T.length+L.length+R.length+13) := by
  let st := fun S T L R => initState w (2*w.particles) (Recovery.degree w) (Recovery.degree w+1) 0 0 S T L R [] []
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

lemma initializeAccumulator_executes (g : BitString → ℕ) (w : WordInstance) :
    initializeAccumulator.Executes g
      (initState w (2*w.particles) (Recovery.degree w) (Recovery.degree w+1) 0 0 [] [] [] [] [] [])
      (state w (Recovery.degree w+1) 0 0 0 0 (0,1) [] [] []) 7 := by
  let st := initState w (2*w.particles) (Recovery.degree w) (Recovery.degree w+1) 0 0 [] [] [] [] [] []
  have h1 := push_executes g (10:Fin 98) false st
  have h2 := push_executes g (11:Fin 98) true (Function.update st 10 [false])
  have h3 := push_executes g (11:Fin 98) false (Function.update (Function.update st 10 [false]) 11 [true])
  have hh := seq_executes _ _ g h1 (seq_executes _ _ g h2 h3)
  convert hh using 1
  funext i;fin_cases i <;> rfl

theorem initialize_executes (g : BitString → ℕ) (w : WordInstance) (rest : BitString) :
    ∃c,initializeProgram.Executes g (Function.update (bareState w 0 0 0) 15 rest)
      (state w (Recovery.degree w+1) 0 0 0 0 (0,1) [] [] []) c ∧
      c≤100*(w.particles+w.word.length+1)^3+(encodeBitList (w.word.map letterBits)).length+rest.length+25 := by
  let S := stateBits w.source
  let T := stateBits w.target
  let L := encodeBitList (w.word.map letterBits)
  have he : Function.update (bareState w 0 0 0) (15:Fin 98) rest=initState w 0 0 0 0 0 S T L rest [] [] := by
    funext i;fin_cases i <;> rfl
  rw [he]
  have hh := seq_executes _ _ g (initializeWidth_executes g w S T L rest)
    (seq_executes _ _ g (initializeDegree_executes g w S T L rest)
      (seq_executes _ _ g (initializeClock_executes g w S T L rest)
        (seq_executes _ _ g (initializeClear_executes g w S T L rest) (initializeAccumulator_executes g w))))
  refine ⟨_,hh,?_⟩
  clear hh
  have hp := w.positive
  dsimp [S,T,L]
  simp only [stateBits_length]
  unfold Recovery.degree
  nlinarith [Nat.zero_le (w.particles^3),Nat.zero_le (w.word.length^3),
    Nat.zero_le (w.particles^2*w.word.length),Nat.zero_le (w.particles*w.word.length^2)]
end HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
