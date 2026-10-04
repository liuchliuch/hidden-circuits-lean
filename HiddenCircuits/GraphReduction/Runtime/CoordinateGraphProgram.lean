import HiddenCircuits.GraphReduction.Runtime.CoordinateGraphFront
import HiddenCircuits.GraphReduction.Runtime.CoordinateGraphCallback

namespace HiddenCircuits.GraphReduction.Runtime.CoordinateGraph
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic Polynomial
set_option maxRecDepth 2000
set_option maxHeartbeats 1200000
noncomputable def emit : OracleBlock 31 := MatrixEmitter.block callback
noncomputable def finishOutput : OracleBlock 31 := seq (clear 0) (moveOn 7 0 27 (by decide) (by decide) (by decide))
noncomputable def program : OracleBlock 31 := seq front (seq emit finishOutput)
noncomputable def rowTime : Polynomial ℕ :=300*(X+1)^2+IntegerDistance.time.comp (4*(X+1))
noncomputable def time : Polynomial ℕ :=1000*(X+1)^4+X^2*(rowTime+20)
noncomputable def size : Polynomial ℕ :=X^2+2*X+1

lemma callback_bound (xs : BitString) :
    callbackBound (LooseWordList.words (coordinates xs)).length (coordinates xs).length (signedBits (denominator xs)).length≤rowTime.eval xs.length := by
  let M:=xs.length
  have hn:=vertices_length xs
  have hl:=coordinate_length xs
  have hd:=denominator_length xs
  have hp:=polynomial_nat_eval_mono IntegerDistance.time
    (show (coordinates xs).length+(signedBits (denominator xs)).length+3≤4*(M+1) by dsimp[M];omega)
  dsimp only at hp
  have hraw:rawLookupBound (coordinates xs).length (LooseWordList.words (coordinates xs)).length≤rawLookupBound M M := by
    unfold rawLookupBound;gcongr
  unfold callbackBound
  simp only [rowTime,eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one,eval_comp]
  dsimp only [M] at hp hraw
  unfold rawLookupBound at hraw ⊢
  nlinarith

lemma emit_executes (g : BitString → ℕ) (xs : BitString) :
    ∃c,emit.Executes g (callbackState (LooseWordList.words (coordinates xs)).length 0 0 [] [] [] (coordinates xs) (denominator xs))
      (Function.update (callbackState (LooseWordList.words (coordinates xs)).length 0 0 [] [] [] (coordinates xs) (denominator xs)) 7 (bits xs)) c ∧
      c≤xs.length^2*(rowTime.eval xs.length+18)+40*xs.length+30 := by
  let n:=(LooseWordList.words (coordinates xs)).length
  obtain ⟨c,hc,hb⟩:=MatrixEmitter.block_executes callback (edge (denominator xs) (coordinates xs)) n
    (callbackBound n (coordinates xs).length (signedBits (denominator xs)).length) (params (coordinates xs) (denominator xs))
    (fun g i j out inner outer hi hj=>callback_executes g n i j out inner outer (coordinates xs) (denominator xs) hi hj) g
  refine ⟨c,hc,hb.trans ?_⟩
  have hn:=vertices_length xs
  have ht:=callback_bound xs
  change n*n*(callbackBound n _ _+18)+40*n+30≤_
  dsimp only [n] at *
  rw [pow_two]
  gcongr

lemma finishOutput_executes (g : BitString → ℕ) (xs : BitString) :
    ∃s,finishOutput.Executes g
      (Function.update (callbackState (LooseWordList.words (coordinates xs)).length 0 0 [] [] [] (coordinates xs) (denominator xs)) 7 (bits xs)) s
      ((LooseWordList.words (coordinates xs)).length+6*(bits xs).length+8) ∧s 0=bits xs := by
  let base:=callbackState (LooseWordList.words (coordinates xs)).length 0 0 [] [] [] (coordinates xs) (denominator xs)
  let s0:=Function.update base (7:Fin 32) (bits xs)
  let s1:=Function.update s0 (0:Fin 32) []
  have h1:=clear_executes g (0:Fin 32) s0
  have h2:=moveOn_executes g (7:Fin 32) 0 27 (by decide) (by decide) (by decide) s1 rfl
  refine ⟨Function.update (Function.update s1 (0:Fin 32) (s1 7++s1 0)) (7:Fin 32) [],?_,?_⟩
  · convert seq_executes _ _ g h1 h2 using 1
    simp [s0,s1,base,callbackState,MatrixEmitter.store,MatrixEmitter.port]
    omega
  · simp [s1,s0]

theorem program_executes (g : BitString → ℕ) (xs : BitString) :
    ∃s c,program.Executes g (Function.update (fun _=>[]) 0 xs) s c ∧s 0=bits xs ∧c≤time.eval xs.length := by
  obtain ⟨a,ha,hba⟩:=front_executes g xs
  obtain ⟨b,hb,hbb⟩:=emit_executes g xs
  obtain ⟨s,hs,ho⟩:=finishOutput_executes g xs
  refine ⟨s,_,seq_executes _ _ g ha (seq_executes _ _ g hb hs),ho,?_⟩
  have hn:=vertices_length xs
  have hbits:=bits_length xs
  simp only [time,eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
  nlinarith [sq_nonneg (xs.length:ℤ)]
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ front_queryFree
  (seq_queryFree _ _ (MatrixEmitter.block_queryFree callback callback_queryFree)
    (seq_queryFree _ _ (clear_queryFree _) (moveOn_queryFree _ _ _ _ _ _)))
lemma size_bound (xs : BitString) : (bits xs).length≤size.eval xs.length := by
  simpa only [size,eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one] using bits_length xs
end HiddenCircuits.GraphReduction.Runtime.CoordinateGraph
