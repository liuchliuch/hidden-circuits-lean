import HiddenCircuits.Circuit.Runtime.SampleEmitterLoop
import HiddenCircuits.Circuit.Runtime.BoundaryMaskEmitter

/-! Parse the canonical source, then emit the actual query
header and both zero-state boundary masks into the reversed output stream. -/
namespace HiddenCircuits.Circuit.Runtime.SampleEmitter
open HiddenCircuits.Complexity OracleBlock

def circuitParseEmbedding : Fin 4 ↪ Fin 32 where
  toFun i := (![8,4,14,15] : Fin 4 → Fin 32) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def maskEmbedding : Fin 6 ↪ Fin 32 where
  toFun i := (![4,5,14,15,16,17] : Fin 6 → Fin 32) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def parseCircuit : OracleBlock 31 :=
  seq (copyOn 0 8 17 (by decide) (by decide) (by decide)) (SamplePairParser.on circuitParseEmbedding)
noncomputable def header : OracleBlock 31 :=
  seq (copyOn 4 13 17 (by decide) (by decide) (by decide))
    (seq (repeatPrepend 13 5 [true,true,true,true]) (seq (push 5 false) (push 7 false)))
noncomputable def masks : OracleBlock 31 := rename BoundaryMask.program maskEmbedding
noncomputable def setup : OracleBlock 31 := seq parseCircuit (seq header masks)

def queryHeader (n : ℕ) : BitString := List.replicate (4*n) true++[false]
def queryPrefix (n : ℕ) : BitString := queryHeader n++encodeBitList [BoundaryMask.mask n,BoundaryMask.mask n]

set_option maxHeartbeats 800000 in
theorem parseCircuit_executes (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n)) (r s u : ℕ) :
    parseCircuit.Executes g (store (circuitBits n w) r s u 0 0 0 [] [] [] [] [] [])
      (store (circuitBits n w) r s u n 0 0 (encodeBitList (w.map gateBits)) [] [] [] [] [])
      (5*(circuitBits n w).length+5*n+11) := by
  have hc : (copyOn (0:Fin 32) 8 17 (by decide) (by decide) (by decide)).Executes g
      (store (circuitBits n w) r s u 0 0 0 [] [] [] [] [] [])
      (store (circuitBits n w) r s u 0 0 0 (circuitBits n w) [] [] [] [] []) (5*(circuitBits n w).length+2) := by
    convert copyOn_executes g (0:Fin 32) 8 17 (by decide) (by decide) (by decide)
      (store (circuitBits n w) r s u 0 0 0 [] [] [] [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [store]
  have hp : (SamplePairParser.on circuitParseEmbedding).Executes g
      (store (circuitBits n w) r s u 0 0 0 (circuitBits n w) [] [] [] [] [])
      (store (circuitBits n w) r s u n 0 0 (encodeBitList (w.map gateBits)) [] [] [] [] []) (5*n+7) := by
    convert SamplePairParser.on_executes circuitParseEmbedding g (List.replicate n true) (encodeBitList (w.map gateBits))
      (store (circuitBits n w) r s u 0 0 0 (circuitBits n w) [] [] [] [] [])
      (store (circuitBits n w) r s u n 0 0 (encodeBitList (w.map gateBits)) [] [] [] [] [])
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim) using 1
    simp
  convert seq_executes _ _ g hc hp using 1 <;> omega

set_option maxHeartbeats 800000 in
theorem header_executes (g : BitString → ℕ) (circuit : BitString) (r s u n : ℕ) (gates : BitString) :
    header.Executes g (store circuit r s u n 0 0 gates [] [] [] [] [])
      (store circuit r s u n 0 0 gates [] [] (queryHeader n).reverse [] [false]) (20*n+11) := by
  have hc : (copyOn (4:Fin 32) 13 17 (by decide) (by decide) (by decide)).Executes g
      (store circuit r s u n 0 0 gates [] [] [] [] [])
      (store circuit r s u n 0 n gates [] [] [] [] []) (5*n+2) := by
    convert copyOn_executes g (4:Fin 32) 13 17 (by decide) (by decide) (by decide)
      (store circuit r s u n 0 0 gates [] [] [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have he : (List.replicate n [true,true,true,true]).flatten=List.replicate (4*n) true := by
    clear hc
    induction n with
    | zero => rfl
    | succ n ih => simp only [List.replicate_succ,List.flatten_cons,ih];rw [Nat.mul_succ,Nat.add_comm (4*n),List.replicate_add];rfl
  have hr : (repeatPrepend (13:Fin 32) 5 [true,true,true,true]).Executes g
      (store circuit r s u n 0 n gates [] [] [] [] [])
      (store circuit r s u n 0 0 gates [] [] (List.replicate (4*n) true) [] []) (15*n+1) := by
    convert repeatPrepend_executes g (13:Fin 32) 5 (by decide) [true,true,true,true]
      (store circuit r s u n 0 n gates [] [] [] [] []) using 1
    · funext i;fin_cases i <;> simp [store,he]
    · simp [store]
  have hp : (push (5:Fin 32) false).Executes g
      (store circuit r s u n 0 0 gates [] [] (List.replicate (4*n) true) [] [])
      (store circuit r s u n 0 0 gates [] [] (queryHeader n).reverse [] []) 1 := by
    convert push_executes g (5:Fin 32) false (store circuit r s u n 0 0 gates [] [] (List.replicate (4*n) true) [] []) using 1
    funext i;fin_cases i <;> simp [store,queryHeader]
  have hs : (push (7:Fin 32) false).Executes g
      (store circuit r s u n 0 0 gates [] [] (queryHeader n).reverse [] [])
      (store circuit r s u n 0 0 gates [] [] (queryHeader n).reverse [] [false]) 1 := by
    convert push_executes g (7:Fin 32) false (store circuit r s u n 0 0 gates [] [] (queryHeader n).reverse [] []) using 1
    funext i;fin_cases i <;> rfl
  convert seq_executes _ _ g hc (seq_executes _ _ g hr (seq_executes _ _ g hp hs)) using 1 <;> omega

set_option maxHeartbeats 800000 in
theorem masks_executes (g : BitString → ℕ) (circuit : BitString) (r s u n : ℕ) (gates out : BitString) :
    masks.Executes g (store circuit r s u n 0 0 gates [] [] out [] [false])
      (store circuit r s u n 0 0 gates [] []
        ((encodeBitList [BoundaryMask.mask n,BoundaryMask.mask n]).reverse++out) [] [false]) (112*n+34) := by
  apply rename_executes_to _ maskEmbedding g (BoundaryMask.program_executes g n out)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 1 rfl).elim

theorem setup_executes (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n)) (r s u : ℕ) :
    setup.Executes g (store (circuitBits n w) r s u 0 0 0 [] [] [] [] [] [])
      (store (circuitBits n w) r s u n 0 0 (encodeBitList (w.map gateBits)) [] [] (queryPrefix n).reverse [] [false])
      (5*(circuitBits n w).length+137*n+60) := by
  have h := seq_executes _ _ g (parseCircuit_executes g w r s u)
    (seq_executes _ _ g (header_executes g (circuitBits n w) r s u n (encodeBitList (w.map gateBits)))
      (masks_executes g (circuitBits n w) r s u n (encodeBitList (w.map gateBits)) (queryHeader n).reverse))
  convert h using 1
  · simp only [queryPrefix,List.reverse_append]
  · omega

lemma setup_queryFree : setup.QueryFree :=
  seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (SamplePairParser.on_queryFree _))
    (seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (repeatPrepend_queryFree _ _ _) (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))))
      (rename_queryFree _ _ BoundaryMask.program_queryFree))
end HiddenCircuits.Circuit.Runtime.SampleEmitter
