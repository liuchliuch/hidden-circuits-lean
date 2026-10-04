import HiddenCircuits.Approximation.SelfReduction.Runtime.ClusterLoop

/-! One physical outer-loop
step copies the complete data, counts a neighborhood, and serializes its score. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
set_option maxHeartbeats 800000

def robustStore (value radius count : ℕ) (item data stream out : BitString) : Store 15 := fun i =>
  if i.val=0 then List.replicate value true else if i.val=1 then List.replicate radius true
  else if i.val=2 then List.replicate count true else if i.val=3 then item
  else if i.val=13 then data else if i.val=14 then stream else if i.val=15 then out else []

def robustParseEmbedding : Fin 4 ↪ Fin 16 where
  toFun i := if i.val=0 then 14 else if i.val=1 then 0 else if i.val=2 then 4 else 12
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def robustScanEmbedding : Fin 13 ↪ Fin 16 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h

noncomputable def robustParse : OracleBlock 15 := GraphVerifier.Runtime.unpairOn robustParseEmbedding
noncomputable def robustScan : OracleBlock 15 := rename neighborhoodScan robustScanEmbedding
noncomputable def robustBody : OracleBlock 15 :=
  seq robustParse (seq (clear 12) (seq (copyOn 13 3 4 (by decide) (by decide) (by decide))
    (seq robustScan (seq (emitUnaryReversed 2 15) (clear 0)))))

theorem robustParse_executes (g : BitString → ℕ) (value radius : ℕ) (data rest out : BitString) :
    robustParse.Executes g (robustStore 0 radius 0 [] data (pairBits (List.replicate value true) rest) out)
      (Function.update (robustStore value radius 0 [] data rest out) (12 : Fin 16) [true]) (5*value+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes robustParseEmbedding g
    (robustStore 0 radius 0 [] data (pairBits (List.replicate value true) rest) out)
    (Function.update (robustStore value radius 0 [] data rest out) (12 : Fin 16) [true])
    (pairBits (List.replicate value true) rest)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro j hj; fin_cases j; all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair,BinaryArithmetic.pair_parse_cost]
  omega

theorem robustScan_executes (g : BitString → ℕ) (value radius : ℕ) (xs : List ℕ) (B : ℕ)
    (hxs : ∀ x ∈ xs, x ≤ B) (rest out : BitString) :
    ∃ t, robustScan.Executes g
      (robustStore value radius 0 (unaryValues xs) (unaryValues xs) rest out)
      (robustStore value radius (neighborhoodCount value radius xs) [] (unaryValues xs) rest out) t ∧
      t  ≤  1+xs.length*(80*(B+value+radius+1)) := by
  obtain ⟨t,ht,hb⟩ := neighborhoodScan_executes g value radius xs 0 B hxs
  simp only [zero_add] at ht
  refine ⟨t,?_,hb⟩
  apply rename_executes_to neighborhoodScan robustScanEmbedding g ht
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · intro j hj; fin_cases j
    all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl)

theorem robustBody_executes (g : BitString → ℕ) (value radius : ℕ) (xs : List ℕ) (B : ℕ)
    (hvalue : value ≤ B) (hxs : ∀ x ∈ xs, x ≤ B) (rest out : BitString) :
    ∃ t, robustBody.Executes g
      (robustStore 0 radius 0 [] (unaryValues xs) (pairBits (List.replicate value true) rest) out)
      (robustStore 0 radius 0 [] (unaryValues xs) rest
        ((true::pairBits (List.replicate (neighborhoodCount value radius xs) true) []).reverse++out)) t ∧
      t+2  ≤  200*(xs.length+1)*(B+radius+1) := by
  have hp := robustParse_executes g value radius (unaryValues xs) rest out
  have hc : (clear (12 : Fin 16)).Executes g
      (Function.update (robustStore value radius 0 [] (unaryValues xs) rest out) (12 : Fin 16) [true])
      (robustStore value radius 0 [] (unaryValues xs) rest out) 2 := by
    convert clear_executes g (12 : Fin 16)
      (Function.update (robustStore value radius 0 [] (unaryValues xs) rest out) (12 : Fin 16) [true]) using 1
    funext i; fin_cases i <;> rfl
  have hcopy : (copyOn (13 : Fin 16) 3 4 (by decide) (by decide) (by decide)).Executes g
      (robustStore value radius 0 [] (unaryValues xs) rest out)
      (robustStore value radius 0 (unaryValues xs) (unaryValues xs) rest out)
      (5*(unaryValues xs).length+2) := by
    convert copyOn_executes g (13 : Fin 16) 3 4 (by decide) (by decide) (by decide)
      (robustStore value radius 0 [] (unaryValues xs) rest out) rfl using 1
    funext i; fin_cases i <;> simp [robustStore]
  obtain ⟨ts,hs,hbs⟩ := robustScan_executes g value radius xs B hxs rest out
  let score := neighborhoodCount value radius xs
  let out' := (true::pairBits (List.replicate score true) []).reverse++out
  have he : (emitUnaryReversed (2 : Fin 16) 15).Executes g
      (robustStore value radius score [] (unaryValues xs) rest out)
      (robustStore value radius 0 [] (unaryValues xs) rest out') (9*score+7) := by
    convert emitUnaryReversed_executes g (2 : Fin 16) 15 (by decide)
      (robustStore value radius score [] (unaryValues xs) rest out) using 1
    · funext i; fin_cases i <;> simp [robustStore,out']
    · simp [robustStore]
  have hd : (clear (0 : Fin 16)).Executes g
      (robustStore value radius 0 [] (unaryValues xs) rest out')
      (robustStore 0 radius 0 [] (unaryValues xs) rest out') (value+1) := by
    convert clear_executes g (0 : Fin 16)
      (robustStore value radius 0 [] (unaryValues xs) rest out') using 1
    · funext i; fin_cases i <;> rfl
    · simp [robustStore]
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hc (seq_executes _ _ g hcopy
    (seq_executes _ _ g hs (seq_executes _ _ g he hd)))),?_⟩
  have hlen := unaryValues_length_bound xs B hxs
  have hscore : score ≤ xs.length := neighborhoodCount_le value radius xs
  have hvalmul := Nat.mul_le_mul_left xs.length hvalue
  nlinarith

end HiddenCircuits.Approximation.SelfReduction.Runtime
