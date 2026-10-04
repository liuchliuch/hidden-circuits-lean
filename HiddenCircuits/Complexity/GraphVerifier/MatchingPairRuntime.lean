import HiddenCircuits.Complexity.GraphVerifier.MatrixLookup
import HiddenCircuits.Complexity.GraphVerifier.ReadOnlyLength
import HiddenCircuits.Complexity.GraphVerifier.MatchingPairDecision

/-! One actual read-only matrix/certificate pair check, including every scratch cleanup. -/
namespace HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
open OracleBlock Runtime

def pairForwardEmbedding : Fin 9 ↪ Fin 16 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 1 else if i.val=2 then 2 else if i.val=3 then 3 else if i.val=4 then 6 else if i.val=5 then 12 else if i.val=6 then 13 else if i.val=7 then 14 else 15
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def pairBackwardEmbedding : Fin 9 ↪ Fin 16 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 2 else if i.val=2 then 1 else if i.val=3 then 3 else if i.val=4 then 7 else if i.val=5 then 12 else if i.val=6 then 13 else if i.val=7 then 14 else 15
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def pairLeftEmbedding : Fin 9 ↪ Fin 16 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 1 else if i.val=2 then 2 else if i.val=3 then 4 else if i.val=4 then 8 else if i.val=5 then 12 else if i.val=6 then 13 else if i.val=7 then 14 else 15
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def pairRightEmbedding : Fin 9 ↪ Fin 16 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 2 else if i.val=2 then 1 else if i.val=3 then 4 else if i.val=4 then 9 else if i.val=5 then 12 else if i.val=6 then 13 else if i.val=7 then 14 else 15
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def pairDiagonalEmbedding : Fin 6 ↪ Fin 16 where
  toFun i := if i.val=0 then 1 else if i.val=1 then 2 else if i.val=2 then 10 else if i.val=3 then 12 else if i.val=4 then 13 else 14
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def pairDecisionEmbedding : Fin 7 ↪ Fin 16 where
  toFun i := if i.val=0 then 6 else if i.val=1 then 7 else if i.val=2 then 8 else if i.val=3 then 9 else if i.val=4 then 10 else if i.val=5 then 5 else 11
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def pairCheckBlock : OracleBlock 15 :=
  seq (matrixLookupOn pairForwardEmbedding) (seq (matrixLookupOn pairBackwardEmbedding)
    (seq (matrixLookupOn pairLeftEmbedding) (seq (matrixLookupOn pairRightEmbedding)
      (seq (readLengthOn pairDiagonalEmbedding) (seq (rename pairDecisionBlock pairDecisionEmbedding)
        (reverseOn 11 5 (by decide)))))))

def pairStore (n i j : ℕ) (payload witness acc forward backward left right diagonal output : BitString) : Store 15 := fun r =>
  if r.val=0 then List.replicate n true else if r.val=1 then List.replicate i true
  else if r.val=2 then List.replicate j true else if r.val=3 then payload else if r.val=4 then witness
  else if r.val=5 then acc else if r.val=6 then forward else if r.val=7 then backward
  else if r.val=8 then left else if r.val=9 then right else if r.val=10 then diagonal
  else if r.val=11 then output else []

 theorem lookup_toList_bitAt (xs : BitString) (k : ℕ) (hk : k<xs.length) :
    xs[k]?.toList=[bitAt xs k] := by simp [bitAt,List.getElem?_eq_getElem,hk]

 theorem pair_index_bound (n i j : ℕ) (hi : i<n) (hj : j<n) : j+n*i<n*n := by
  have hm := Nat.mul_le_mul_left n (show i+1≤n by omega)
  nlinarith

/-- Every elementary bit access is implemented by the compiled read-only routines.
The length premises are precisely the preceding parser/length guards. -/
theorem pairCheck_executes (g : BitString → ℕ) (n i j : ℕ) (payload witness : BitString) (a : Bool)
    (hp : payload.length=n*n) (hw : n*n≤witness.length) (hi : i<n) (hj : j<n) :
    ∃ cost, pairCheckBlock.Executes g (pairStore n i j payload witness [a] [] [] [] [] [] [])
      (pairStore n i j payload witness [a && entryFlag n payload witness i j] [] [] [] [] [] []) cost ∧
      cost≤56*n^2+118*n+134 := by
  let e := bitAt payload (j+n*i)
  let b := bitAt payload (i+n*j)
  let l := bitAt witness (j+n*i)
  let r := bitAt witness (i+n*j)
  let d := decide (i=j)
  let result := pairDecision e b l r d a
  let s₀ := pairStore n i j payload witness [a] [] [] [] [] [] []
  let s₁ := pairStore n i j payload witness [a] [e] [] [] [] [] []
  let s₂ := pairStore n i j payload witness [a] [e] [b] [] [] [] []
  let s₃ := pairStore n i j payload witness [a] [e] [b] [l] [] [] []
  let s₄ := pairStore n i j payload witness [a] [e] [b] [l] [r] [] []
  let s₅ := pairStore n i j payload witness [a] [e] [b] [l] [r] [d] []
  let s₆ := pairStore n i j payload witness [] [] [] [] [] [] [result]
  let s₇ := pairStore n i j payload witness [result] [] [] [] [] [] []
  have hij : j+n*i<payload.length := by rw [hp];exact pair_index_bound n i j hi hj
  have hji : i+n*j<payload.length := by rw [hp];exact pair_index_bound n j i hj hi
  have h₁ : (matrixLookupOn pairForwardEmbedding).Executes g s₀ s₁ (matrixLookupCost n i j payload) := by
    have h := matrixLookupOn_executes pairForwardEmbedding g s₀ n i j payload
      (by funext z;fin_cases z <;> rfl)
    rw [lookup_toList_bitAt payload _ hij] at h
    convert h using 1
    funext z;fin_cases z <;> simp [s₀,s₁,pairStore,pairForwardEmbedding,e]
  have h₂ : (matrixLookupOn pairBackwardEmbedding).Executes g s₁ s₂ (matrixLookupCost n j i payload) := by
    have h := matrixLookupOn_executes pairBackwardEmbedding g s₁ n j i payload
      (by funext z;fin_cases z <;> rfl)
    rw [lookup_toList_bitAt payload _ hji] at h
    convert h using 1
    funext z;fin_cases z <;> simp [s₁,s₂,pairStore,pairBackwardEmbedding,b]
  have h₃ : (matrixLookupOn pairLeftEmbedding).Executes g s₂ s₃ (matrixLookupCost n i j witness) := by
    have h := matrixLookupOn_executes pairLeftEmbedding g s₂ n i j witness
      (by funext z;fin_cases z <;> rfl)
    rw [lookup_toList_bitAt witness _ (lt_of_lt_of_le (pair_index_bound n i j hi hj) hw)] at h
    convert h using 1
    funext z;fin_cases z <;> simp [s₂,s₃,pairStore,pairLeftEmbedding,l]
  have h₄ : (matrixLookupOn pairRightEmbedding).Executes g s₃ s₄ (matrixLookupCost n j i witness) := by
    have h := matrixLookupOn_executes pairRightEmbedding g s₃ n j i witness
      (by funext z;fin_cases z <;> rfl)
    rw [lookup_toList_bitAt witness _ (lt_of_lt_of_le (pair_index_bound n j i hj hi) hw)] at h
    convert h using 1
    funext z;fin_cases z <;> simp [s₃,s₄,pairStore,pairRightEmbedding,r]
  obtain ⟨c,hc,hcb⟩ := readLengthOn_executes pairDiagonalEmbedding g s₄
    (List.replicate i true) (List.replicate j true) (by funext z;fin_cases z <;> rfl)
  have h₅ : (readLengthOn pairDiagonalEmbedding).Executes g s₄ s₅ c := by
    simp only [List.length_replicate] at hc
    convert hc using 1
    funext z;fin_cases z <;> simp [s₄,s₅,pairStore,pairDiagonalEmbedding,d]
  have h₆ : (rename pairDecisionBlock pairDecisionEmbedding).Executes g s₅ s₆ 16 := by
    apply rename_executes_to pairDecisionBlock pairDecisionEmbedding g (pairDecision_executes g e b l r d a)
    · funext z;fin_cases z <;> rfl
    · funext z;fin_cases z <;> rfl
    · intro z hz
      fin_cases z
      all_goals first | rfl | exact False.elim (hz 0 rfl) | exact False.elim (hz 1 rfl) |
        exact False.elim (hz 2 rfl) | exact False.elim (hz 3 rfl) | exact False.elim (hz 4 rfl) |
        exact False.elim (hz 5 rfl) | exact False.elim (hz 6 rfl)
  have h₇ : (reverseOn (11:Fin 16) 5 (by decide)).Executes g s₆ s₇ 3 := by
    have h := reverseOn_executes g (11:Fin 16) 5 (by decide) s₆
    convert h using 1
    funext z;fin_cases z <;> simp [s₆,s₇,pairStore]
  have hall := seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃
    (seq_executes _ _ g h₄ (seq_executes _ _ g h₅ (seq_executes _ _ g h₆ h₇)))))
  have hresult : result=(a && entryFlag n payload witness i j) := pairDecision_correct n payload witness i j a
  refine ⟨matrixLookupCost n i j payload+matrixLookupCost n j i payload+
    matrixLookupCost n i j witness+matrixLookupCost n j i witness+c+31,?_,?_⟩
  · simpa only [s₇,hresult,Nat.add_assoc] using hall
  · have hb₁ := matrixLookupCost_in_range n i j payload hi hj
    have hb₂ := matrixLookupCost_in_range n j i payload hj hi
    have hb₃ := matrixLookupCost_in_range n i j witness hi hj
    have hb₄ := matrixLookupCost_in_range n j i witness hj hi
    simp only [List.length_replicate] at hcb hb₃ hb₄
    nlinarith

 theorem pairCheck_queryFree : pairCheckBlock.QueryFree :=
  seq_queryFree _ _ (matrixLookupOn_queryFree _) (seq_queryFree _ _ (matrixLookupOn_queryFree _)
    (seq_queryFree _ _ (matrixLookupOn_queryFree _) (seq_queryFree _ _ (matrixLookupOn_queryFree _)
      (seq_queryFree _ _ (readLengthOn_queryFree _) (seq_queryFree _ _
        (rename_queryFree _ _ pairDecision_queryFree) (reverseOn_queryFree _ _ _))))))

end HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
