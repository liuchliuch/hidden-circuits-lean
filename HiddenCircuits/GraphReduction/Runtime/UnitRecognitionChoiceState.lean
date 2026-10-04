import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionScoreLoop
import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionBetter

/-! Literal ports and read routines for first-maximum unit-interval selection. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionChoice
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

abbrev Best (n : ℕ) := Option (Fin n)
def index {n : ℕ} (b : Best n) : ℕ := (b.map Fin.val).getD 0
def selectedScore {n : ℕ} (G : MatrixData n) (S : Vector Bool n) (b : Best n) : ℕ :=
  (b.map (UnitRecognitionScore.score G S)).getD 0

def prefer {n : ℕ} (G : MatrixData n) (A S R : Vector Bool n) (b : Best n) (i : Fin n) : Bool :=
  UnitRecognitionBetter.better (UnitRecognitionScore.score G S i) (UnitRecognitionScore.score G A i)
    (selectedScore G S b) (selectedScore G A b) b.isSome R[i.val]
def step {n : ℕ} (G : MatrixData n) (A S R : Vector Bool n) (i : Fin n) (b : Best n) : Best n :=
  if prefer G A S R b i then some i else b

def rawState (n i : ℕ) (payload alive selected remaining best bestScore bestDegree found clock ns nd eligible decision : BitString) : Store 32 :=
  fun r => if r.val=0 then List.replicate n true else if r.val=1 then payload
    else if r.val=2 then alive else if r.val=3 then selected else if r.val=4 then remaining
    else if r.val=5 then best else if r.val=6 then bestScore else if r.val=7 then bestDegree
    else if r.val=8 then found else if r.val=9 then List.replicate i true else if r.val=10 then clock
    else if r.val=11 then ns else if r.val=12 then nd else if r.val=13 then eligible
    else if r.val=14 then decision else []

def state {n : ℕ} (G : MatrixData n) (A S R : Vector Bool n) (b : Best n) (i : ℕ)
    (clock ns nd eligible decision : BitString) : Store 32 :=
  rawState n i G.bits (liveBits A) (liveBits S) (liveBits R)
    (List.replicate (index b) true) (List.replicate (selectedScore G S b) true)
    (List.replicate (selectedScore G A b) true) [b.isSome] clock ns nd eligible decision

def scoreEmbedding (alive : Bool) : Fin 23 ↪ Fin 33 where
  toFun i := ![0,1,if alive then 2 else 3,9,15,if alive then 12 else 11,16,17,
    18,19,20,21,22,23,24,25,26,27,28,29,30,31,32] i
  inj' := by cases alive <;> decide +kernel
noncomputable def readScore (alive : Bool) : OracleBlock 32 := UnitRecognitionScore.on (scoreEmbedding alive)

def maskEmbedding : Fin 7 ↪ Fin 33 where
  toFun i := ![4,9,13,15,16,17,18] i
  inj' := by decide +kernel
noncomputable def readEligible : OracleBlock 32 := listLookupOn maskEmbedding

def betterEmbedding : Fin 15 ↪ Fin 33 where
  toFun i := ![11,12,6,7,8,13,14,15,16,17,18,19,20,21,22] i
  inj' := by decide +kernel
noncomputable def readBetter : OracleBlock 32 := UnitRecognitionBetter.on betterEmbedding

lemma readScore_false_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A S R : Vector Bool n) (b : Best n) (i : Fin n) (clock : BitString) :
    ∃t, (readScore false).Executes g (state G A S R b i.val clock [] [] [] [])
      (state G A S R b i.val clock (List.replicate (UnitRecognitionScore.score G S i) true) [] [] []) t ∧
      t≤400*(n+1)^3 := by
  obtain ⟨t,ht,hb⟩ := UnitRecognitionScore.on_executes (scoreEmbedding false) g G S i 0
    (state G A S R b i.val clock [] [] [] [])
    (by funext j;fin_cases j <;> rfl)
  simp only [Nat.zero_add] at ht
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext j;fin_cases j <;> rfl

lemma readScore_true_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A S R : Vector Bool n) (b : Best n) (i : Fin n) (clock ns : BitString) :
    ∃t, (readScore true).Executes g (state G A S R b i.val clock ns [] [] [])
      (state G A S R b i.val clock ns (List.replicate (UnitRecognitionScore.score G A i) true) [] []) t ∧
      t≤400*(n+1)^3 := by
  obtain ⟨t,ht,hb⟩ := UnitRecognitionScore.on_executes (scoreEmbedding true) g G A i 0
    (state G A S R b i.val clock ns [] [] [])
    (by funext j;fin_cases j <;> rfl)
  simp only [Nat.zero_add] at ht
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext j;fin_cases j <;> rfl

lemma readEligible_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A S R : Vector Bool n) (b : Best n) (i : Fin n) (clock ns nd : BitString) :
    ∃t, readEligible.Executes g (state G A S R b i.val clock ns nd [] [])
      (state G A S R b i.val clock ns nd [R[i.val]] []) t ∧ t≤100*(n+1)^2 := by
  obtain ⟨t,ht,hb⟩ := listLookupOn_executes maskEmbedding g
    (state G A S R b i.val clock ns nd [] []) (liveWords R) i.val
    (by funext j;fin_cases j <;> rfl)
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext j;fin_cases j <;> simp [state,rawState,maskEmbedding,liveWords_get]
  · change t≤lookupBound (liveBits R).length i.val at hb
    rw [liveBits_length] at hb
    unfold lookupBound at hb
    have hi := i.isLt
    have hm := Nat.mul_le_mul_left n hi.le
    nlinarith

lemma selectedScore_le {n : ℕ} (G : MatrixData n) (S : Vector Bool n) (b : Best n) : selectedScore G S b≤n := by
  cases b with
  | none => simp [selectedScore]
  | some i => exact UnitRecognitionScore.score_le G S i

lemma readBetter_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A S R : Vector Bool n) (b : Best n) (i : Fin n) (clock : BitString) :
    ∃t, readBetter.Executes g
      (state G A S R b i.val clock (List.replicate (UnitRecognitionScore.score G S i) true)
        (List.replicate (UnitRecognitionScore.score G A i) true) [R[i.val]] [])
      (state G A S R b i.val clock (List.replicate (UnitRecognitionScore.score G S i) true)
        (List.replicate (UnitRecognitionScore.score G A i) true) [R[i.val]] [prefer G A S R b i]) t ∧
      t≤300*(n+1) := by
  obtain ⟨t,ht,hb⟩ := UnitRecognitionBetter.on_executes betterEmbedding g
    (UnitRecognitionScore.score G S i) (UnitRecognitionScore.score G A i)
    (selectedScore G S b) (selectedScore G A b) b.isSome R[i.val]
    (state G A S R b i.val clock (List.replicate (UnitRecognitionScore.score G S i) true)
      (List.replicate (UnitRecognitionScore.score G A i) true) [R[i.val]] [])
    (by funext j;fin_cases j <;> rfl)
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext j;fin_cases j <;> rfl
  · have h1 := UnitRecognitionScore.score_le G S i
    have h2 := UnitRecognitionScore.score_le G A i
    have h3 := selectedScore_le G S b
    have h4 := selectedScore_le G A b
    omega

lemma readScore_queryFree (a : Bool) : (readScore a).QueryFree := UnitRecognitionScore.on_queryFree _
lemma readEligible_queryFree : readEligible.QueryFree := listLookupOn_queryFree _
lemma readBetter_queryFree : readBetter.QueryFree := UnitRecognitionBetter.on_queryFree _

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionChoice
