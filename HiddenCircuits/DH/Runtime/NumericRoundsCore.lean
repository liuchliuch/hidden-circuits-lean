import HiddenCircuits.DH.Runtime.PairSearch
import HiddenCircuits.DH.Runtime.StorageBounds

/-! Fixed public storage and a literal pair-search stage
for the bounded-round numeric counter. The round clock is a real unary stack. -/
namespace HiddenCircuits.DH.Runtime.NumericRounds
open Complexity OracleBlock PairCheck PruningModel
set_option maxHeartbeats 1600000

def state (n : ℕ) (payload keep removed live sizes table kind clock : BitString) : Store 53 := fun q =>
  if q.val=0 then keep else if q.val=1 then removed else if q.val=2 then live
  else if q.val=3 then sizes else if q.val=4 then table else if q.val=5 then List.replicate n true
  else if q.val=50 then payload else if q.val=51 then kind else if q.val=52 then clock else []

def store {n : ℕ} (G : MatrixData n) (s : NumericStateModel.State n)
    (found : Option (Action n)) (clock : BitString) : Store 53 :=
  state n G.bits (PairSearch.keptBits found) (PairSearch.removedBits found)
    (liveBits s.alive) (NumericEncoding.sizeBits s) (NumericEncoding.tableBits s) (resultBits found) clock

def searchMap : Fin 31 ↪ Fin 54 where
  toFun q := ⟨if q.val=0 then 5 else if q.val=1 then 50 else if q.val=2 then 2
    else if q.val=3 then 0 else if q.val=4 then 1 else if q.val=5 then 51 else q.val,
    by split_ifs <;> omega⟩
  inj' := by
    intro q z h;apply Fin.ext;have hh:=congrArg Fin.val h
    dsimp only at hh
    split_ifs at hh <;> omega

def updateMap : Fin 46 ↪ Fin 54 := ⟨fun q=>⟨q.val,by omega⟩,by intro q z h;exact Fin.ext (congrArg (fun x : Fin 54=>x.val) h)⟩
noncomputable def search : OracleBlock 53 := PairSearch.programOn searchMap
noncomputable def clearIndices : OracleBlock 53 := seq (clear 0) (clear 1)

lemma search_executes (g : BitString→ℕ) {n : ℕ} (G : MatrixData n)
    (s : NumericStateModel.State n) (clock : BitString) :
    ∃t,search.Executes g (store G s none clock) (store G s (PairSearch.find G s.alive) clock) t ∧
      t≤2400*(n+1)^5 := by
  obtain ⟨t,ht,hb⟩:=PairSearch.programOn_executes searchMap g (store G s none clock) G s.alive (by
    funext q;fin_cases q <;> rfl)
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext q;fin_cases q <;> rfl

lemma clearIndices_executes (g : BitString→ℕ) (n : ℕ) (payload live sizes table clock : BitString)
    (keep removed : ℕ) :
    clearIndices.Executes g
      (state n payload (List.replicate keep true) (List.replicate removed true) live sizes table [] clock)
      (state n payload [] [] live sizes table [] clock) (keep+removed+4) := by
  have ha:(clear (0:Fin 54)).Executes g
      (state n payload (List.replicate keep true) (List.replicate removed true) live sizes table [] clock)
      (state n payload [] (List.replicate removed true) live sizes table [] clock) (keep+1):=by
    convert clear_executes g (0:Fin 54)
      (state n payload (List.replicate keep true) (List.replicate removed true) live sizes table [] clock) using 1
    · funext q;fin_cases q <;> rfl
    · simp [state]
  have hb:(clear (1:Fin 54)).Executes g
      (state n payload [] (List.replicate removed true) live sizes table [] clock)
      (state n payload [] [] live sizes table [] clock) (removed+1):=by
    convert clear_executes g (1:Fin 54) (state n payload [] (List.replicate removed true) live sizes table [] clock) using 1
    · funext q;fin_cases q <;> rfl
    · simp [state]
  convert seq_executes _ _ g ha hb using 1 <;> omega

lemma search_queryFree : search.QueryFree := PairSearch.programOn_queryFree _
lemma clearIndices_queryFree : clearIndices.QueryFree := seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)
end HiddenCircuits.DH.Runtime.NumericRounds
