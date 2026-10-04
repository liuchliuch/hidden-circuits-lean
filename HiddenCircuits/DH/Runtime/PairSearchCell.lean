import HiddenCircuits.DH.Runtime.PairCheck
import HiddenCircuits.DH.Runtime.PairSearchModel

/-! Literal first-success candidate processing for the exhaustive pair search. -/
namespace HiddenCircuits.DH.Runtime.PairSearch
open Complexity Complexity.OracleBlock PairCheck

/-- Public ports 0–5 are preserved n/matrix/marks and the three outputs.
Counters use 6/7 and clocks 28/29; ports 8–27 and 30 are scratch. -/
def rawState (n u v : ℕ) (payload marks keep removed kind outerClock innerClock : BitString) : Store 30 := fun i =>
  if i.val=0 then List.replicate n true else if i.val=1 then payload else if i.val=2 then marks else
  if i.val=3 then keep else if i.val=4 then removed else if i.val=5 then kind else
  if i.val=6 then List.replicate u true else if i.val=7 then List.replicate v true else
  if i.val=28 then outerClock else if i.val=29 then innerClock else []

def state {n : ℕ} (payload marks : BitString) (found : Option (PruningModel.Action n))
    (u v : ℕ) (outerClock innerClock : BitString) : Store 30 :=
  rawState n u v payload marks (keptBits found) (removedBits found) (resultBits found) outerClock innerClock

def pairEmbedding : Fin 26 ↪ Fin 31 where
  toFun i := ⟨if i.val<3 then i.val else if i.val=3 then 6 else if i.val=4 then 7 else
    if i.val=5 then 5 else i.val+2,by split_ifs <;> omega⟩
  inj' := by
    intro i j h;apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp only at hv
    split_ifs at hv <;> omega

noncomputable def check : OracleBlock 30 := PairCheck.programOn pairEmbedding
noncomputable def save (b : Bool) : OracleBlock 30 := seq (push 5 b)
  (seq (copyOn 6 3 30 (by decide) (by decide) (by decide))
    (copyOn 7 4 30 (by decide) (by decide) (by decide)))
noncomputable def saveFound : OracleBlock 30 := branchPop 5 skip (save false) (save true)
noncomputable def fresh : OracleBlock 30 := seq check saveFound
noncomputable def candidate : OracleBlock 30 := branchPop 5 fresh (push 5 false) (push 5 true)
noncomputable def body : OracleBlock 30 := seq candidate (push 7 true)

lemma restore_head {k : ℕ} (g : BitString → ℕ) (s : Store k) (port : Fin (k+1))
    (b : Bool) (rest : BitString) (hs : s port=b::rest) :
    (push port b).Executes g (Function.update s port rest) s 1 := by
  convert push_executes g port b (Function.update s port rest) using 1
  funext i
  by_cases hi : i=port
  · subst i;simp [hs]
  · simp [hi]

lemma save_executes (g : BitString → ℕ) (n u v : ℕ) (payload marks rest outerClock innerClock : BitString) (b : Bool) :
    (save b).Executes g (rawState n u v payload marks [] [] rest outerClock innerClock)
      (rawState n u v payload marks (List.replicate u true) (List.replicate v true) (b::rest) outerClock innerClock)
      (5*u+5*v+9) := by
  have h1 : (push (5 : Fin 31) b).Executes g (rawState n u v payload marks [] [] rest outerClock innerClock)
      (rawState n u v payload marks [] [] (b::rest) outerClock innerClock) 1 := by
    convert push_executes g (5 : Fin 31) b (rawState n u v payload marks [] [] rest outerClock innerClock) using 1
    funext i;fin_cases i <;> simp [rawState]
  have h2 : (copyOn (6 : Fin 31) 3 30 (by decide) (by decide) (by decide)).Executes g
      (rawState n u v payload marks [] [] (b::rest) outerClock innerClock)
      (rawState n u v payload marks (List.replicate u true) [] (b::rest) outerClock innerClock) (5*u+2) := by
    convert copyOn_executes g (6 : Fin 31) 3 30 (by decide) (by decide) (by decide)
      (rawState n u v payload marks [] [] (b::rest) outerClock innerClock) rfl using 1
    · funext i;fin_cases i <;> simp [rawState]
    · simp [rawState]
  have h3 : (copyOn (7 : Fin 31) 4 30 (by decide) (by decide) (by decide)).Executes g
      (rawState n u v payload marks (List.replicate u true) [] (b::rest) outerClock innerClock)
      (rawState n u v payload marks (List.replicate u true) (List.replicate v true) (b::rest) outerClock innerClock)
      (5*v+2) := by
    convert copyOn_executes g (7 : Fin 31) 4 30 (by decide) (by decide) (by decide)
      (rawState n u v payload marks (List.replicate u true) [] (b::rest) outerClock innerClock) rfl using 1
    · funext i;fin_cases i <;> simp [rawState]
    · simp [rawState]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1 <;> omega

lemma pop_kind (n u v : ℕ) (payload marks keep removed rest outerClock innerClock : BitString) (b : Bool) :
    Function.update (rawState n u v payload marks keep removed (b::rest) outerClock innerClock) 5 rest=
      rawState n u v payload marks keep removed rest outerClock innerClock := by
  funext i;fin_cases i <;> rfl

lemma saveFound_some (g : BitString → ℕ) {n : ℕ} (payload marks outerClock innerClock : BitString)
    (a : PruningModel.Action n) :
    saveFound.Executes g
      (rawState n a.keep.val a.removed.val payload marks [] [] (kindBits a.kind) outerClock innerClock)
      (state (n:=n) payload marks (some a) a.keep.val a.removed.val outerClock innerClock)
      (5*a.keep.val+5*a.removed.val+11) := by
  cases a with | mk u v kind =>
    cases kind with
    | pendant =>
      convert branchPop_false 5 skip (save false) (save true) g rfl
        (s:=rawState n u.val v.val payload marks [] [] [false] outerClock innerClock)
        (by rw [pop_kind];exact save_executes g n u.val v.val payload marks [] outerClock innerClock false) using 1 <;> omega
    | twin b =>
      convert branchPop_true 5 skip (save false) (save true) g rfl
        (s:=rawState n u.val v.val payload marks [] [] [true,b] outerClock innerClock)
        (by rw [pop_kind];exact save_executes g n u.val v.val payload marks [b] outerClock innerClock true) using 1 <;> omega

lemma candidate_found (g : BitString → ℕ) {n : ℕ} (payload marks outerClock innerClock : BitString)
    (a : PruningModel.Action n) (u v : ℕ) :
    candidate.Executes g (state (n:=n) payload marks (some a) u v outerClock innerClock)
      (state (n:=n) payload marks (some a) u v outerClock innerClock) 3 := by
  cases a with | mk keep removed kind =>
    cases kind with
    | pendant =>
      exact branchPop_false 5 fresh (push 5 false) (push 5 true) g rfl
        (restore_head g _ 5 false [] rfl)
    | twin b =>
      exact branchPop_true 5 fresh (push 5 false) (push 5 true) g rfl
        (restore_head g _ 5 true [b] rfl)


lemma rawResult_eq (G : MatrixData n) (alive : Vector Bool n) (u v : Fin n) :
    PairCheck.rawResult G alive u v=resultBits (tryPair G alive u v) := by
  cases hp : test false G alive u v <;> cases ht : test true G alive u v <;>
    simp [PairCheck.rawResult,chooseBits,tryPair,resultBits,kindBits,hp,ht]

lemma tryPair_coordinates (G : MatrixData n) (alive : Vector Bool n) (u v : Fin n)
    {a : PruningModel.Action n} (ha : tryPair G alive u v=some a) : a.keep=u ∧ a.removed=v := by
  unfold tryPair at ha
  split at ha
  · cases ha;exact ⟨rfl,rfl⟩
  · split at ha
    · cases ha;exact ⟨rfl,rfl⟩
    · contradiction

lemma check_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (alive : Vector Bool n)
    (u v : Fin n) (outerClock innerClock : BitString) :
    ∃c, check.Executes g (state (n:=n) G.bits (liveBits alive) none u.val v.val outerClock innerClock)
      (rawState n u.val v.val G.bits (liveBits alive) [] [] (resultBits (tryPair G alive u v)) outerClock innerClock) c ∧
      c≤2200*(n+1)^3 := by
  obtain ⟨c,hc,hb⟩ := PairCheck.programOn_executes pairEmbedding g
    (state (n:=n) G.bits (liveBits alive) none u.val v.val outerClock innerClock) G alive u v
    (by funext i;fin_cases i <;> rfl)
  refine ⟨c,?_,hb⟩
  convert hc using 1
  funext i;fin_cases i <;> simp [state,rawState,keptBits,removedBits,resultBits,pairEmbedding,rawResult_eq]

def candidateBudget (n : ℕ) : ℕ := 2200*(n+1)^3+10*n+20

def bodyBudget (n : ℕ) : ℕ := candidateBudget n+3

lemma candidate_none (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (alive : Vector Bool n)
    (u v : Fin n) (outerClock innerClock : BitString) :
    ∃c, candidate.Executes g (state (n:=n) G.bits (liveBits alive) none u.val v.val outerClock innerClock)
      (state (n:=n) G.bits (liveBits alive) (tryPair G alive u v) u.val v.val outerClock innerClock) c ∧
      c≤candidateBudget n := by
  obtain ⟨c,hc,hb⟩ := check_executes g G alive u v outerClock innerClock
  cases ha : tryPair G alive u v with
  | none =>
    have hc' : check.Executes g (state (n:=n) G.bits (liveBits alive) none u.val v.val outerClock innerClock)
        (state (n:=n) G.bits (liveBits alive) none u.val v.val outerClock innerClock) c := by
      simpa only [ha,resultBits,Option.map_none,Option.getD_none] using hc
    have hsave : saveFound.Executes g (state (n:=n) G.bits (liveBits alive) none u.val v.val outerClock innerClock)
        (state (n:=n) G.bits (liveBits alive) none u.val v.val outerClock innerClock) 3 :=
      branchPop_empty 5 skip (save false) (save true) g rfl
        (skip_executes g (state (n:=n) G.bits (liveBits alive) none u.val v.val outerClock innerClock))
    refine ⟨(c+3+2)+2,?_,?_⟩
    · exact branchPop_empty 5 fresh (push 5 false) (push 5 true) g rfl (seq_executes _ _ g hc' hsave)
    · unfold candidateBudget;omega
  | some a =>
    obtain ⟨hkeep,hremoved⟩ := tryPair_coordinates G alive u v ha
    have hsave := saveFound_some g G.bits (liveBits alive) outerClock innerClock a
    rw [hkeep,hremoved] at hsave
    have hc' : check.Executes g (state (n:=n) G.bits (liveBits alive) none u.val v.val outerClock innerClock)
        (rawState n u.val v.val G.bits (liveBits alive) [] [] (kindBits a.kind) outerClock innerClock) c := by
      simpa only [ha,resultBits,Option.map_some,Option.getD_some] using hc
    refine ⟨(c+(5*u.val+5*v.val+11)+2)+2,?_,?_⟩
    · exact branchPop_empty 5 fresh (push 5 false) (push 5 true) g rfl (seq_executes _ _ g hc' hsave)
    · unfold candidateBudget;omega

lemma body_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (alive : Vector Bool n)
    (u v : Fin n) (found : Option (PruningModel.Action n)) (outerClock innerClock : BitString) :
    ∃c, body.Executes g (state (n:=n) G.bits (liveBits alive) found u.val v.val outerClock innerClock)
      (state (n:=n) G.bits (liveBits alive) (step G alive u v found) u.val (v.val+1) outerClock innerClock) c ∧
      c≤bodyBudget n := by
  have hcand : ∃c, candidate.Executes g (state (n:=n) G.bits (liveBits alive) found u.val v.val outerClock innerClock)
      (state (n:=n) G.bits (liveBits alive) (step G alive u v found) u.val v.val outerClock innerClock) c ∧
      c≤candidateBudget n := by
    cases found with
    | none => simpa only [step,Option.orElse_none] using candidate_none g G alive u v outerClock innerClock
    | some a => exact ⟨3,candidate_found g G.bits (liveBits alive) outerClock innerClock a u.val v.val,by unfold candidateBudget;omega⟩
  obtain ⟨c,hc,hb⟩ := hcand
  have hpush : (push (7 : Fin 31) true).Executes g
      (state (n:=n) G.bits (liveBits alive) (step G alive u v found) u.val v.val outerClock innerClock)
      (state (n:=n) G.bits (liveBits alive) (step G alive u v found) u.val (v.val+1) outerClock innerClock) 1 := by
    convert push_executes g (7 : Fin 31) true
      (state (n:=n) G.bits (liveBits alive) (step G alive u v found) u.val v.val outerClock innerClock) using 1
    funext i;fin_cases i <;> simp [state,rawState,List.replicate_succ]
  exact ⟨c+1+2,seq_executes _ _ g hc hpush,by unfold bodyBudget;omega⟩

lemma check_queryFree : check.QueryFree := PairCheck.programOn_queryFree _
lemma save_queryFree (b : Bool) : (save b).QueryFree := seq_queryFree _ _ (push_queryFree _ _)
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _))
lemma saveFound_queryFree : saveFound.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree (save_queryFree _) (save_queryFree _)
lemma fresh_queryFree : fresh.QueryFree := seq_queryFree _ _ check_queryFree saveFound_queryFree
lemma candidate_queryFree : candidate.QueryFree := branchPop_queryFree _ _ _ _ fresh_queryFree (push_queryFree _ _) (push_queryFree _ _)
lemma body_queryFree : body.QueryFree := seq_queryFree _ _ candidate_queryFree (push_queryFree _ _)

end HiddenCircuits.DH.Runtime.PairSearch
