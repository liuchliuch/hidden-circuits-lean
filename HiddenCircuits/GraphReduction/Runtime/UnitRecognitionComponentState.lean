import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionChoiceLoop
import HiddenCircuits.Complexity.PairSerialization

/-! Fixed-universe component-scan data and actual array/list update ports. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

structure Data (n : ℕ) where
  order : List (Fin n)
  selected : Vector Bool n
  remaining : Vector Bool n

def advance {n : ℕ} (s : Data n) (v : Fin n) : Data n :=
  ⟨s.order++[v],s.selected.set v.val true,s.remaining.set v.val false⟩

def step {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (s : Data n) : Data n :=
  match UnitRecognitionChoice.choose G A s.selected s.remaining with
  | none => s
  | some v => if UnitRecognitionScore.score G s.selected v=0 then s else advance s v

def run {n : ℕ} (G : MatrixData n) (A : Vector Bool n) : ℕ → Data n → Data n
  | 0,s => s
  | m+1,s => run G A m (step G A s)

def orderBits {n : ℕ} (ls : List (Fin n)) : BitString :=
  encodeBitList (ls.reverse.map (fun v => List.replicate v.val true))

lemma orderBits_append {n : ℕ} (ls : List (Fin n)) (v : Fin n) :
    orderBits (ls++[v]) = true::pairBits (List.replicate v.val true) (orderBits ls) := by
  simp [orderBits,List.reverse_append,encodeBitList]

lemma liveBits_set {n : ℕ} (A : Vector Bool n) (v : Fin n) (b : Bool) :
    liveBits (A.set v.val b)=encodeBitList ((liveWords A).set v.val [b]) := by
  simp [liveBits,liveWords,Vector.toList_set,List.map_set]

/-- The candidate-selection region uses 33 stacks. The reversed label array,
component clock, update singleton and copied label occupy four extra stacks. -/
def store {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (s : Data n)
    (clock winner score degree found value copied : BitString) : Store 36 := fun r =>
  if h:r.val<33 then UnitRecognitionChoice.rawState n 0 G.bits (liveBits A) (liveBits s.selected)
    (liveBits s.remaining) winner score degree found [] [] [] [] [] ⟨r.val,h⟩
  else if r.val=33 then orderBits s.order else if r.val=34 then clock
  else if r.val=35 then value else copied

def choiceEmbedding : Fin 33 ↪ Fin 37 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 37 => z.val) h)

noncomputable def choose : OracleBlock 36 := UnitRecognitionChoice.on choiceEmbedding

theorem choose_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (s : Data n) (clock : BitString) :
    ∃t, choose.Executes g (store G A s clock [] [] [] [false] [] [])
      (store G A s clock
        (List.replicate (UnitRecognitionChoice.index (UnitRecognitionChoice.choose G A s.selected s.remaining)) true)
        (List.replicate (UnitRecognitionChoice.selectedScore G s.selected (UnitRecognitionChoice.choose G A s.selected s.remaining)) true)
        (List.replicate (UnitRecognitionChoice.selectedScore G A (UnitRecognitionChoice.choose G A s.selected s.remaining)) true)
        [(UnitRecognitionChoice.choose G A s.selected s.remaining).isSome] [] []) t ∧ t≤1600*(n+1)^4 := by
  apply UnitRecognitionChoice.on_executes choiceEmbedding g G A s.selected s.remaining
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have hg : ¬i.val<33 := by
      intro h;exact hi ⟨i.val,h⟩ (Fin.ext rfl)
    simp [store,hg]

lemma choose_queryFree : choose.QueryFree := UnitRecognitionChoice.on_queryFree _

def updateEmbedding (selected : Bool) : Fin 8 ↪ Fin 37 where
  toFun i := ![if selected then 3 else 4,5,35,15,16,17,18,19] i
  inj' := by cases selected <;> decide +kernel
noncomputable def updateMask (selected : Bool) : OracleBlock 36 := DH.Runtime.WordArray.updateOn (updateEmbedding selected)

def pairEmbedding : Fin 3 ↪ Fin 37 where
  toFun i := ![33,36,15] i
  inj' := by decide +kernel
noncomputable def emitLabel : OracleBlock 36 := seq
  (copyOn 5 36 15 (by decide) (by decide) (by decide))
  (seq (PairSerialization.on pairEmbedding) (push 33 true))

lemma emitLabel_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (s : Data n) (v : Fin n)
    (clock score degree found value : BitString) :
    emitLabel.Executes g (store G A s clock (List.replicate v.val true) score degree found value [])
      (store G A ⟨s.order++[v],s.selected,s.remaining⟩ clock
        (List.replicate v.val true) score degree found value []) (15*v.val+16) := by
  have h1 : (copyOn (5 : Fin 37) 36 15 (by decide) (by decide) (by decide)).Executes g
      (store G A s clock (List.replicate v.val true) score degree found value [])
      (store G A s clock (List.replicate v.val true) score degree found value (List.replicate v.val true)) (5*v.val+2) := by
    convert copyOn_executes g (5 : Fin 37) 36 15 (by decide) (by decide) (by decide)
      (store G A s clock (List.replicate v.val true) score degree found value []) rfl using 1
    · funext i;fin_cases i <;> simp [store,UnitRecognitionChoice.rawState]
    · simp [store,UnitRecognitionChoice.rawState]
  have h2 := PairSerialization.on_executes pairEmbedding g
    (store G A s clock (List.replicate v.val true) score degree found value (List.replicate v.val true))
    (List.replicate v.val true) (orderBits s.order) (by funext i;fin_cases i <;> rfl)
  have h3 := push_executes g (33 : Fin 37) true
    (Function.update (Function.update
      (store G A s clock (List.replicate v.val true) score degree found value (List.replicate v.val true))
      (pairEmbedding 1) []) (pairEmbedding 0) (pairBits (List.replicate v.val true) (orderBits s.order)))
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1
  · funext i;fin_cases i <;> simp [store,UnitRecognitionChoice.rawState,pairEmbedding,orderBits_append]
  · simp only [List.length_replicate];omega

lemma emitLabel_queryFree : emitLabel.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (PairSerialization.on_queryFree _) (push_queryFree _ _))

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
