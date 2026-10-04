import HiddenCircuits.GraphReduction.UnitCoordinateExtractionModel
import HiddenCircuits.GraphReduction.UnitIntervalGraphInput
import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionScalar
import HiddenCircuits.DH.Runtime.PairCheckModel

/-! Fixed ports and physical random access for bounded integer coordinates.
The coordinate array is indexed by original labels, independently of the order. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMachine
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck
open UnitCoordinateExtraction

def words {n : ℕ} (x : Coordinates n) : List BitString :=
  List.ofFn (fun i=>List.replicate (x i) true)
def encoded {n : ℕ} (x : Coordinates n) : BitString := encodeBitList (words x)
lemma words_get {n : ℕ} (x : Coordinates n) (v : Fin n) :
    (words x)[v.val]?.getD []=List.replicate (x v) true := by
  simp [words,List.getElem?_eq_getElem,v.isLt]
lemma words_update {n : ℕ} (x : Coordinates n) (v : Fin n) (a : ℕ) :
    words (Function.update x v a)=(words x).set v.val (List.replicate a true) := by
  apply List.ext_getElem
  · simp [words]
  · intro i h1 h2
    simp only [words,List.getElem_ofFn,List.getElem_set]
    by_cases hi : i=v.val
    · subst i;simp
    · have hne : (⟨i,by simpa [words] using h1⟩ : Fin n)≠v := by intro h;exact hi (congrArg Fin.val h)
      simp [Function.update_apply,hi,Ne.symm hi,hne]
lemma encoded_length {n : ℕ} (x : Coordinates n) (B : ℕ) (hx : ∀i,x i≤B) :
    (encoded x).length≤n*(2*B+2) := by
  have h := UnitIntervalGraphInput.encode_list_bound (words x) B (by
    intro w hw;obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    simpa using hx i)
  simpa [encoded,words] using h

structure Frame where
  n : ℕ
  D : ℕ
  payload : BitString
  order : BitString
  outer : BitString
  inner : BitString
  clock : BitString
  out : BitString

def state (f : Frame) (values : BitString) (u v : ℕ) (a b edge : BitString) : Store 22 := fun i=>
  if i.val=0 then List.replicate f.n true else if i.val=1 then f.payload
  else if i.val=2 then f.order else if i.val=3 then values
  else if i.val=4 then List.replicate f.D true else if i.val=5 then List.replicate u true
  else if i.val=6 then List.replicate v true else if i.val=7 then a else if i.val=8 then b
  else if i.val=9 then edge else if i.val=10 then f.outer else if i.val=11 then f.inner
  else if i.val=12 then f.clock else if i.val=13 then f.out else []

def readEmbedding (first : Bool) : Fin 8 ↪ Fin 23 where
  toFun i := ![3,if first then 5 else 6,if first then 7 else 8,18,19,20,21,22] i
  inj' := by cases first <;> decide +kernel
noncomputable def readValue (first : Bool) : OracleBlock 22 := DH.Runtime.WordArray.readOn (readEmbedding first)
noncomputable def writeValue (first : Bool) : OracleBlock 22 := DH.Runtime.WordArray.updateOn (readEmbedding first)

def edgeEmbedding : Fin 9 ↪ Fin 23 where
  toFun i := ![0,5,6,1,9,18,19,20,21] i
  inj' := by decide +kernel
noncomputable def readEdge : OracleBlock 22 := GraphVerifier.Runtime.matrixLookupOn edgeEmbedding

def scalarEmbedding : Fin 8 ↪ Fin 23 where
  toFun i := ![4,7,8,9,14,15,16,17] i
  inj' := by decide +kernel
noncomputable def arithmetic : OracleBlock 22 := rename UnitCoordinateExtractionScalar.program scalarEmbedding

lemma readFirst_executes (g : BitString → ℕ) {n : ℕ} (f : Frame) (x : Coordinates n)
    (u v : Fin n) (b edge : BitString) :
    ∃t,(readValue true).Executes g (state f (encoded x) u.val v.val [] b edge)
      (state f (encoded x) u.val v.val (List.replicate (x u) true) b edge) t ∧
      t≤lookupBound (encoded x).length u.val := by
  obtain ⟨t,ht,hb⟩ := DH.Runtime.WordArray.readOn_executes (readEmbedding true) g
    (state f (encoded x) u.val v.val [] b edge) (words x) u.val
    (by funext i;fin_cases i <;> rfl)
  rw [words_get] at ht
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext i;fin_cases i <;> rfl

lemma readSecond_executes (g : BitString → ℕ) {n : ℕ} (f : Frame) (x : Coordinates n)
    (u v : Fin n) (a edge : BitString) :
    ∃t,(readValue false).Executes g (state f (encoded x) u.val v.val a [] edge)
      (state f (encoded x) u.val v.val a (List.replicate (x v) true) edge) t ∧
      t≤lookupBound (encoded x).length v.val := by
  obtain ⟨t,ht,hb⟩ := DH.Runtime.WordArray.readOn_executes (readEmbedding false) g
    (state f (encoded x) u.val v.val a [] edge) (words x) v.val
    (by funext i;fin_cases i <;> rfl)
  rw [words_get] at ht
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext i;fin_cases i <;> rfl

lemma writeFirst_executes (g : BitString → ℕ) {n : ℕ} (f : Frame) (x : Coordinates n)
    (u v : Fin n) (a : ℕ) (b edge : BitString) :
    ∃t,(writeValue true).Executes g (state f (encoded x) u.val v.val (List.replicate a true) b edge)
      (state f (encoded (Function.update x u a)) u.val v.val (List.replicate a true) b edge) t ∧
      t≤DH.Runtime.WordArray.updateBound (encoded x).length u.val a := by
  obtain ⟨t,ht,hb⟩ := DH.Runtime.WordArray.updateOn_executes (readEmbedding true) g
    (state f (encoded x) u.val v.val (List.replicate a true) b edge) (words x) u.val (List.replicate a true)
    (by funext i;fin_cases i <;> rfl)
  rw [←words_update] at ht
  refine ⟨t,?_,by simpa only [List.length_replicate] using hb⟩
  convert ht using 1
  funext i;fin_cases i <;> rfl

lemma writeSecond_executes (g : BitString → ℕ) {n : ℕ} (f : Frame) (x : Coordinates n)
    (u v : Fin n) (a : BitString) (b : ℕ) (edge : BitString) :
    ∃t,(writeValue false).Executes g (state f (encoded x) u.val v.val a (List.replicate b true) edge)
      (state f (encoded (Function.update x v b)) u.val v.val a (List.replicate b true) edge) t ∧
      t≤DH.Runtime.WordArray.updateBound (encoded x).length v.val b := by
  obtain ⟨t,ht,hb⟩ := DH.Runtime.WordArray.updateOn_executes (readEmbedding false) g
    (state f (encoded x) u.val v.val a (List.replicate b true) edge) (words x) v.val (List.replicate b true)
    (by funext i;fin_cases i <;> rfl)
  rw [←words_update] at ht
  refine ⟨t,?_,by simpa only [List.length_replicate] using hb⟩
  convert ht using 1
  funext i;fin_cases i <;> rfl

lemma readEdge_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (f : Frame) (hn : f.n=n) (hp : f.payload=G.bits) (values : BitString)
    (u v : Fin n) (a b : BitString) :
    ∃t,readEdge.Executes g (state f values u.val v.val a b [])
      (state f values u.val v.val a b [G.edge u v]) t ∧t≤110*(n+1)^2 := by
  have ht := GraphVerifier.Runtime.matrixLookupOn_executes edgeEmbedding g
    (state f values u.val v.val a b []) n u.val v.val G.bits
    (by funext i;fin_cases i <;> simp [state,edgeEmbedding,hn,hp,GraphVerifier.Runtime.matrixStore])
  rw [matrix_bit] at ht
  refine ⟨GraphVerifier.Runtime.matrixLookupCost n u.val v.val G.bits,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> rfl
  · have h := GraphVerifier.Runtime.matrixLookupCost_in_range n u.val v.val G.bits u.isLt v.isLt
    nlinarith

lemma arithmetic_executes (g : BitString → ℕ) (f : Frame) (values : BitString)
    (u v a b : ℕ) (edge : Bool) :
    ∃t,arithmetic.Executes g (state f values u v (List.replicate a true) (List.replicate b true) [edge])
      (state f values u v (List.replicate (UnitCoordinateExtractionScalar.left f.D a b edge) true)
        (List.replicate (UnitCoordinateExtractionScalar.right f.D a b edge) true) []) t ∧
      t≤102*(f.D+a+b+1) := by
  obtain ⟨t,ht,hb⟩ := UnitCoordinateExtractionScalar.program_executes g f.D a b edge
  refine ⟨t,?_,hb⟩
  apply rename_executes_to _ scalarEmbedding g ht
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim

lemma readValue_queryFree (first : Bool) : (readValue first).QueryFree := DH.Runtime.WordArray.readOn_queryFree _
lemma writeValue_queryFree (first : Bool) : (writeValue first).QueryFree := DH.Runtime.WordArray.updateOn_queryFree _
lemma readEdge_queryFree : readEdge.QueryFree := GraphVerifier.Runtime.matrixLookupOn_queryFree _
lemma arithmetic_queryFree : arithmetic.QueryFree := rename_queryFree _ _ UnitCoordinateExtractionScalar.program_queryFree

end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMachine
