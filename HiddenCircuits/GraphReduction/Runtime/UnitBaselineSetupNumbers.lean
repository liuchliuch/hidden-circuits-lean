import HiddenCircuits.GraphReduction.Runtime.UnitBaselineSetupDefs

namespace HiddenCircuits.GraphReduction.Runtime.UnitBaselineSetup
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine
set_option maxRecDepth 2000


lemma seededFlags_append {k : ℕ} (fs gs : List (Fin (k+1) × Bool)) (s : Store k) :
    seededFlags (fs++gs) s=seededFlags gs (seededFlags fs s) := by
  induction fs generalizing s with
  | nil => rfl
  | cons f fs ih => cases f;exact ih _
lemma seededFlags_reverse_word {k : ℕ} (i : Fin (k+1)) (bs : BitString) (s : Store k) :
    seededFlags (bs.reverse.map (fun b=>(i,b))) s=Function.update s i (bs++s i) := by
  induction bs generalizing s with
  | nil => simp [seededFlags]
  | cons b bs ih =>
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,seededFlags_append,ih,seededFlags]
    simp only [Function.update_self,Function.update_idem,List.cons_append]

def numberStage (width height : ℕ) (x : VertexRecord) (j : ℕ) : Fin 7 → BitString :=
  fun i=>if i.val<j then signedBits (UnitBaseline.init width height x.layer x.track i) else []

 theorem readNumbers_executes (g : BitString → ℕ) (c : QueryContext) (width height : ℕ) (x : VertexRecord) :
    ∃t,readNumbers.Executes g (parsed c width height x)
      (state c width height [] (recordFields x) (numberStage width height x 4) []) t ∧
      t≤UnarySignedRead.bound width+UnarySignedRead.bound height+
        UnarySignedRead.bound x.layer+UnarySignedRead.bound x.track+6 := by
  let s := fun j=>state c width height [] (recordFields x) (numberStage width height x j) []
  obtain ⟨a,ha,hba⟩ := UnarySignedRead.on_executes (readMap 0) g (s 0) width (by funext i;fin_cases i <;> rfl)
  have h1 : (UnarySignedRead.on (readMap 0)).Executes g (s 0) (s 1) a := by
    convert ha using 1;funext i;fin_cases i <;> rfl
  obtain ⟨b,hb,hbb⟩ := UnarySignedRead.on_executes (readMap 1) g (s 1) height (by funext i;fin_cases i <;> rfl)
  have h2 : (UnarySignedRead.on (readMap 1)).Executes g (s 1) (s 2) b := by
    convert hb using 1;funext i;fin_cases i <;> rfl
  obtain ⟨d,hd,hbd⟩ := UnarySignedRead.on_executes (readMap 2) g (s 2) x.layer (by funext i;fin_cases i <;> rfl)
  have h3 : (UnarySignedRead.on (readMap 2)).Executes g (s 2) (s 3) d := by
    convert hd using 1;funext i;fin_cases i <;> rfl
  obtain ⟨e,he,hbe⟩ := UnarySignedRead.on_executes (readMap 3) g (s 3) x.track (by funext i;fin_cases i <;> rfl)
  have h4 : (UnarySignedRead.on (readMap 3)).Executes g (s 3) (s 4) e := by
    convert he using 1;funext i;fin_cases i <;> rfl
  exact ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),by omega⟩

 theorem setup_executes (g : BitString → ℕ) (c : QueryContext) (width height : ℕ) (x : VertexRecord) :
    ∃t,setup.Executes g (parsed c width height x) (ready c width height x) t ∧
      t≤100*(magnitude width height x+1)^2+2000 := by
  let s0:=state c width height [] (recordFields x) (numberStage width height x 4) []
  let s1:=state c width height [] (recordFields x) (numberStage width height x 4) [decide (x.track=x.cut.index)]
  obtain ⟨a,ha,hba⟩ := readNumbers_executes g c width height x
  obtain ⟨b,hb,hbb⟩ := Complexity.GraphVerifier.Runtime.readLengthOn_executes equalMap g s0
    (List.replicate x.track true) (List.replicate x.cut.index true) (by funext i;fin_cases i <;> rfl)
  have h2 : equal.Executes g s0 s1 b := by
    simp only [List.length_replicate] at hb
    convert hb using 1;funext i;fin_cases i <;> rfl
  have h3 : seed.Executes g s1 (ready c width height x) 46 := by
    convert seedFlags_executes constantFlags g s1 using 1
    simp only [constantFlags,seededFlags_append,seededFlags_reverse_word]
    funext i;fin_cases i <;> first | rfl | simp [ready,state,s1,numberStage,UnitBaseline.init,Function.comp_def]
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g h2 h3),?_⟩
  simp only [List.length_replicate] at hbb
  unfold UnarySignedRead.bound at hba
  unfold magnitude
  nlinarith [sq_nonneg (width:ℤ),sq_nonneg (height:ℤ)]

 lemma setup_queryFree : setup.QueryFree :=
  seq_queryFree _ _ (seq_queryFree _ _ (UnarySignedRead.on_queryFree _) (seq_queryFree _ _
    (UnarySignedRead.on_queryFree _) (seq_queryFree _ _ (UnarySignedRead.on_queryFree _) (UnarySignedRead.on_queryFree _))))
    (seq_queryFree _ _ (Complexity.GraphVerifier.Runtime.readLengthOn_queryFree _) (seedFlags_queryFree _))
end HiddenCircuits.GraphReduction.Runtime.UnitBaselineSetup
