import HiddenCircuits.GraphReduction.Runtime.DirectedCore

/-! Actual coordinate comparisons used by the directed query predicate. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

noncomputable def dirPrepare : OracleBlock 40 :=
  seq (copyOn 15 19 32 (by decide) (by decide) (by decide))
    (seq (push 19 true) (seq (copyOn 17 20 32 (by decide) (by decide) (by decide)) (push 20 true)))

theorem dirPrepare_executes (g : BitString → ℕ) (x y : VertexRecord) :
    dirPrepare.Executes g (dirStore x y [] [] (fun _ => []) []) (dirState x y 0)
      (5*y.layer+5*y.cut.index+12) := by
  let s1 := dirStore x y (List.replicate y.layer true) [] (fun _ => []) []
  let s2 := dirStore x y (List.replicate (y.layer+1) true) [] (fun _ => []) []
  let s3 := dirStore x y (List.replicate (y.layer+1) true) (List.replicate y.cut.index true) (fun _ => []) []
  have h1 : (copyOn (15 : Fin 41) 19 32 (by decide) (by decide) (by decide)).Executes g
      (dirStore x y [] [] (fun _ => []) []) s1 (5*y.layer+2) := by
    convert copyOn_executes g (15 : Fin 41) 19 32 (by decide) (by decide) (by decide)
      (dirStore x y [] [] (fun _ => []) []) rfl using 1
    · funext i; fin_cases i <;> simp [s1,dirStore,recordFields]
    · simp [dirStore,recordFields]
  have h2 : (push (19 : Fin 41) true).Executes g s1 s2 1 := by
    convert push_executes g (19 : Fin 41) true s1 using 1
    funext i; fin_cases i <;> simp [s1,s2,dirStore,List.replicate_succ]
  have h3 : (copyOn (17 : Fin 41) 20 32 (by decide) (by decide) (by decide)).Executes g s2 s3 (5*y.cut.index+2) := by
    convert copyOn_executes g (17 : Fin 41) 20 32 (by decide) (by decide) (by decide) s2 rfl using 1
    · funext i; fin_cases i <;> simp [s2,s3,dirStore,recordFields]
    · simp [s2,dirStore,recordFields]
  have h4 : (push (20 : Fin 41) true).Executes g s3 (dirState x y 0) 1 := by
    convert push_executes g (20 : Fin 41) true s3 using 1
    funext i; fin_cases i <;> simp [s3,dirStore,dirState,List.replicate_succ]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)) using 1 <;> omega

def dirCompareEmbedding0 : Fin 6 ↪ Fin 41 where
  toFun i := ![6,15,21,32,33,34] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
noncomputable def dirCompare0 : OracleBlock 40 := GraphVerifier.Runtime.readLengthOn dirCompareEmbedding0

theorem dirCompare0_executes (g : BitString → ℕ) (x y : VertexRecord) :
    ∃ c, dirCompare0.Executes g (dirState x y 0) (dirState x y 1) c ∧ c≤26*dirSize x y+23 := by
  obtain ⟨c,hc,hb⟩ := GraphVerifier.Runtime.readLengthOn_executes dirCompareEmbedding0 g (dirState x y 0)
    (List.replicate (x.layer) true) (List.replicate (y.layer) true) (by funext i; fin_cases i <;> rfl)
  simp only [List.length_replicate] at hb
  refine ⟨c,?_,?_⟩
  · convert hc using 1
    funext i; fin_cases i <;> simp only [List.length_replicate] <;> rfl
  · have h := dir_coordinates_bound x y
    omega

def dirCompareEmbedding1 : Fin 6 ↪ Fin 41 where
  toFun i := ![6,19,22,32,33,34] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
noncomputable def dirCompare1 : OracleBlock 40 := GraphVerifier.Runtime.readLengthOn dirCompareEmbedding1

theorem dirCompare1_executes (g : BitString → ℕ) (x y : VertexRecord) :
    ∃ c, dirCompare1.Executes g (dirState x y 1) (dirState x y 2) c ∧ c≤26*dirSize x y+23 := by
  obtain ⟨c,hc,hb⟩ := GraphVerifier.Runtime.readLengthOn_executes dirCompareEmbedding1 g (dirState x y 1)
    (List.replicate (x.layer) true) (List.replicate (y.layer+1) true) (by funext i; fin_cases i <;> rfl)
  simp only [List.length_replicate] at hb
  refine ⟨c,?_,?_⟩
  · convert hc using 1
    funext i; fin_cases i <;> simp only [List.length_replicate] <;> rfl
  · have h := dir_coordinates_bound x y
    omega

def dirCompareEmbedding2 : Fin 6 ↪ Fin 41 where
  toFun i := ![16,7,23,32,33,34] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
noncomputable def dirCompare2 : OracleBlock 40 := readOnlyLTOn dirCompareEmbedding2

theorem dirCompare2_executes (g : BitString → ℕ) (x y : VertexRecord) :
    ∃ c, dirCompare2.Executes g (dirState x y 2) (dirState x y 3) c ∧ c≤26*dirSize x y+23 := by
  obtain ⟨c,hc,hb⟩ := readOnlyLTOn_executes dirCompareEmbedding2 g (dirState x y 2)
    (y.track) (x.track) (by funext i; fin_cases i <;> rfl)
  refine ⟨c,?_,?_⟩
  · convert hc using 1
    funext i; fin_cases i <;> simp only [List.length_replicate] <;> rfl
  · have h := dir_coordinates_bound x y
    omega

def dirCompareEmbedding3 : Fin 6 ↪ Fin 41 where
  toFun i := ![7,17,24,32,33,34] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
noncomputable def dirCompare3 : OracleBlock 40 := GraphVerifier.Runtime.readLengthOn dirCompareEmbedding3

theorem dirCompare3_executes (g : BitString → ℕ) (x y : VertexRecord) :
    ∃ c, dirCompare3.Executes g (dirState x y 3) (dirState x y 4) c ∧ c≤26*dirSize x y+23 := by
  obtain ⟨c,hc,hb⟩ := GraphVerifier.Runtime.readLengthOn_executes dirCompareEmbedding3 g (dirState x y 3)
    (List.replicate (x.track) true) (List.replicate (y.cut.index) true) (by funext i; fin_cases i <;> rfl)
  simp only [List.length_replicate] at hb
  refine ⟨c,?_,?_⟩
  · convert hc using 1
    funext i; fin_cases i <;> simp only [List.length_replicate] <;> rfl
  · have h := dir_coordinates_bound x y
    omega

def dirCompareEmbedding4 : Fin 6 ↪ Fin 41 where
  toFun i := ![7,20,25,32,33,34] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
noncomputable def dirCompare4 : OracleBlock 40 := GraphVerifier.Runtime.readLengthOn dirCompareEmbedding4

theorem dirCompare4_executes (g : BitString → ℕ) (x y : VertexRecord) :
    ∃ c, dirCompare4.Executes g (dirState x y 4) (dirState x y 5) c ∧ c≤26*dirSize x y+23 := by
  obtain ⟨c,hc,hb⟩ := GraphVerifier.Runtime.readLengthOn_executes dirCompareEmbedding4 g (dirState x y 4)
    (List.replicate (x.track) true) (List.replicate (y.cut.index+1) true) (by funext i; fin_cases i <;> rfl)
  simp only [List.length_replicate] at hb
  refine ⟨c,?_,?_⟩
  · convert hc using 1
    funext i; fin_cases i <;> simp only [List.length_replicate] <;> rfl
  · have h := dir_coordinates_bound x y
    omega

def dirCompareEmbedding5 : Fin 6 ↪ Fin 41 where
  toFun i := ![16,17,26,32,33,34] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
noncomputable def dirCompare5 : OracleBlock 40 := GraphVerifier.Runtime.readLengthOn dirCompareEmbedding5

theorem dirCompare5_executes (g : BitString → ℕ) (x y : VertexRecord) :
    ∃ c, dirCompare5.Executes g (dirState x y 5) (dirState x y 6) c ∧ c≤26*dirSize x y+23 := by
  obtain ⟨c,hc,hb⟩ := GraphVerifier.Runtime.readLengthOn_executes dirCompareEmbedding5 g (dirState x y 5)
    (List.replicate (y.track) true) (List.replicate (y.cut.index) true) (by funext i; fin_cases i <;> rfl)
  simp only [List.length_replicate] at hb
  refine ⟨c,?_,?_⟩
  · convert hc using 1
    funext i; fin_cases i <;> simp only [List.length_replicate] <;> rfl
  · have h := dir_coordinates_bound x y
    omega

noncomputable def dirCompare : OracleBlock 40 := seq dirCompare0 (seq dirCompare1 (seq dirCompare2 (seq dirCompare3 (seq dirCompare4 (dirCompare5)))))

theorem dirCompare_executes (g : BitString → ℕ) (x y : VertexRecord) :
    ∃ c, dirCompare.Executes g (dirState x y 0) (dirState x y 6) c ∧ c≤156*dirSize x y+148 := by
  obtain ⟨c0,h0,hb0⟩ := dirCompare0_executes g x y
  obtain ⟨c1,h1,hb1⟩ := dirCompare1_executes g x y
  obtain ⟨c2,h2,hb2⟩ := dirCompare2_executes g x y
  obtain ⟨c3,h3,hb3⟩ := dirCompare3_executes g x y
  obtain ⟨c4,h4,hb4⟩ := dirCompare4_executes g x y
  obtain ⟨c5,h5,hb5⟩ := dirCompare5_executes g x y
  refine ⟨_,seq_executes _ _ g h0 (seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 (h5))))),?_⟩
  omega

lemma dirPrepare_queryFree : dirPrepare.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (push_queryFree _ _)))
lemma dirCompare_queryFree : dirCompare.QueryFree :=
  seq_queryFree _ _ (GraphVerifier.Runtime.readLengthOn_queryFree _) (seq_queryFree _ _ (GraphVerifier.Runtime.readLengthOn_queryFree _) (seq_queryFree _ _ (readOnlyLTOn_queryFree _) (seq_queryFree _ _ (GraphVerifier.Runtime.readLengthOn_queryFree _) (seq_queryFree _ _ (GraphVerifier.Runtime.readLengthOn_queryFree _) ((GraphVerifier.Runtime.readLengthOn_queryFree _))))))

end HiddenCircuits.GraphReduction.Runtime
