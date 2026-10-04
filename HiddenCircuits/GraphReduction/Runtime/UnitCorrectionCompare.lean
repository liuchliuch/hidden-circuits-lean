import HiddenCircuits.GraphReduction.Runtime.UnitCorrectionDefs

namespace HiddenCircuits.GraphReduction.Runtime.UnitCorrection
open Complexity Complexity.OracleBlock
set_option maxRecDepth 2000

noncomputable def prepare : OracleBlock 48 := seq (unarySuccessorOn (successorMap false)) (unarySuccessorOn (successorMap true))
noncomputable def compareAll : OracleBlock 48 := seq (compare 0) (seq (compare 1) (seq (compare 2)
  (seq (compare 3) (seq (compare 4) (seq (compare 5) (seq (compare 6) (compare 7)))))))

theorem prepare_executes (g : BitString → ℕ) (second : Bool) (width : ℕ) (x y : VertexRecord) :
    prepare.Executes g (state second width x y 0 0) (state second width x y 2 0)
      (5*x.track+5*y.cut.index+12) := by
  have h1 : (unarySuccessorOn (successorMap false)).Executes g (state second width x y 0 0)
      (state second width x y 1 0) (5*x.track+5) := by
    convert unarySuccessorOn_executes (successorMap false) g (state second width x y 0 0) x.track
      (by funext i;fin_cases i <;> rfl) using 1
    funext i;fin_cases i <;> rfl
  have h2 : (unarySuccessorOn (successorMap true)).Executes g (state second width x y 1 0)
      (state second width x y 2 0) (5*y.cut.index+5) := by
    convert unarySuccessorOn_executes (successorMap true) g (state second width x y 1 0) y.cut.index
      (by funext i;fin_cases i <;> rfl) using 1
    funext i;fin_cases i <;> rfl
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

theorem compare0_executes (g : BitString → ℕ) (second : Bool) (width : ℕ) (x y : VertexRecord) :
    ∃t,(compare 0).Executes g (state second width x y 2 0) (state second width x y 2 1) t ∧
      t≤100*size width x y+100 := by
  obtain ⟨t,ht,hb⟩ := Complexity.GraphVerifier.Runtime.readLengthOn_executes (compareMap 0) g (state second width x y 2 0) (List.replicate (x.track) true) (List.replicate (x.cut.index) true) (by funext i;fin_cases i <;> rfl)
  try simp only [List.length_replicate] at ht hb
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> rfl
  · unfold size;omega

theorem compare1_executes (g : BitString → ℕ) (second : Bool) (width : ℕ) (x y : VertexRecord) :
    ∃t,(compare 1).Executes g (state second width x y 2 1) (state second width x y 2 2) t ∧
      t≤100*size width x y+100 := by
  obtain ⟨t,ht,hb⟩ := readOnlyLTOn_executes (compareMap 1) g (state second width x y 2 1) (x.track+1) (width) (by funext i;fin_cases i <;> rfl)
  try simp only [List.length_replicate] at ht hb
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> rfl
  · unfold size;omega

theorem compare2_executes (g : BitString → ℕ) (second : Bool) (width : ℕ) (x y : VertexRecord) :
    ∃t,(compare 2).Executes g (state second width x y 2 2) (state second width x y 2 3) t ∧
      t≤100*size width x y+100 := by
  obtain ⟨t,ht,hb⟩ := readOnlyLTOn_executes (compareMap 2) g (state second width x y 2 2) (y.layer) (x.layer) (by funext i;fin_cases i <;> rfl)
  try simp only [List.length_replicate] at ht hb
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> rfl
  · unfold size;omega

theorem compare3_executes (g : BitString → ℕ) (second : Bool) (width : ℕ) (x y : VertexRecord) :
    ∃t,(compare 3).Executes g (state second width x y 2 3) (state second width x y 2 4) t ∧
      t≤100*size width x y+100 := by
  obtain ⟨t,ht,hb⟩ := Complexity.GraphVerifier.Runtime.readLengthOn_executes (compareMap 3) g (state second width x y 2 3) (List.replicate (y.track) true) (List.replicate (0) true) (by funext i;fin_cases i <;> rfl)
  try simp only [List.length_replicate] at ht hb
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> rfl
  · unfold size;omega

theorem compare4_executes (g : BitString → ℕ) (second : Bool) (width : ℕ) (x y : VertexRecord) :
    ∃t,(compare 4).Executes g (state second width x y 2 4) (state second width x y 2 5) t ∧
      t≤100*size width x y+100 := by
  obtain ⟨t,ht,hb⟩ := Complexity.GraphVerifier.Runtime.readLengthOn_executes (compareMap 4) g (state second width x y 2 4) (List.replicate (x.track) true) (List.replicate (y.cut.index) true) (by funext i;fin_cases i <;> rfl)
  try simp only [List.length_replicate] at ht hb
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> rfl
  · unfold size;omega

theorem compare5_executes (g : BitString → ℕ) (second : Bool) (width : ℕ) (x y : VertexRecord) :
    ∃t,(compare 5).Executes g (state second width x y 2 5) (state second width x y 2 6) t ∧
      t≤100*size width x y+100 := by
  obtain ⟨t,ht,hb⟩ := Complexity.GraphVerifier.Runtime.readLengthOn_executes (compareMap 5) g (state second width x y 2 5) (List.replicate (x.track) true) (List.replicate (y.cut.index+1) true) (by funext i;fin_cases i <;> rfl)
  try simp only [List.length_replicate] at ht hb
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> rfl
  · unfold size;omega

theorem compare6_executes (g : BitString → ℕ) (second : Bool) (width : ℕ) (x y : VertexRecord) :
    ∃t,(compare 6).Executes g (state second width x y 2 6) (state second width x y 2 7) t ∧
      t≤100*size width x y+100 := by
  obtain ⟨t,ht,hb⟩ := Complexity.GraphVerifier.Runtime.readLengthOn_executes (compareMap 6) g (state second width x y 2 6) (List.replicate (x.track+1) true) (List.replicate (y.cut.index) true) (by funext i;fin_cases i <;> rfl)
  try simp only [List.length_replicate] at ht hb
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> rfl
  · unfold size;omega

theorem compare7_executes (g : BitString → ℕ) (second : Bool) (width : ℕ) (x y : VertexRecord) :
    ∃t,(compare 7).Executes g (state second width x y 2 7) (state second width x y 2 8) t ∧
      t≤100*size width x y+100 := by
  obtain ⟨t,ht,hb⟩ := Complexity.GraphVerifier.Runtime.readLengthOn_executes (compareMap 7) g (state second width x y 2 7) (List.replicate (x.track+1) true) (List.replicate (y.cut.index+1) true) (by funext i;fin_cases i <;> rfl)
  try simp only [List.length_replicate] at ht hb
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> rfl
  · unfold size;omega

theorem compareAll_executes (g : BitString → ℕ) (second : Bool) (width : ℕ) (x y : VertexRecord) :
    ∃t,compareAll.Executes g (state second width x y 2 0) (state second width x y 2 8) t ∧
      t≤800*size width x y+814 := by
  obtain ⟨t0,h0,b0⟩ := compare0_executes g second width x y
  obtain ⟨t1,h1,b1⟩ := compare1_executes g second width x y
  obtain ⟨t2,h2,b2⟩ := compare2_executes g second width x y
  obtain ⟨t3,h3,b3⟩ := compare3_executes g second width x y
  obtain ⟨t4,h4,b4⟩ := compare4_executes g second width x y
  obtain ⟨t5,h5,b5⟩ := compare5_executes g second width x y
  obtain ⟨t6,h6,b6⟩ := compare6_executes g second width x y
  obtain ⟨t7,h7,b7⟩ := compare7_executes g second width x y
  exact ⟨_,(seq_executes _ _ g h0 (seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 (seq_executes _ _ g h5 (seq_executes _ _ g h6 h7))))))),by omega⟩

lemma prepare_queryFree : prepare.QueryFree := seq_queryFree _ _ (unarySuccessorOn_queryFree _) (unarySuccessorOn_queryFree _)
lemma compare_queryFree (j : Fin 8) : (compare j).QueryFree := by
  unfold compare;split_ifs
  · exact readOnlyLTOn_queryFree _
  · exact Complexity.GraphVerifier.Runtime.readLengthOn_queryFree _
lemma compareAll_queryFree : compareAll.QueryFree :=
  (seq_queryFree _ _ (compare_queryFree 0) (seq_queryFree _ _ (compare_queryFree 1) (seq_queryFree _ _ (compare_queryFree 2) (seq_queryFree _ _ (compare_queryFree 3) (seq_queryFree _ _ (compare_queryFree 4) (seq_queryFree _ _ (compare_queryFree 5) (seq_queryFree _ _ (compare_queryFree 6) (compare_queryFree 7))))))))
end HiddenCircuits.GraphReduction.Runtime.UnitCorrection
