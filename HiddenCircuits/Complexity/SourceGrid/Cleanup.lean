import HiddenCircuits.Complexity.SourceGrid.Ports

/-! Real cleanup of just the generated cell values; grid clocks and all persistent
input/denominator/accumulator words are untouched, however long those clocks are. -/
namespace HiddenCircuits.Complexity.SourceGrid
open OracleBlock

noncomputable def clearGenerated : OracleBlock 42 := seq (clear 12) (seq (clear 13)
  (seq (clear 14) (seq (clear 15) (clear 16))))

def cleared (v : Values) : Values :=
  {v with leftWeight:=[],rightWeight:=[],numeratorWeight:=[],value:=[],temporary:=[]}

theorem clearGenerated_executes (g : BitString → ℕ) (n m i j : ℕ) (inner outer : BitString) (v : Values) :
    clearGenerated.Executes g (store n m i j inner outer v) (store n m i j inner outer (cleared v))
      (v.leftWeight.length+v.rightWeight.length+v.numeratorWeight.length+v.value.length+v.temporary.length+13) := by
  have h₀ : (clear (12 : Fin 43)).Executes g (store n m i j inner outer v)
      (store n m i j inner outer {v with leftWeight:=[]}) (v.leftWeight.length+1) := by
    simpa only [update_leftWeight] using clear_executes g (12 : Fin 43) (store n m i j inner outer v)
  have h₁ : (clear (13 : Fin 43)).Executes g (store n m i j inner outer {v with leftWeight:=[]})
      (store n m i j inner outer {v with leftWeight:=[],rightWeight:=[]}) (v.rightWeight.length+1) := by
    simpa only [update_rightWeight] using clear_executes g (13 : Fin 43) (store n m i j inner outer {v with leftWeight:=[]})
  have h₂ : (clear (14 : Fin 43)).Executes g (store n m i j inner outer {v with leftWeight:=[],rightWeight:=[]})
      (store n m i j inner outer {v with leftWeight:=[],rightWeight:=[],numeratorWeight:=[]}) (v.numeratorWeight.length+1) := by
    simpa only [update_numeratorWeight] using clear_executes g (14 : Fin 43) (store n m i j inner outer {v with leftWeight:=[],rightWeight:=[]})
  have h₃ : (clear (15 : Fin 43)).Executes g
      (store n m i j inner outer {v with leftWeight:=[],rightWeight:=[],numeratorWeight:=[]})
      (store n m i j inner outer {v with leftWeight:=[],rightWeight:=[],numeratorWeight:=[],value:=[]}) (v.value.length+1) := by
    simpa only [update_value] using clear_executes g (15 : Fin 43)
      (store n m i j inner outer {v with leftWeight:=[],rightWeight:=[],numeratorWeight:=[]})
  have h₄ : (clear (16 : Fin 43)).Executes g
      (store n m i j inner outer {v with leftWeight:=[],rightWeight:=[],numeratorWeight:=[],value:=[]})
      (store n m i j inner outer (cleared v)) (v.temporary.length+1) := by
    simpa only [update_temporary] using clear_executes g (16 : Fin 43)
      (store n m i j inner outer {v with leftWeight:=[],rightWeight:=[],numeratorWeight:=[],value:=[]})
  convert seq_executes _ _ g h₀ (seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄))) using 1
  omega

lemma clearGenerated_queryFree : clearGenerated.QueryFree :=
  seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))

end HiddenCircuits.Complexity.SourceGrid
