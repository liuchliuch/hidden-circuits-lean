import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMax

/-! Literal bounded-grid pair arithmetic. Unary integers are polynomially
bounded; all addition, subtraction and maximum operations are physical copies,
pops and finite loops. The Boolean edge bit is consumed. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionScalar
open Complexity Complexity.OracleBlock

def state (D a b c d : ℕ) (edge flag : BitString) : Store 7 := fun i=>
  if i.val=0 then List.replicate D true else if i.val=1 then List.replicate a true
  else if i.val=2 then List.replicate b true else if i.val=3 then edge
  else if i.val=4 then List.replicate c true else if i.val=5 then List.replicate d true
  else if i.val=6 then flag else []

def maxEmbedding (first : Bool) : Fin 5 ↪ Fin 8 where
  toFun i := ![if first then 1 else 2,4,5,6,7] i
  inj' := by cases first <;> decide +kernel
noncomputable def takeMax (first : Bool) : OracleBlock 7 := UnitCoordinateExtractionMax.on (maxEmbedding first)

def subEmbedding : Fin 3 ↪ Fin 8 where
  toFun i := ![4,5,6] i
  inj' := by decide +kernel
noncomputable def subtract : OracleBlock 7 := seq (CNFCloneEmitter.UnarySplit.on subEmbedding) (clear 6)

lemma takeMax_false_executes (g : BitString → ℕ) (D a b c : ℕ) :
    ∃t,(takeMax false).Executes g (state D a b c 0 [] [])
      (state D a (max b c) 0 0 [] []) t ∧t≤20*(b+c+1) := by
  apply UnitCoordinateExtractionMax.on_executes (maxEmbedding false) g _ _ b c
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim

lemma takeMax_true_executes (g : BitString → ℕ) (D a b c : ℕ) :
    ∃t,(takeMax true).Executes g (state D a b c 0 [] [])
      (state D (max a c) b 0 0 [] []) t ∧t≤20*(a+c+1) := by
  apply UnitCoordinateExtractionMax.on_executes (maxEmbedding true) g _ _ a c
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim

lemma subtract_executes (g : BitString → ℕ) (D a b c d : ℕ) :
    ∃t,subtract.Executes g (state D a b c d [] [])
      (state D a b (c-d) 0 [] []) t ∧t≤9*d+8 := by
  obtain ⟨t,ht,hb⟩ := CNFCloneEmitter.UnarySplit.on_executes subEmbedding g
    (state D a b c d [] []) c d (by funext i;fin_cases i <;> rfl)
  have he : Function.update (Function.update (Function.update (state D a b c d [] [])
      (subEmbedding 0) (List.replicate (c-d) true)) (subEmbedding 1) [])
      (subEmbedding 2) [decide (c<d)] = state D a b (c-d) 0 [] [decide (c<d)] := by
    funext i;fin_cases i <;> rfl
  rw [he] at ht
  have hc : (clear (6 : Fin 8)).Executes g (state D a b (c-d) 0 [] [decide (c<d)])
      (state D a b (c-d) 0 [] []) 2 := by
    convert clear_executes g (6 : Fin 8) _ using 1
    funext i;fin_cases i <;> rfl
  exact ⟨_,seq_executes _ _ g ht hc,by omega⟩

noncomputable def edgeProgram : OracleBlock 7 :=
  seq (copyOn 1 4 7 (by decide) (by decide) (by decide)) (seq (takeMax false)
    (seq (copyOn 2 4 7 (by decide) (by decide) (by decide))
      (seq (copyOn 0 5 7 (by decide) (by decide) (by decide)) (seq subtract (takeMax true)))))
noncomputable def nonedgeProgram : OracleBlock 7 :=
  seq (copyOn 1 4 7 (by decide) (by decide) (by decide))
    (seq (copyOn 0 4 7 (by decide) (by decide) (by decide)) (seq (push 4 true) (takeMax false)))
noncomputable def program : OracleBlock 7 := branchPop 3 skip nonedgeProgram edgeProgram

lemma edgeProgram_executes (g : BitString → ℕ) (D a b : ℕ) :
    ∃t,edgeProgram.Executes g (state D a b 0 0 [] [])
      (state D (max a (b-D)) (max b a) 0 0 [] []) t ∧ t≤100*(D+a+b+1) := by
  have h1 : (copyOn (1 : Fin 8) 4 7 (by decide) (by decide) (by decide)).Executes g
      (state D a b 0 0 [] []) (state D a b a 0 [] []) (5*a+2) := by
    convert copyOn_executes g (1 : Fin 8) 4 7 (by decide) (by decide) (by decide) (state D a b 0 0 [] []) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  obtain ⟨c2,h2,b2⟩ := takeMax_false_executes g D a b a
  have h3 : (copyOn (2 : Fin 8) 4 7 (by decide) (by decide) (by decide)).Executes g
      (state D a (max b a) 0 0 [] []) (state D a (max b a) (max b a) 0 [] []) (5*max b a+2) := by
    convert copyOn_executes g (2 : Fin 8) 4 7 (by decide) (by decide) (by decide)
      (state D a (max b a) 0 0 [] []) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h4 : (copyOn (0 : Fin 8) 5 7 (by decide) (by decide) (by decide)).Executes g
      (state D a (max b a) (max b a) 0 [] []) (state D a (max b a) (max b a) D [] []) (5*D+2) := by
    convert copyOn_executes g (0 : Fin 8) 5 7 (by decide) (by decide) (by decide)
      (state D a (max b a) (max b a) 0 [] []) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  obtain ⟨c5,h5,b5⟩ := subtract_executes g D a (max b a) (max b a) D
  obtain ⟨c6,h6,b6⟩ := takeMax_true_executes g D a (max b a) (max b a-D)
  have he : max a (max b a-D)=max a (b-D) := by omega
  rw [he] at h6
  exact ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6)))),by omega⟩

lemma nonedgeProgram_executes (g : BitString → ℕ) (D a b : ℕ) :
    ∃t,nonedgeProgram.Executes g (state D a b 0 0 [] [])
      (state D a (max b (a+D+1)) 0 0 [] []) t ∧ t≤100*(D+a+b+1) := by
  have h1 : (copyOn (1 : Fin 8) 4 7 (by decide) (by decide) (by decide)).Executes g
      (state D a b 0 0 [] []) (state D a b a 0 [] []) (5*a+2) := by
    convert copyOn_executes g (1 : Fin 8) 4 7 (by decide) (by decide) (by decide) (state D a b 0 0 [] []) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h2 : (copyOn (0 : Fin 8) 4 7 (by decide) (by decide) (by decide)).Executes g
      (state D a b a 0 [] []) (state D a b (a+D) 0 [] []) (5*D+2) := by
    convert copyOn_executes g (0 : Fin 8) 4 7 (by decide) (by decide) (by decide) (state D a b a 0 [] []) rfl using 1
    · funext i;fin_cases i <;> simp [state,←List.replicate_add,Nat.add_comm]
    · simp [state]
  have h3 : (push (4 : Fin 8) true).Executes g (state D a b (a+D) 0 [] [])
      (state D a b (a+D+1) 0 [] []) 1 := by
    convert push_executes g (4 : Fin 8) true _ using 1
    funext i;fin_cases i <;> simp [state,List.replicate_succ]
  obtain ⟨c4,h4,b4⟩ := takeMax_false_executes g D a b (a+D+1)
  exact ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),by omega⟩

def left (D a b : ℕ) (edge : Bool) : ℕ := if edge then max a (b-D) else a
def right (D a b : ℕ) (edge : Bool) : ℕ := if edge then max b a else max b (a+D+1)

theorem program_executes (g : BitString → ℕ) (D a b : ℕ) (edge : Bool) :
    ∃t,program.Executes g (state D a b 0 0 [edge] [])
      (state D (left D a b edge) (right D a b edge) 0 0 [] []) t ∧t≤102*(D+a+b+1) := by
  cases edge with
  | false =>
    obtain ⟨t,ht,hb⟩ := nonedgeProgram_executes g D a b
    refine ⟨t+2,branchPop_false _ _ _ _ g rfl ?_,by omega⟩
    convert ht using 1
    funext i;fin_cases i <;> rfl
  | true =>
    obtain ⟨t,ht,hb⟩ := edgeProgram_executes g D a b
    refine ⟨t+2,branchPop_true _ _ _ _ g rfl ?_,by omega⟩
    convert ht using 1
    funext i;fin_cases i <;> rfl

lemma takeMax_queryFree (first : Bool) : (takeMax first).QueryFree := UnitCoordinateExtractionMax.on_queryFree _
lemma subtract_queryFree : subtract.QueryFree :=
  seq_queryFree _ _ (CNFCloneEmitter.UnarySplit.on_queryFree _) (clear_queryFree _)
lemma edgeProgram_queryFree : edgeProgram.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (takeMax_queryFree _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ subtract_queryFree (takeMax_queryFree _)))))
lemma nonedgeProgram_queryFree : nonedgeProgram.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (push_queryFree _ _) (takeMax_queryFree _)))
lemma program_queryFree : program.QueryFree :=
  branchPop_queryFree _ _ _ _ skip_queryFree nonedgeProgram_queryFree edgeProgram_queryFree
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionScalar
