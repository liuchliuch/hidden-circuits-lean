import HiddenCircuits.Complexity.LocalCellEmitter

/-! Fixed finite families of cell emitters: control states and stack symbols.
All variable-height iteration is left to the actual row loop. -/
namespace HiddenCircuits.Complexity.FamilyEmitter
open OracleBlock TM2BooleanEncoding OutputLiteralEmitter Polynomial

noncomputable def controls (M : Turing.FinTM2) : List (Family M) :=
  List.ofFn (fun i : Fin (controlBits M) => Sum.inl ((Fintype.equivFin (Control M)).symm i))
noncomputable def symbols (M : Turing.FinTM2) : List (Family M) :=
  List.ofFn (fun i : Fin (symbolBits M) => Sum.inr ((symbolEnumeration M).symm i))

noncomputable def bits (M : Turing.FinTM2) (fs : List (Family M)) (j r base nextBase : ℕ) : BitString :=
  fs.flatMap (fun f => LocalCellEmitter.bits M f j r base nextBase)
noncomputable def program (M : Turing.FinTM2) (fs : List (Family M)) : OracleBlock 7 :=
  sequence (fs.map (LocalCellEmitter.program M))
noncomputable def sumTimes (M : Turing.FinTM2) : List (Family M) → Polynomial ℕ
  | [] => 0
  | f::fs => LocalCellEmitter.time M f+sumTimes M fs
noncomputable def time (M : Turing.FinTM2) (fs : List (Family M)) : Polynomial ℕ :=
  sumTimes M fs+C (2*fs.length+1)

lemma sumTimes_eval (M : Turing.FinTM2) (fs : List (Family M)) (n : ℕ) :
    (sumTimes M fs).eval n = (fs.map (fun f => (LocalCellEmitter.time M f).eval n)).sum := by
  induction fs <;> simp [sumTimes, *]

theorem program_executes (g : BitString → ℕ) (M : Turing.FinTM2) (fs : List (Family M))
    (j r base nextBase : ℕ) (stream : BitString) :
    ∃ cost, (program M fs).Executes g (LocalClauseEmitter.state j base nextBase 0 0 0 r stream)
      (LocalClauseEmitter.state j base nextBase 0 0 0 r ((bits M fs j r base nextBase).reverse++stream)) cost ∧
      cost ≤ (time M fs).eval (j+r+base+nextBase) := by
  have hitem (f : Family M) (_ : f∈fs) (acc : BitString) : ∃ cost,
      (LocalCellEmitter.program M f).Executes g
        (Function.update (LocalClauseEmitter.state j base nextBase 0 0 0 r []) 6 acc)
        (Function.update (LocalClauseEmitter.state j base nextBase 0 0 0 r []) 6
          ((LocalCellEmitter.bits M f j r base nextBase).reverse++acc)) cost ∧
      cost ≤ (LocalCellEmitter.time M f).eval (j+r+base+nextBase) := by
    simpa only [LocalClauseEmitter.update_stream] using LocalCellEmitter.program_executes g M f j r base nextBase acc
  obtain ⟨cost,hc,hb⟩ := sequence_emit_bounded g fs (LocalCellEmitter.program M)
    (fun f => LocalCellEmitter.bits M f j r base nextBase)
    (fun f => (LocalCellEmitter.time M f).eval (j+r+base+nextBase))
    (LocalClauseEmitter.state j base nextBase 0 0 0 r []) 6 hitem stream
  refine ⟨cost,?_,?_⟩
  · simpa only [LocalClauseEmitter.update_stream] using hc
  · simpa only [time,Polynomial.eval_add,Polynomial.eval_C,sumTimes_eval] using hb

lemma program_queryFree (M : Turing.FinTM2) (fs : List (Family M)) : (program M fs).QueryFree := by
  apply sequence_queryFree
  intro B hb
  obtain ⟨f,_,rfl⟩ := List.mem_map.mp hb
  exact LocalCellEmitter.program_queryFree _ _

/-- Emit one stack position's fixed symbol family, then physically increment the
unary position register. The remaining-height counter is preserved by the body. -/
noncomputable def symbolBody (M : Turing.FinTM2) : OracleBlock 7 :=
  seq (program M (symbols M)) (push 0 true)

theorem symbolBody_executes (g : BitString → ℕ) (M : Turing.FinTM2) (j r base nextBase : ℕ) (stream : BitString) :
    ∃ cost, (symbolBody M).Executes g (LocalClauseEmitter.state j base nextBase 0 0 0 r stream)
      (LocalClauseEmitter.state (j+1) base nextBase 0 0 0 r
        ((bits M (symbols M) j r base nextBase).reverse++stream)) cost ∧
      cost ≤ (time M (symbols M)).eval (j+r+base+nextBase)+3 := by
  obtain ⟨cost,hc,hb⟩ := program_executes g M (symbols M) j r base nextBase stream
  have hp := push_executes g (0 : Fin 8) true
    (LocalClauseEmitter.state j base nextBase 0 0 0 r ((bits M (symbols M) j r base nextBase).reverse++stream))
  have he : Function.update
      (LocalClauseEmitter.state j base nextBase 0 0 0 r ((bits M (symbols M) j r base nextBase).reverse++stream))
      0 (true::List.replicate j true) =
      LocalClauseEmitter.state (j+1) base nextBase 0 0 0 r ((bits M (symbols M) j r base nextBase).reverse++stream) := by
    funext i;fin_cases i <;> simp [LocalClauseEmitter.state,List.replicate_succ]
  change (push (0 : Fin 8) true).Executes g _
    (Function.update _ 0 (true::List.replicate j true)) 1 at hp
  rw [he] at hp
  refine ⟨cost+1+2,seq_executes _ _ g hc hp,by omega⟩

lemma symbolBody_queryFree (M : Turing.FinTM2) : (symbolBody M).QueryFree :=
  seq_queryFree _ _ (program_queryFree _ _) (push_queryFree _ _)

end HiddenCircuits.Complexity.FamilyEmitter
