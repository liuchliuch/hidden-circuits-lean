import HiddenCircuits.Approximation.Initialization.Search.Stage.Program

namespace HiddenCircuits.Approximation.Initialization.Search.Stage
open Complexity Complexity.OracleBlock

theorem finish_executes (g : BitString → ℕ) (N : ℕ) (payload mask source : BitString)
    (B : ℕ) (data : BitString) (L p : ℕ) (selected stage : BitString) (ok : Bool) :
    (finish ok).Executes g (work N payload mask source B data L [] p [] selected stage [] [])
      (state N payload mask source B data L [ok]) (p+selected.length+stage.length+10) := by
  have h1 : (clear (8:Fin 51)).Executes g
      (work N payload mask source B data L [] p [] selected stage [] [])
      (work N payload mask source B data L [] 0 [] selected stage [] []) (p+1) := by
    convert clear_executes g (8:Fin 51) (work N payload mask source B data L [] p [] selected stage [] []) using 1
    · funext r;fin_cases r <;> rfl
    · simp [work]
  have h2 : (clear (11:Fin 51)).Executes g
      (work N payload mask source B data L [] 0 [] selected stage [] [])
      (work N payload mask source B data L [] 0 [] [] stage [] []) (selected.length+1) := by
    convert clear_executes g (11:Fin 51) (work N payload mask source B data L [] 0 [] selected stage [] []) using 1
    funext r;fin_cases r <;> rfl
  have h3 : (clear (12:Fin 51)).Executes g
      (work N payload mask source B data L [] 0 [] [] stage [] [])
      (work N payload mask source B data L [] 0 [] [] [] [] []) (stage.length+1) := by
    convert clear_executes g (12:Fin 51) (work N payload mask source B data L [] 0 [] [] stage [] []) using 1
    funext r;fin_cases r <;> rfl
  have h4 : (push (7:Fin 51) ok).Executes g
      (work N payload mask source B data L [] 0 [] [] [] [] [])
      (state N payload mask source B data L [ok]) 1 := by
    convert push_executes g (7:Fin 51) ok (work N payload mask source B data L [] 0 [] [] [] [] []) using 1
    funext r;fin_cases r <;> rfl
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)) using 1 <;> omega

theorem prepare_executes (g : BitString → ℕ) (N : ℕ) (payload mask source : BitString)
    (B : ℕ) (data : BitString) (L p : ℕ) :
    prepare.Executes g (work N payload mask source B data L [] p [] [] [] [] [])
      (work N payload mask (source.drop L) B data L [] p [] []
        (SamplerRuntime.TapeRead.takePadded L source) [] []) (12*L+8) := by
  have h1 : (copyOn (6:Fin 51) 13 18 (by decide) (by decide) (by decide)).Executes g
      (work N payload mask source B data L [] p [] [] [] [] [])
      (work N payload mask source B data L [] p [] [] [] (unary L) []) (5*L+2) := by
    convert copyOn_executes g (6:Fin 51) 13 18 (by decide) (by decide) (by decide)
      (work N payload mask source B data L [] p [] [] [] [] []) rfl using 1
    · funext r;fin_cases r <;> simp [work]
    · simp [work]
  have h2 : (SamplerRuntime.TapeRead.on tapePorts).Executes g
      (work N payload mask source B data L [] p [] [] [] (unary L) [])
      (work N payload mask (source.drop L) B data L [] p [] [] [] []
        (SamplerRuntime.TapeRead.takePadded L source).reverse) (5*L+1) := by
    convert SamplerRuntime.TapeRead.on_executes tapePorts g
      (work N payload mask source B data L [] p [] [] [] (unary L) [])
      (work N payload mask (source.drop L) B data L [] p [] [] [] []
        (SamplerRuntime.TapeRead.takePadded L source).reverse) source (unary L) []
      (by funext r;fin_cases r <;> rfl)
      (by funext r;fin_cases r <;> simp [work,tapePorts,SamplerRuntime.TapeRead.state])
      (by
        intro r hr
        fin_cases r
        all_goals first | rfl | exact False.elim (hr 0 rfl) | exact False.elim (hr 1 rfl) | exact False.elim (hr 2 rfl)) using 1
    simp
  have h3 : (reverseOn (14:Fin 51) 12 (by decide)).Executes g
      (work N payload mask (source.drop L) B data L [] p [] [] [] []
        (SamplerRuntime.TapeRead.takePadded L source).reverse)
      (work N payload mask (source.drop L) B data L [] p [] []
        (SamplerRuntime.TapeRead.takePadded L source) [] []) (2*L+1) := by
    convert reverseOn_executes g (14:Fin 51) 12 (by decide)
      (work N payload mask (source.drop L) B data L [] p [] [] [] []
        (SamplerRuntime.TapeRead.takePadded L source).reverse) using 1
    · funext r;fin_cases r <;> simp [work]
    · simp [work,SamplerRuntime.TapeRead.prefix_length]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1 <;> omega

theorem pivot_executes (g : BitString → ℕ) (N : ℕ) (payload mask source : BitString)
    (B : ℕ) (data : BitString) (L : ℕ) :
    ∃ t,(SelfReduction.Runtime.firstTrueOn pivotPorts).Executes g
      (state N payload mask source B data L [])
      (work N payload mask source B data L [] (SelfReduction.Runtime.seekPos mask)
        [SelfReduction.Runtime.seekFound mask] [] [] [] []) t ∧ t≤8*mask.length+9 := by
  exact SelfReduction.Runtime.firstTrueOn_executes pivotPorts g
    (state N payload mask source B data L [])
    (work N payload mask source B data L [] (SelfReduction.Runtime.seekPos mask)
      [SelfReduction.Runtime.seekFound mask] [] [] [] []) mask
    (by funext r;fin_cases r <;> rfl)
    (by funext r;fin_cases r <;> rfl)
    (by
      intro r hr
      fin_cases r
      all_goals first | rfl | exact False.elim (hr 1 rfl) | exact False.elim (hr 3 rfl))

end HiddenCircuits.Approximation.Initialization.Search.Stage
