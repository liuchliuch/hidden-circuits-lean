import HiddenCircuits.Complexity.DeterminantRuntime.MatrixProductLayout
import HiddenCircuits.Complexity.UnaryArithmetic

/-! Actual unary row-offset preparation and scratch cleanup for matrix cells. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.MatrixProduct
open OracleBlock BinaryArithmetic

noncomputable def rowSetup : OracleBlock 24 :=
  seq (copyOn 1 13 14 (by decide) (by decide) (by decide))
    (seq (repeatCopy 13 0 10 14 (by decide) (by decide) (by decide))
      (seq (push 11 true) (push 3 false)))

theorem rowSetup_executes (g : BitString → ℕ) (n i j : ℕ) (out inner outer a b : BitString) :
    rowSetup.Executes g (cellState n i j [] out inner outer a b [] [] [] [])
      (cellState n i j (signedBits 0) out inner outer a b (List.replicate (i*n) true) [true] [] [])
      (5*i+(5*n+4)*i+11) := by
  let s := cellState n i j [] out inner outer a b [] [] [] []
  let s1 := Function.update s (13 : Fin 25) (List.replicate i true)
  let s2 := cellState n i j [] out inner outer a b (List.replicate (i*n) true) [] [] []
  let s3 := cellState n i j [] out inner outer a b (List.replicate (i*n) true) [true] [] []
  have h1 : (copyOn (1 : Fin 25) 13 14 (by decide) (by decide) (by decide)).Executes g s s1 (5*i+2) := by
    simpa only [show s 1 = List.replicate i true from rfl, show s 13 = [] from rfl,
      List.length_replicate, List.append_nil] using
      copyOn_executes g (1 : Fin 25) 13 14 (by decide) (by decide) (by decide) s rfl
  have h2 : (repeatCopy (13 : Fin 25) 0 10 14 (by decide) (by decide) (by decide)).Executes g s1 s2
      ((5*n+4)*i+1) := by
    have h := unaryMultiply_executes g (13 : Fin 25) 0 10 14
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s1 i n (by simp [s1]) rfl (by rfl)
    have he : workStore s1 13 10 [] (List.replicate (i*n) true++s1 10) = s2 := by
      funext q; fin_cases q <;> simp [workStore,s1,s,s2,cellState]
    rw [he] at h
    exact h
  have h3 : (push (11 : Fin 25) true).Executes g s2 s3 1 := by
    convert push_executes g (11 : Fin 25) true s2 using 1
    funext q; fin_cases q <;> rfl
  have h4 : (push (3 : Fin 25) false).Executes g s3
      (cellState n i j (signedBits 0) out inner outer a b (List.replicate (i*n) true) [true] [] []) 1 := by
    convert push_executes g (3 : Fin 25) false s3 using 1
    funext q; fin_cases q <;> rfl
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)) using 1 <;> omega

noncomputable def columnSetup : OracleBlock 24 :=
  seq (clear 11) (copyOn 0 11 13 (by decide) (by decide) (by decide))

theorem columnSetup_executes (g : BitString → ℕ) (n i j : ℕ)
    (result out inner outer a b start left : BitString) :
    columnSetup.Executes g (cellState n i j result out inner outer a b start [true] left [])
      (cellState n i j result out inner outer a b start (List.replicate n true) left []) (5*n+6) := by
  let s := cellState n i j result out inner outer a b start [] left []
  have h1 : (clear (11 : Fin 25)).Executes g (cellState n i j result out inner outer a b start [true] left []) s 2 := by
    convert clear_executes g (11 : Fin 25) (cellState n i j result out inner outer a b start [true] left []) using 1
    funext q; fin_cases q <;> rfl
  have h2 : (copyOn (0 : Fin 25) 11 13 (by decide) (by decide) (by decide)).Executes g s
      (cellState n i j result out inner outer a b start (List.replicate n true) left []) (5*n+2) := by
    have h := copyOn_executes g (0 : Fin 25) 11 13 (by decide) (by decide) (by decide) s rfl
    have he : Function.update s 11 (List.replicate n true) =
        cellState n i j result out inner outer a b start (List.replicate n true) left [] := by
      funext q; fin_cases q <;> rfl
    simpa only [show s 0 = List.replicate n true from rfl, show s 11 = [] from rfl,
      List.append_nil, List.length_replicate, he] using h
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

noncomputable def cellCleanup : OracleBlock 24 := seq (clear 10) (clear 11)

theorem cellCleanup_executes (g : BitString → ℕ) (n i j : ℕ)
    (result out inner outer a b : BitString) :
    cellCleanup.Executes g
      (cellState n i j result out inner outer a b (List.replicate (i*n) true) (List.replicate n true) [] [])
      (cellState n i j result out inner outer a b [] [] [] []) (i*n+n+4) := by
  have h1 : (clear (10 : Fin 25)).Executes g
      (cellState n i j result out inner outer a b (List.replicate (i*n) true) (List.replicate n true) [] [])
      (cellState n i j result out inner outer a b [] (List.replicate n true) [] []) (i*n+1) := by
    have h := clear_executes g (10 : Fin 25)
      (cellState n i j result out inner outer a b (List.replicate (i*n) true) (List.replicate n true) [] [])
    have he : Function.update
        (cellState n i j result out inner outer a b (List.replicate (i*n) true) (List.replicate n true) [] []) 10 [] =
        cellState n i j result out inner outer a b [] (List.replicate n true) [] [] := by
      funext q; fin_cases q <;> rfl
    simpa only [show cellState n i j result out inner outer a b (List.replicate (i*n) true)
      (List.replicate n true) [] [] 10 = List.replicate (i*n) true from rfl,List.length_replicate,he] using h
  have h2 : (clear (11 : Fin 25)).Executes g
      (cellState n i j result out inner outer a b [] (List.replicate n true) [] [])
      (cellState n i j result out inner outer a b [] [] [] []) (n+1) := by
    have h := clear_executes g (11 : Fin 25) (cellState n i j result out inner outer a b [] (List.replicate n true) [] [])
    have he : Function.update (cellState n i j result out inner outer a b [] (List.replicate n true) [] []) 11 [] =
        cellState n i j result out inner outer a b [] [] [] [] := by
      funext q; fin_cases q <;> rfl
    simpa only [show cellState n i j result out inner outer a b [] (List.replicate n true) [] [] 11 =
      List.replicate n true from rfl,List.length_replicate,he] using h
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

theorem rowSetup_queryFree : rowSetup.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (repeatCopy_queryFree _ _ _ _ _ _ _)
    (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _)))
theorem columnSetup_queryFree : columnSetup.QueryFree := seq_queryFree _ _ (clear_queryFree _)
  (copyOn_queryFree _ _ _ _ _ _)
theorem cellCleanup_queryFree : cellCleanup.QueryFree := seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)

end HiddenCircuits.Complexity.DeterminantRuntime.MatrixProduct
