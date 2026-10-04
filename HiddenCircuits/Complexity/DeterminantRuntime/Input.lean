import HiddenCircuits.Complexity.DeterminantRuntime.RoundLayout
import HiddenCircuits.Complexity.GraphVerifier.RuntimeLibrary
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorProduct

/-! Actual canonical matrix-header parsing and rearrangement into round storage. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.Input
open OracleBlock

def store (xs : BitString) : Store 30 := Function.update (fun _ => []) 0 xs

def state (data header temporary flag : BitString) : Store 30 := fun q =>
  if q.val=0 then data else if q.val=1 then header else if q.val=2 then temporary else
  if q.val=3 then flag else []

def parsePorts : Fin 4 ↪ Fin 31 where
  toFun := ![0,1,2,3]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def program : OracleBlock 30 := seq (GraphVerifier.Runtime.unpairOn parsePorts)
  (seq (reverseOn 0 2 (by decide))
    (seq (moveOn 1 0 4 (by decide) (by decide) (by decide))
      (seq (reverseOn 2 1 (by decide)) (clear 3))))

theorem executes (g : BitString → ℕ) (n : ℕ) (data : BitString) :
    program.Executes g (store (pairBits (List.replicate n true) data))
      (Round.store n data [] [] 0 0) (11*n+4*data.length+20) := by
  have hparse : (GraphVerifier.Runtime.unpairOn parsePorts).Executes g
      (store (pairBits (List.replicate n true) data)) (state data (List.replicate n true) [] [true]) (5*n+3) := by
    have h := GraphVerifier.Runtime.unpairOn_executes parsePorts g
      (store (pairBits (List.replicate n true) data)) (state data (List.replicate n true) [] [true])
      (pairBits (List.replicate n true) data)
      (by funext q; fin_cases q <;> rfl)
      (by funext q; fin_cases q <;> simp only [GraphVerifier.parse_pair] <;> rfl)
      (by
        intro q hq
        fin_cases q <;> first | exact (hq 0 rfl).elim | exact (hq 1 rfl).elim | exact (hq 3 rfl).elim | rfl)
    convert h using 1
    simp [GraphVerifier.parse_pair,BinaryArithmetic.pair_parse_cost]
    omega
  have h1 : (reverseOn (0 : Fin 31) 2 (by decide)).Executes g
      (state data (List.replicate n true) [] [true]) (state [] (List.replicate n true) data.reverse [true])
      (2*data.length+1) := by
    convert reverseOn_executes g (0 : Fin 31) 2 (by decide) (state data (List.replicate n true) [] [true]) using 1
    funext q; fin_cases q <;> simp [state]
  have h2 : (moveOn (1 : Fin 31) 0 4 (by decide) (by decide) (by decide)).Executes g
      (state [] (List.replicate n true) data.reverse [true]) (state (List.replicate n true) [] data.reverse [true])
      (6*n+5) := by
    have h := moveOn_executes g (1 : Fin 31) 0 4 (by decide) (by decide) (by decide)
      (state [] (List.replicate n true) data.reverse [true]) rfl
    have he : Function.update (Function.update (state [] (List.replicate n true) data.reverse [true]) 0
        (List.replicate n true)) 1 [] = state (List.replicate n true) [] data.reverse [true] := by
      funext q; fin_cases q <;> rfl
    simpa only [show state [] (List.replicate n true) data.reverse [true] 1 = List.replicate n true from rfl,
      show state [] (List.replicate n true) data.reverse [true] 0 = [] from rfl,List.append_nil,List.length_replicate,he] using h
  have h3 : (reverseOn (2 : Fin 31) 1 (by decide)).Executes g
      (state (List.replicate n true) [] data.reverse [true]) (state (List.replicate n true) data [] [true])
      (2*data.length+1) := by
    convert reverseOn_executes g (2 : Fin 31) 1 (by decide) (state (List.replicate n true) [] data.reverse [true]) using 1
    · funext q; fin_cases q <;> simp [state]
    · simp [state]
  have h4 : (clear (3 : Fin 31)).Executes g (state (List.replicate n true) data [] [true])
      (Round.store n data [] [] 0 0) 2 := by
    convert clear_executes g (3 : Fin 31) (state (List.replicate n true) data [] [true]) using 1
    funext q; fin_cases q <;> rfl
  convert seq_executes _ _ g hparse (seq_executes _ _ g h1
    (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4))) using 1 <;> omega

theorem queryFree : program.QueryFree := seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _)
  (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (clear_queryFree _))))

end HiddenCircuits.Complexity.DeterminantRuntime.Input
