import HiddenCircuits.Complexity.DeterminantRuntime.Encoding
import HiddenCircuits.Complexity.MatrixEmitterSerialization

/-! Shared clean 25-stack matrix-operation interface.  -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.MatrixProduct
open OracleBlock

def store (n : ℕ) (a b output : BitString) : Store 24 := fun q =>
  if q.val = 0 then List.replicate n true else if q.val = 7 then output else
  if q.val = 8 then a else if q.val = 9 then b else []

def params (a b : BitString) : Store 24 := store 0 a b []

def cellState (n i j : ℕ) (result out inner outer a b start stride left right : BitString) : Store 24 := fun q =>
  if q.val = 0 then List.replicate n true else if q.val = 1 then List.replicate i true else
  if q.val = 2 then List.replicate j true else if q.val = 3 then result else
  if q.val = 4 then out else if q.val = 5 then inner else if q.val = 6 then outer else
  if q.val = 8 then a else if q.val = 9 then b else if q.val = 10 then start else
  if q.val = 11 then stride else if q.val = 12 then left else if q.val = 22 then right else []

theorem cellState_emitter (n i j : ℕ) (result out inner outer a b : BitString) :
    cellState n i j result out inner outer a b [] [] [] [] =
      MatrixEmitter.store n i j result out inner outer (params a b) := by
  funext q; fin_cases q <;> rfl

theorem store_emitter (n : ℕ) (a b : BitString) :
    store n a b [] = MatrixEmitter.store n 0 0 [] [] [] [] (params a b) := by
  funext q; fin_cases q <;> rfl

theorem emitter_output (n : ℕ) (a b output : BitString) :
    Function.update (MatrixEmitter.store n 0 0 [] [] [] [] (params a b)) (MatrixEmitter.port 7) output =
      store n a b output := by
  funext q; fin_cases q <;> rfl

end HiddenCircuits.Complexity.DeterminantRuntime.MatrixProduct
