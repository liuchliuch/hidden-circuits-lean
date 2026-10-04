import HiddenCircuits.DH.LinearBuckets

/-! Pure ordered-partition semantics for the operational LexBFS refinement engine.
This model is an extensional specification; its list scans are not assigned the engine's
linear running time. The implementation refines it with direct vertex/cell pointers. -/
namespace HiddenCircuits.DH.LexBFSModel

abbrev Partition (V : Type*) := List (List V)

/-- Empty cells are never present in the canonical semantic partition. -/
def nonemptyCell {V : Type*} (xs : List V) : Partition V := if xs = [] then [] else [xs]

/-- `neighborsFirst = false` implements a complement sweep without complement rows. -/
def splitCell {V : Type*} (neighborsFirst : Bool) (adjacent : V → Bool) (xs : List V) : Partition V :=
  let yes := xs.filter adjacent
  let no := xs.filter (fun x => !adjacent x)
  if neighborsFirst then nonemptyCell yes ++ nonemptyCell no
  else nonemptyCell no ++ nonemptyCell yes

/-- Stable refinement never moves a vertex across a pre-existing cell boundary. -/
def refine {V : Type*} (neighborsFirst : Bool) (adjacent : V → Bool) (p : Partition V) : Partition V :=
  p.flatMap (splitCell neighborsFirst adjacent)

/-- Pop the first vertex of the first nonempty cell, recording its pre-pop slice size. -/
def pop {V : Type*} : Partition V → Option (V × ℕ × Partition V)
  | [] => none
  | []::ps => pop ps
  | (v::vs)::ps => some (v,vs.length+1,nonemptyCell vs ++ ps)

structure Event (V : Type*) where
  vertex : V
  sliceSize : ℕ
  deriving Repr, DecidableEq

/-- The actual output contains one pivot and one integer slice size per vertex. -/
def run {V : Type*} (adjacent : V → V → Bool) (neighborsFirst : Bool) :
    ℕ → Partition V → List (Event V)
  | 0,_ => []
  | fuel+1,p => match pop p with
    | none => []
    | some (v,size,q) => ⟨v,size⟩::run adjacent neighborsFirst fuel (refine neighborsFirst (adjacent v) q)

/-- Starting from the supplied tie order, the next pivot is always its first remaining
vertex in the first cell. Stable refinement preserves that tie order inside cells. -/
def sweep {V : Type*} (adjacent : V → V → Bool) (neighborsFirst : Bool) (tieOrder : List V) :
    List (Event V) := run adjacent neighborsFirst tieOrder.length (nonemptyCell tieOrder)

/-- Effective adjacency preference, for normal and complement sweeps respectively. -/
def prefers {V : Type*} (adjacent : V → V → Bool) (neighborsFirst : Bool) (u v : V) : Bool :=
  adjacent u v == neighborsFirst

end HiddenCircuits.DH.LexBFSModel
