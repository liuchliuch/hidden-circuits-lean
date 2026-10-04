import HiddenCircuits.DH.LexBFSBlockBoundary
import HiddenCircuits.DH.LexBFSInput
import HiddenCircuits.DH.LexBFSRow
import HiddenCircuits.DH.LexBFSCapacity

/-! Global sparse-sweep correctness and the live-incidence capacity potential. -/
namespace HiddenCircuits.DH.LexBFSPartition
open LexBFSLinks

/-- Original row volume belonging to vertices which have not yet been selected. -/
def liveWork {n : ℕ} (rows : Vector (List (Fin n)) n) (p : LexBFSModel.Partition (Fin n)) : ℕ :=
  (p.flatten.map (fun v => rows[v.val].length)).sum

lemma liveWork_refine {n : ℕ} (rows : Vector (List (Fin n)) n) (first : Bool)
    (a : Fin n → Bool) (p : LexBFSModel.Partition (Fin n)) :
    liveWork rows (LexBFSModel.refine first a p) = liveWork rows p :=
  ((LexBFSModel.refine_perm first a p).map _).sum_eq

lemma liveWork_pop {n : ℕ} (rows : Vector (List (Fin n)) n)
    {p q : LexBFSModel.Partition (Fin n)} {v : Fin n} {size : ℕ}
    (h : LexBFSModel.pop p = some (v,size,q)) :
    liveWork rows p = rows[v.val].length+liveWork rows q := by
  have hp := ((LexBFSModel.pop_perm h).map (fun v => rows[v.val].length)).sum_eq
  simpa [liveWork] using hp.symm

/-- Compositional induction for the actual program. The row lemma is supplied by the
pointer/ghost simulation theorem, rather than a pruning certificate or graph oracle. -/
theorem run_refines_of_row_correct {n b : ℕ} (rows : Vector (List (Fin n)) n) (first : Bool)
    (hrows : ∀ v : Fin n, (rows[v.val]).Pairwise (· < ·))
    (hrow : ∀ {s : Heap n b} {cs : List (Fin b)} {f : CellContents n b},
      Canonical s cs f → ∀ epoch, Ready s epoch → ∀ row : List (Fin n),
      row.Pairwise (· < ·) → s.fresh+row.length ≤ b →
      ∃ cs' f', Canonical (refineRow epoch first row s).value cs' f' ∧
        Ready (refineRow epoch first row s).value (epoch+1) ∧
        cs'.map f' = LexBFSModel.refine first (fun v => decide (v ∈ row)) (cs.map f))
    (fuel epoch : ℕ) (s : Heap n b) (cs : List (Fin b)) (f : CellContents n b)
    (h : Canonical s cs f) (hr : Ready s epoch)
    (hcap : s.fresh+liveWork rows (cs.map f) ≤ b) :
    (run rows first fuel epoch s).events =
      LexBFSModel.run (fun u v => decide (v ∈ rows[u.val])) first fuel (cs.map f) := by
  induction fuel generalizing epoch s cs f with
  | zero => rfl
  | succ fuel ih =>
    cases cs with
    | nil =>
      have hp := pop_empty h.cells
      simp [run,hp,LexBFSModel.run,LexBFSModel.pop]
    | cons c cs =>
      have hne : f c≠[] := (h.support c).mp List.mem_cons_self
      cases hfc : f c with
      | nil => exact False.elim (hne hfc)
      | cons v vs =>
        let tailCells := if vs=[] then cs else c::cs
        let tailContents := Function.update f c vs
        let q := tailCells.map tailContents
        have hp := pop_nonempty h.vertices h.cells v vs hfc
        have hm := pop_model h.vertices h.cells v vs hfc
        have hw : liveWork rows ((c::cs).map f) = rows[v.val].length+liveWork rows q :=
          liveWork_pop rows hm
        have hpc : Canonical (pop s).value.2 tailCells tailContents := pop_canonical h v vs hfc
        have hpr : Ready (pop s).value.2 epoch := pop_ready hr
        have hspace : (pop s).value.2.fresh+rows[v.val].length ≤ b := by
          rw [pop_fresh]
          omega
        obtain ⟨newCells,newContents,hc',hr',he⟩ :=
          hrow hpc epoch hpr rows[v.val] (hrows v) hspace
        have hcap' : (refineRow epoch first rows[v.val] (pop s).value.2).value.fresh+
            liveWork rows (newCells.map newContents) ≤ b := by
          have hf := (refineRow_fresh rows[v.val] (pop s).value.2 epoch first).2
          rw [pop_fresh] at hf
          rw [he,liveWork_refine]
          change _+liveWork rows q ≤ b
          omega
        have ht := ih (epoch+1) (refineRow epoch first rows[v.val] (pop s).value.2).value
          newCells newContents hc' hr' hcap'
        have hpe : (pop s).value.1 = some ⟨v,vs.length+1⟩ := congrArg Prod.fst hp
        simp only [run,hpe,LexBFSModel.run,hm]
        rw [ht,he]

/-- Fixed input-derived capacity. No successful-allocation certificate is provided as input. -/
def sweep {n : ℕ} (rows : Vector (List (Fin n)) n) (first : Bool) :
    Result n (LinearBuckets.Adjacency.incidenceCount rows+1) :=
  let cap := capacityScan rows
  let initial := initialHeap n (cap.value+1) (Nat.zero_lt_succ _)
  let r := run rows first n 1 initial.value
  ⟨capacityScan_value rows ▸ r.heap,r.events,cap.accesses+initial.accesses+r.accesses⟩

lemma sweep_events_eq {n : ℕ} (rows : Vector (List (Fin n)) n) (first : Bool) :
    (sweep rows first).events =
      (run rows first n 1 (initialHeap n (LinearBuckets.Adjacency.incidenceCount rows+1)
        (Nat.zero_lt_succ _)).value).events := by
  change (run rows first n 1 (initialHeap n ((capacityScan rows).value+1)
    (Nat.zero_lt_succ _)).value).events = _
  exact congrArg (fun k : ℕ => (run rows first n 1 (initialHeap n (k+1)
    (Nat.zero_lt_succ k)).value).events) (capacityScan_value rows)

lemma sweep_accesses_eq {n : ℕ} (rows : Vector (List (Fin n)) n) (first : Bool) :
    (sweep rows first).accesses = (capacityScan rows).accesses+
      (initialHeap n (LinearBuckets.Adjacency.incidenceCount rows+1) (Nat.zero_lt_succ _)).accesses+
      (run rows first n 1 (initialHeap n (LinearBuckets.Adjacency.incidenceCount rows+1)
        (Nat.zero_lt_succ _)).value).accesses := by
  have hi := congrArg (fun k : ℕ => (initialHeap n (k+1) (Nat.zero_lt_succ k)).accesses)
    (capacityScan_value rows)
  have hr := congrArg (fun k : ℕ => (run rows first n 1 (initialHeap n (k+1)
    (Nat.zero_lt_succ k)).value).accesses) (capacityScan_value rows)
  change (capacityScan rows).accesses+
      (initialHeap n ((capacityScan rows).value+1) (Nat.zero_lt_succ _)).accesses+
      (run rows first n 1 (initialHeap n ((capacityScan rows).value+1)
        (Nat.zero_lt_succ _)).value).accesses = _
  exact congrArg₂ (fun a b => (capacityScan rows).accesses+a+b) hi hr

lemma initial_partition (n b : ℕ) (hb : 0<b) :
    (if n=0 then [] else [⟨0,hb⟩]).map (initialContents n b hb) =
      LexBFSModel.nonemptyCell (List.finRange n) := by
  by_cases hn : n=0 <;> simp [hn,initialContents,LexBFSModel.nonemptyCell]

lemma liveWork_initial (n : ℕ) (rows : Vector (List (Fin n)) n) :
    liveWork rows (LexBFSModel.nonemptyCell (List.finRange n)) =
      LinearBuckets.Adjacency.incidenceCount rows := by
  simp [liveWork,LinearBuckets.Adjacency.incidenceCount,
    LinearBuckets.Adjacency.entriesFrom_values,List.length_flatMap,List.length_map]

/-- This boundary lemma will be instantiated directly with `refineRow_correct`. -/
theorem sweep_refines_of_row_correct {n : ℕ} (rows : Vector (List (Fin n)) n) (first : Bool)
    (hrows : ∀ v : Fin n, (rows[v.val]).Pairwise (· < ·))
    (hrow : ∀ {s : Heap n (LinearBuckets.Adjacency.incidenceCount rows+1)} {cs} {f},
      Canonical s cs f → ∀ epoch, Ready s epoch → ∀ row : List (Fin n),
      row.Pairwise (· < ·) → s.fresh+row.length ≤ LinearBuckets.Adjacency.incidenceCount rows+1 →
      ∃ cs' f', Canonical (refineRow epoch first row s).value cs' f' ∧
        Ready (refineRow epoch first row s).value (epoch+1) ∧
        cs'.map f' = LexBFSModel.refine first (fun v => decide (v ∈ row)) (cs.map f)) :
    (sweep rows first).events =
      LexBFSModel.sweep (fun u v => decide (v ∈ rows[u.val])) first (List.finRange n) := by
  have hi := run_refines_of_row_correct rows first hrows hrow n 1
    (initialHeap n (LinearBuckets.Adjacency.incidenceCount rows+1) (Nat.zero_lt_succ _)).value
    (if n=0 then [] else [⟨0,Nat.zero_lt_succ _⟩]) (initialContents n _ (Nat.zero_lt_succ _))
    (initialHeap_canonical n _ _) (initialHeap_ready n _ _) (by
      rw [initial_partition,initialHeap_fresh,liveWork_initial]
      omega)
  rw [sweep_events_eq]
  simpa only [initial_partition,LexBFSModel.sweep,List.length_finRange] using hi

/-- Exact semantic refinement yields the promised global linear operation count. -/
theorem sweep_accesses_of_refines {n : ℕ} (rows : Vector (List (Fin n)) n) (first : Bool)
    (he : (sweep rows first).events =
      LexBFSModel.sweep (fun u v => decide (v ∈ rows[u.val])) first (List.finRange n)) :
    (sweep rows first).accesses ≤ 38*n+47*LinearBuckets.Adjacency.incidenceCount rows+7 := by
  have hp : ((sweep rows first).events.map LexBFSModel.Event.vertex).Perm (List.finRange n) := by
    rw [he]
    exact LexBFSModel.sweep_perm _ _ _
  have hi := initialHeap_accesses n (LinearBuckets.Adjacency.incidenceCount rows+1) (Nat.zero_lt_succ _)
  have hp' : ((run rows first n 1 (initialHeap n (LinearBuckets.Adjacency.incidenceCount rows+1)
      (Nat.zero_lt_succ _)).value).events.map LexBFSModel.Event.vertex).Perm (List.finRange n) := by
    rw [← sweep_events_eq]
    exact hp
  have hr := run_accesses_of_perm rows first 1
    (initialHeap n (LinearBuckets.Adjacency.incidenceCount rows+1) (Nat.zero_lt_succ _)).value hp'
  rw [sweep_accesses_eq,capacityScan_accesses]
  omega

/-- Unconditional semantic refinement of the actual pointer sweep, on ordinary sorted rows. -/
theorem sweep_refines {n : ℕ} (rows : Vector (List (Fin n)) n) (first : Bool)
    (hrows : ∀ v : Fin n, (rows[v.val]).Pairwise (· < ·)) :
    (sweep rows first).events =
      LexBFSModel.sweep (fun u v => decide (v ∈ rows[u.val])) first (List.finRange n) :=
  sweep_refines_of_row_correct rows first hrows
    (fun h epoch hready row hsort hcap => refineRow_correct h epoch first row hready hsort hcap)

theorem sweep_accesses {n : ℕ} (rows : Vector (List (Fin n)) n) (first : Bool)
    (hrows : ∀ v : Fin n, (rows[v.val]).Pairwise (· < ·)) :
    (sweep rows first).accesses ≤ 38*n+47*LinearBuckets.Adjacency.incidenceCount rows+7 :=
  sweep_accesses_of_refines rows first (sweep_refines rows first hrows)

end HiddenCircuits.DH.LexBFSPartition
