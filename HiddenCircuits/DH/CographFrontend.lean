import HiddenCircuits.DH.CographSortedHeads
import HiddenCircuits.DH.CographProgramCorrectness
import HiddenCircuits.DH.LexBFSAlgorithm
import HiddenCircuits.DH.FirstHeadChoices

/-! Ordinary-input linear cotree construction from two verified pointer sweeps,
sparse profile counting, stable size ordering, and counted recursive assembly. -/
namespace HiddenCircuits.DH.CographFrontend
open SimpleGraph LexBFSModel LinearBuckets CographProgram
variable {n : ℕ}

structure Prepared (n : ℕ) where
  data : HeadData n
  normalEvents : List (Event (Fin n))
  complementEvents : List (Event (Fin n))
  accesses : ℕ

/-- The first output order becomes the second input tie order. All graph tests
are performed against original adjacency rows, including complementary sweeps. -/
def prepare (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v:Fin n, (rows[v.val]).Nodup) (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) : Prepared n :=
  let a := LexBFSAlgorithm.runOrdered rows true tie hp
  let next := mapCount Event.vertex a.value
  let hpNext : next.1.Perm (List.finRange n) := by
    rw [mapCount_values]
    exact LexBFSAlgorithm.runOrdered_perm G rows hr hn true tie hp
  let b := LexBFSAlgorithm.runOrdered rows false next.1 hpNext
  let headsA := CographSortedHeads.run rows true a.value
  let headsB := CographSortedHeads.run rows false b.value
  let choices := FirstHeadChoices.construct rows headsA.rows headsB.rows
  ⟨⟨headsA.rows,headsB.rows,choices.choices⟩,a.value,b.value,
    a.accesses+next.2+b.accesses+headsA.accesses+headsB.accesses+choices.accesses⟩

lemma prepare_events (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v:Fin n, (rows[v.val]).Nodup) (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) :
    (prepare G rows hr hn tie hp).normalEvents=sweep (fun a b => decide (G.Adj a b)) true tie ∧
    (prepare G rows hr hn tie hp).complementEvents=sweep (fun a b => decide (G.Adj a b)) false
      ((sweep (fun a b => decide (G.Adj a b)) true tie).map Event.vertex) := by
  simp only [prepare,LexBFSAlgorithm.runOrdered_correct G rows hr hn,mapCount_values]
  simp

lemma prepare_data (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v:Fin n, (rows[v.val]).Nodup) (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) :
    let normal := sweep (fun a b => decide (G.Adj a b)) true tie
    let other := sweep (fun a b => decide (G.Adj a b)) false (normal.map Event.vertex)
    let a := CographSortedHeads.run rows true normal
    let b := CographSortedHeads.run rows false other
    (prepare G rows hr hn tie hp).data=
      ⟨a.rows,b.rows,(FirstHeadChoices.construct rows a.rows b.rows).choices⟩ := by
  simp only [prepare,LexBFSAlgorithm.runOrdered_correct G rows hr hn,mapCount_values]

/-- Every local head-array property used by the interpreter is derived from
ordinary rows and the paired-slice invariant of the actual sweeps. -/
theorem prepare_correct (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : P4Free G)
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v:Fin n, (rows[v.val]).Nodup) (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) :
    DataCorrect G tie (prepare G rows hr hn tie hp).data := by
  let normal := sweep (fun a b => decide (G.Adj a b)) true tie
  let other := sweep (fun a b => decide (G.Adj a b)) false (normal.map Event.vertex)
  have htie : tie.Nodup := hp.nodup_iff.mpr (List.nodup_finRange n)
  have hcover : ∀v:Fin n, v∈tie := fun v => hp.mem_iff.mpr (List.mem_finRange v)
  have hpN := sweep_perm (fun a b => decide (G.Adj a b)) true tie
  have hnN : (normal.map Event.vertex).Nodup := hpN.nodup_iff.mpr htie
  have hcoverN : ∀v, v∈normal.map Event.vertex := fun v => hpN.mem_iff.mpr (hcover v)
  have hpC := sweep_perm (fun a b => decide (G.Adj a b)) false (normal.map Event.vertex)
  have hnC : (other.map Event.vertex).Nodup := hpC.nodup_iff.mpr hnN
  rw [prepare_data]
  constructor
  · intro r
    exact (CographSortedHeads.row_perm rows true normal r).nodup_iff.mpr
      (hnN.sublist (NonpreferredHeads.construct_child_sublist G rows hr true normal r))
  · intro r
    exact (CographSortedHeads.row_perm rows false other r).nodup_iff.mpr
      (hnC.sublist (NonpreferredHeads.construct_child_sublist G rows hr false other r))
  · intro M r hInv x
    obtain ⟨past,size,tail,he,henv⟩ := hInv.normal_position
    exact (CographSortedHeads.row_perm rows true normal r).mem_iff.trans
      (hG.normal_heads_iff rows hr tie htie hcover past ⟨r,size⟩ tail he hInv.module hInv.root_mem henv x)
  · intro M r hInv x
    obtain ⟨past,size,tail,he,henv⟩ := hInv.complement_position
    exact (CographSortedHeads.row_perm rows false other r).mem_iff.trans
      (hG.complement_heads_iff rows hr (normal.map Event.vertex) hnN hcoverN past ⟨r,size⟩ tail he
        hInv.module hInv.root_mem henv x)
  · intro M r hInv
    obtain ⟨past,size,tail,he,henv⟩ := hInv.normal_position
    have hfamily := hG.normal_head_family rows hr tie htie hcover past ⟨r,size⟩ tail he
      hInv.module hInv.root_mem henv
    exact (hfamily.perm (CographSortedHeads.row_perm rows true normal r)).strict_order hG
      (CographSortedHeads.normal_card_order G rows hr hn normal hnN r)
  · intro M r hInv
    obtain ⟨past,size,tail,he,henv⟩ := hInv.complement_position
    have hfamily := hG.complement_head_family rows hr (normal.map Event.vertex) hnN hcoverN past ⟨r,size⟩ tail he
      hInv.module hInv.root_mem henv
    exact (hfamily.perm (CographSortedHeads.row_perm rows false other r)).strict_order hG.compl
      (CographSortedHeads.complement_card_order G rows hr hn other hnC r)
  · intro r
    exact FirstHeadChoices.construct_headChoice G rows hr _ _ r

lemma incidenceCount_eq_sum (rows : Vector (List (Fin n)) n) :
    Adjacency.incidenceCount rows=∑i:Fin n, rows[i.val].length := by
  simp only [Adjacency.incidenceCount,Adjacency.entriesFrom_values,List.length_flatMap,List.map_map,List.length_map]
  rw [←List.ofFn_eq_map,List.sum_ofFn]

/-- Both complete pointer sweeps and every sparse frontend pass are included. -/
theorem prepare_accesses (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v:Fin n, (rows[v.val]).Nodup) (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) :
    (prepare G rows hr hn tie hp).accesses≤210*Adjacency.incidenceCount rows+325*n+8 := by
  let a := LexBFSAlgorithm.runOrdered rows true tie hp
  let next := mapCount Event.vertex a.value
  have hpNext : next.1.Perm (List.finRange n) := by
    rw [mapCount_values]
    exact LexBFSAlgorithm.runOrdered_perm G rows hr hn true tie hp
  let b := LexBFSAlgorithm.runOrdered rows false next.1 hpNext
  have ha := LexBFSAlgorithm.runOrdered_accesses G rows hr hn true tie hp
  have hb := LexBFSAlgorithm.runOrdered_accesses G rows hr hn false next.1 hpNext
  have hpA := LexBFSAlgorithm.runOrdered_perm G rows hr hn true tie hp
  have hpB := LexBFSAlgorithm.runOrdered_perm G rows hr hn false next.1 hpNext
  have hlenA : a.value.length=n := by simpa [a] using hpA.length_eq
  have hlenB : b.value.length=n := by simpa [b] using hpB.length_eq
  have hnA := hpA.nodup_iff.mpr (List.nodup_finRange n)
  have hnB := hpB.nodup_iff.mpr (List.nodup_finRange n)
  have hmap : next.2=2*n := by simp [next,hlenA]
  have hheadA := CographSortedHeads.accesses G rows hr true a.value hnA
  have hheadB := CographSortedHeads.accesses G rows hr false b.value hnB
  have hc := FirstHeadChoices.construct_accesses rows
    (CographSortedHeads.run rows true a.value).rows (CographSortedHeads.run rows false b.value).rows
  have hI := incidenceCount_eq_sum rows
  change a.accesses+next.2+b.accesses+(CographSortedHeads.run rows true a.value).accesses+
    (CographSortedHeads.run rows false b.value).accesses+
    (FirstHeadChoices.construct rows (CographSortedHeads.run rows true a.value).rows
      (CographSortedHeads.run rows false b.value).rows).accesses≤_
  change a.accesses≤_ at ha
  change b.accesses≤_ at hb
  omega

/-- Ordinary finite input. The graph and row-support proofs justify erased
permutation obligations; every executable graph access is to the supplied rows. -/
def construct (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v:Fin n, (rows[v.val]).Nodup) : Result n :=
  if hz : n=0 then ⟨none,1,0⟩ else
    let p := prepare G rows hr hn (List.finRange n) (.refl _)
    let out := CographProgram.run n p.data ⟨0,Nat.pos_of_ne_zero hz⟩
    ⟨out.tree,p.accesses+out.accesses+n+1,out.allocations⟩

/-- Genuine ordinary-input linear cotree construction: no supplied cotree,
pruning sequence, module schedule, or head-array certificate appears here. -/
theorem construct_spec (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : P4Free G)
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v:Fin n, (rows[v.val]).Nodup) (hpos : 0<n) :
    ∃t, (construct G rows hr hn).tree=some t ∧ LabeledCographTree.Correct G t ∧ t.leaves.Nodup ∧
      (∀v, v∈t.leaves) ∧ (construct G rows hr hn).accesses≤400*(n+Adjacency.incidenceCount rows)+9 ∧
      (construct G rows hr hn).allocations+1=2*n := by
  classical
  cases n with
  | zero => omega
  | succ k =>
    let p := prepare G rows hr hn (List.finRange (k+1)) (.refl _)
    have hd : DataCorrect G (List.finRange (k+1)) p.data := prepare_correct G hG rows hr hn _ _
    have hi : PairedModule G (sweep (fun a b => decide (G.Adj a b)) true (List.finRange (k+1)))
        (sweep (fun a b => decide (G.Adj a b)) false
          ((sweep (fun a b => decide (G.Adj a b)) true (List.finRange (k+1))).map Event.vertex)) Set.univ 0 := by
      simpa only [List.finRange_succ] using (PairedModule.initial (G := G) (0 : Fin (k+1)) ((List.finRange k).map Fin.succ))
    obtain ⟨t,ht,hc,htn,hcover,hacc,halloc⟩ := run_correct_resources G hG (List.finRange (k+1))
      (List.nodup_finRange _) (fun v => List.mem_finRange v) p.data hd (k+1) Set.univ 0 hi (by simp)
    have hpacc := prepare_accesses G rows hr hn (List.finRange (k+1)) (.refl _)
    simp only [Set.ncard_univ,Nat.card_fin] at hacc halloc
    refine ⟨t,?_,hc,htn,?_,?_,?_⟩
    · simpa only [construct,Nat.succ_ne_zero,↓reduceDIte,p] using ht
    · intro v; exact (hcover v).mpr (Set.mem_univ _)
    · simp only [construct,Nat.succ_ne_zero,↓reduceDIte]
      change p.accesses+(CographProgram.run (k+1) p.data 0).accesses+(k+1)+1≤_
      change p.accesses≤_ at hpacc
      omega
    · simpa only [construct,Nat.succ_ne_zero,↓reduceDIte,p] using halloc

end HiddenCircuits.DH.CographFrontend
