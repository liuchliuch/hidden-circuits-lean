import HiddenCircuits.DH.PruningSearch
import HiddenCircuits.DH.ModuleStoreSemantics
import HiddenCircuits.DH.PendantExecution

/-! A deliberately slower fixed-label pruning model for the binary FP bridge.
Every candidate is checked against the unchanged input adjacency relation and
the current live mask; the outer loop has input-size fuel on every input. -/
namespace HiddenCircuits.DH.Runtime.PruningModel
open SimpleGraph

inductive Kind where
  | twin (joined : Bool)
  | pendant
  deriving DecidableEq, Repr

structure Action (n : ℕ) where
  keep : Fin n
  removed : Fin n
  kind : Kind
  deriving DecidableEq, Repr

def twinTest {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (alive : Vector Bool n) (u v : Fin n) : Bool :=
  alive[u.val] && alive[v.val] && decide (u≠v) &&
    (List.finRange n).all (fun x=> !alive[x.val] || decide (x=u) || decide (x=v) ||
      decide (G.Adj v x ↔ G.Adj u x))

def pendantTest {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (alive : Vector Bool n) (u v : Fin n) : Bool :=
  alive[u.val] && alive[v.val] && decide (u≠v) && decide (G.Adj v u) &&
    (List.finRange n).all (fun x=> !alive[x.val] || !decide (G.Adj v x) || decide (x=u))

def tryPair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (alive : Vector Bool n) (u v : Fin n) : Option (Action n) :=
  if pendantTest G alive u v then some ⟨u,v,.pendant⟩
  else if twinTest G alive u v then some ⟨u,v,.twin (decide (G.Adj u v))⟩ else none

/-- Finite semantic conditions tested by the executable Boolean scan. -/
def Valid {n : ℕ} (G : SimpleGraph (Fin n)) (alive : Vector Bool n) (a : Action n) : Prop :=
  alive[a.keep.val]=true ∧ alive[a.removed.val]=true ∧ a.keep≠a.removed ∧
  match a.kind with
  | .pendant => G.Adj a.removed a.keep ∧ ∀x, alive[x.val]=true → G.Adj a.removed x → x=a.keep
  | .twin joined => (G.Adj a.keep a.removed ↔ joined=true) ∧
      ∀x, alive[x.val]=true → x≠a.keep → x≠a.removed → (G.Adj a.removed x ↔ G.Adj a.keep x)

lemma twinTest_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (alive : Vector Bool n) (u v : Fin n) :
    twinTest G alive u v=true ↔ alive[u.val]=true ∧ alive[v.val]=true ∧ u≠v ∧
      ∀x, alive[x.val]=true → x≠u → x≠v → (G.Adj v x ↔ G.Adj u x) := by
  simp only [twinTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_finRange,
    forall_const,Bool.or_eq_true]
  constructor
  · rintro ⟨⟨⟨hu,hv⟩,hne⟩,hall⟩
    refine ⟨hu,hv,hne,?_⟩
    intro x hx hxu hxv
    have h := hall x
    rcases h with ((h | h) | h) | h
    · simp [hx] at h
    · exact False.elim (hxu h)
    · exact False.elim (hxv h)
    · exact h
  · rintro ⟨hu,hv,hne,hall⟩
    refine ⟨⟨⟨hu,hv⟩,hne⟩,?_⟩
    intro x
    by_cases hx : alive[x.val]=true
    · by_cases hxu : x=u
      · exact Or.inl (Or.inl (Or.inr hxu))
      · by_cases hxv : x=v
        · exact Or.inl (Or.inr hxv)
        · exact Or.inr (hall x hx hxu hxv)
    · exact Or.inl (Or.inl (Or.inl (by simp [hx])))

lemma pendantTest_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (alive : Vector Bool n) (u v : Fin n) :
    pendantTest G alive u v=true ↔ Valid G alive ⟨u,v,.pendant⟩ := by
  simp only [pendantTest,Valid,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_finRange,
    forall_const,Bool.or_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨hu,hv⟩,hne⟩,ha⟩,hall⟩
    refine ⟨hu,hv,hne,ha,?_⟩
    intro x hx hvx
    rcases hall x with (h | h) | h
    · simp [hx] at h
    · exact False.elim ((by simpa using h : ¬G.Adj v x) hvx)
    · exact h
  · rintro ⟨hu,hv,hne,ha,hall⟩
    refine ⟨⟨⟨⟨hu,hv⟩,hne⟩,ha⟩,?_⟩
    intro x
    by_cases hx : alive[x.val]=true
    · by_cases hvx : G.Adj v x
      · exact Or.inr (hall x hx hvx)
      · exact Or.inl (Or.inr (by simp [hvx]))
    · exact Or.inl (Or.inl (by simp [hx]))

lemma tryPair_valid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (alive : Vector Bool n) (u v : Fin n) {a : Action n} (h : tryPair G alive u v=some a) :
    Valid G alive a := by
  unfold tryPair at h
  split at h
  · cases h;exact (pendantTest_iff G alive u v).mp ‹_›
  · split at h
    · cases h
      obtain ⟨hu,hv,hne,hext⟩ := (twinTest_iff G alive u v).mp ‹_›
      exact ⟨hu,hv,hne,by simp,hext⟩
    · contradiction

lemma tryPair_exists_of_pendant {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (alive : Vector Bool n) (u v : Fin n) (h : Valid G alive ⟨u,v,.pendant⟩) :
    ∃a, tryPair G alive u v=some a := by
  exact ⟨⟨u,v,.pendant⟩,by simp only [tryPair,(pendantTest_iff G alive u v).mpr h,↓reduceIte]⟩

lemma tryPair_exists_of_twin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (alive : Vector Bool n) (u v : Fin n)
    (h : alive[u.val]=true ∧ alive[v.val]=true ∧ u≠v ∧
      ∀x, alive[x.val]=true → x≠u → x≠v → (G.Adj v x ↔ G.Adj u x)) :
    ∃a, tryPair G alive u v=some a := by
  unfold tryPair
  split
  · exact ⟨_,rfl⟩
  · exact ⟨⟨u,v,.twin (decide (G.Adj u v))⟩,by simp only [(twinTest_iff G alive u v).mpr h,↓reduceIte]⟩

/-- Ordinary row-major exhaustive pair traversal; no structural witness is input. -/
def candidates (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun u=>(List.finRange n).map (fun v=>(u,v)))

def scan {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (alive : Vector Bool n) :
    List (Fin n × Fin n)→Option (Action n)
  | [] => none
  | (u,v)::pairs => (tryPair G alive u v).orElse (fun _=>scan G alive pairs)

def find {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (alive : Vector Bool n) : Option (Action n) :=
  scan G alive (candidates n)

lemma scan_valid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (alive : Vector Bool n) (pairs : List (Fin n × Fin n)) {a : Action n}
    (h : scan G alive pairs=some a) : Valid G alive a := by
  induction pairs with
  | nil => simp [scan] at h
  | cons uv pairs ih =>
    cases he : tryPair G alive uv.1 uv.2 with
    | none => exact ih (by simpa [scan,he] using h)
    | some b =>
      have hab : b=a := by simpa [scan,he] using h
      subst b
      exact tryPair_valid G alive uv.1 uv.2 he

lemma scan_none {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (alive : Vector Bool n) (pairs : List (Fin n × Fin n)) :
    scan G alive pairs=none ↔ ∀uv∈pairs, tryPair G alive uv.1 uv.2=none := by
  induction pairs with
  | nil => simp [scan]
  | cons uv pairs ih =>
    cases he : tryPair G alive uv.1 uv.2 <;> simp [scan,he,ih]

lemma find_valid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (alive : Vector Bool n) {a : Action n} (h : find G alive=some a) : Valid G alive a :=
  scan_valid G alive _ h

lemma find_none {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (alive : Vector Bool n) :
    find G alive=none ↔ ∀u v, tryPair G alive u v=none := by
  rw [find,scan_none]
  constructor
  · intro h u v
    exact h (u,v) (List.mem_flatMap.mpr ⟨u,List.mem_finRange u,List.mem_map.mpr ⟨v,List.mem_finRange v,rfl⟩⟩)
  · intro h uv huv;exact h uv.1 uv.2

@[simp] lemma candidates_length (n : ℕ) : (candidates n).length=n*n := by
  simp [candidates,List.length_flatMap,List.map_map]

def remove {n : ℕ} (alive : Vector Bool n) (a : Action n) : Vector Bool n := alive.set a.removed.val false

@[simp] lemma remove_alive {n : ℕ} (alive : Vector Bool n) (a : Action n) (v : Fin n) :
    (remove alive a)[v.val]=true ↔ alive[v.val]=true ∧ v≠a.removed := by
  by_cases hv : v=a.removed
  · subst v;simp [remove]
  · have hval : a.removed.val≠v.val := fun he=>hv (Fin.ext he).symm
    simp [remove,hv,hval]

structure Output (n : ℕ) where
  alive : Vector Bool n
  actions : List (Action n)

def run {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ℕ→Vector Bool n→Output n
  | 0,alive => ⟨alive,[]⟩
  | fuel+1,alive =>
      match find G alive with
      | none => ⟨alive,[]⟩
      | some a =>
          let q := run G fuel (remove alive a)
          ⟨q.alive,a::q.actions⟩

lemma run_length {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (fuel : ℕ) (alive : Vector Bool n) : (run G fuel alive).actions.length≤fuel := by
  induction fuel generalizing alive with
  | zero => simp [run]
  | succ fuel ih =>
    cases he : find G alive with
    | none => simp [run,he]
    | some a =>
      have h := ih (remove alive a)
      simp only [run,he,List.length_cons]
      omega

end HiddenCircuits.DH.Runtime.PruningModel
