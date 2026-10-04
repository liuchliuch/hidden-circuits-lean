import HiddenCircuits.DH.CographAssembly

/-! The actual fuelled cotree interpreter. Runtime inputs are only head arrays,
initial weave bits, a vertex, and fuel. All recursive traversal work is counted. -/
namespace HiddenCircuits.DH.CographProgram
open CographStaircase LabeledCographTree

structure HeadData (n : ℕ) where
  normal : Vector (List (Fin n)) n
  complement : Vector (List (Fin n)) n
  choice : Vector Bool n

structure Result (n : ℕ) where
  tree : Option (LabeledCographTree (Fin n))
  accesses : ℕ
  allocations : ℕ

structure GatherResult (n : ℕ) where
  branches : Option (List (Bool × LabeledCographTree (Fin n)))
  accesses : ℕ
  allocations : ℕ

def mapCount {A B : Type*} (f : A → B) : List A → List B × ℕ
  | [] => ([],0)
  | x::xs => let q := mapCount f xs; (f x::q.1,q.2+2)

@[simp] lemma mapCount_values {A B : Type*} (f : A → B) (xs : List A) :
    (mapCount f xs).1=xs.map f := by induction xs <;> simp [mapCount, *]
@[simp] lemma mapCount_accesses {A B : Type*} (f : A → B) (xs : List A) :
    (mapCount f xs).2=2*xs.length := by induction xs <;> simp [mapCount, *] <;> omega

/-- Counted alternating list traversal. -/
def weaveCount {A B : Type*} (s : Bool) (as : List A) (bs : List B) : List (A ⊕ B) × ℕ :=
  match as,bs with
  | [],bs => mapCount Sum.inr bs
  | as,[] => mapCount Sum.inl as
  | a::as,b::bs => if s then
      let q := weaveCount false (a::as) bs
      (Sum.inr b::q.1,q.2+4)
    else
      let q := weaveCount true as (b::bs)
      (Sum.inl a::q.1,q.2+4)
termination_by as.length+bs.length

@[simp] lemma weaveCount_values {A B : Type*} (s : Bool) (as : List A) (bs : List B) :
    (weaveCount s as bs).1=weave s as bs := by
  fun_induction weaveCount s as bs <;> simp_all +zetaDelta [weaveCount,weave]

lemma weaveCount_accesses {A B : Type*} (s : Bool) (as : List A) (bs : List B) :
    (weaveCount s as bs).2≤4*(as.length+bs.length) := by
  fun_induction weaveCount s as bs <;> simp_all +zetaDelta [weaveCount] <;> omega

/-- Each child is evaluated exactly once, and its completed tree is shared in the
branch list. The counters include both option tests and the list constructors. -/
def gather {n : ℕ} (eval : Fin n → Result n) : List (Fin n ⊕ Fin n) → GatherResult n
  | [] => ⟨some [],0,0⟩
  | h::hs =>
      let c := eval (branchHead h)
      let q := gather eval hs
      ⟨(do let t ← c.tree; let ts ← q.branches; pure ((joined h,t)::ts)),
        c.accesses+q.accesses+6,c.allocations+q.allocations⟩

/-- Only a new binary node is allocated at each attachment; existing subtrees
are passed by reference through the recursion. -/
def attachCount {V : Type*} (t : LabeledCographTree V) :
    List (Bool × LabeledCographTree V) → LabeledCographTree V × ℕ × ℕ
  | [] => (t,0,0)
  | (b,u)::us =>
      let q := attachCount (.node b t u) us
      (q.1,q.2.1+3,q.2.2+1)

@[simp] lemma attachCount_tree {V : Type*} (t : LabeledCographTree V)
    (bs : List (Bool × LabeledCographTree V)) : (attachCount t bs).1=attach t bs := by
  induction bs generalizing t with
  | nil => rfl
  | cons p ps ih => rcases p with ⟨b,u⟩; simp [attachCount,attach,ih]

@[simp] lemma attachCount_resources {V : Type*} (t : LabeledCographTree V)
    (bs : List (Bool × LabeledCographTree V)) :
    (attachCount t bs).2.1=3*bs.length ∧ (attachCount t bs).2.2=bs.length := by
  induction bs generalizing t with
  | nil => simp [attachCount]
  | cons p ps ih => rcases p with ⟨b,u⟩; simp [attachCount,ih]; omega

/-- No pruning certificate, cotree, module, or graph-class proof is an input. -/
def run {n : ℕ} : ℕ → HeadData n → Fin n → Result n
  | 0,_,_ => ⟨none,1,0⟩
  | fuel+1,data,root =>
      let w := weaveCount data.choice[root.val] data.normal[root.val] data.complement[root.val]
      let g := gather (run fuel data) w.1
      match g.branches with
      | none => ⟨none,w.2+g.accesses+4,g.allocations⟩
      | some bs =>
          let a := attachCount (.leaf root) bs
          ⟨some a.1,w.2+g.accesses+a.2.1+5,g.allocations+a.2.2+1⟩

lemma gather_step {n : ℕ} (eval : Fin n → Result n) (hs : List (Fin n ⊕ Fin n))
    (child : (Fin n ⊕ Fin n) → LabeledCographTree (Fin n))
    (hc : ∀h∈hs, (eval (branchHead h)).tree=some (child h)) :
    (gather eval hs).branches=some (hs.map (fun h => (joined h,child h))) := by
  induction hs with
  | nil => rfl
  | cons h hs ih => simp [gather,hc h List.mem_cons_self,ih (fun k hk => hc k (List.mem_cons_of_mem _ hk))]

/-- One executable interpreter step equals the verified labeled spine assembly. -/
theorem run_step {n : ℕ} (fuel : ℕ) (data : HeadData n) (root : Fin n)
    (child : (Fin n ⊕ Fin n) → LabeledCographTree (Fin n))
    (hc : ∀h∈weave data.choice[root.val] data.normal[root.val] data.complement[root.val],
      (run fuel data (branchHead h)).tree=some (child h)) :
    (run (fuel+1) data root).tree=some
      (assembleCograph root data.choice[root.val] data.normal[root.val] data.complement[root.val] child) := by
  simp only [run,weaveCount_values,gather_step _ _ child hc,attachCount_tree,assembleCograph]

/-- Successful gathering accounts for exactly the leaves of its child trees. -/
lemma gather_resources {n : ℕ} (eval : Fin n → Result n) (hs : List (Fin n ⊕ Fin n))
    (hc : ∀h∈hs, ∀t, (eval (branchHead h)).tree=some t →
      (eval (branchHead h)).accesses+13≤18*t.leaves.length ∧
      (eval (branchHead h)).allocations+1=2*t.leaves.length)
    (bs : List (Bool × LabeledCographTree (Fin n))) (hb : (gather eval hs).branches=some bs) :
    bs.length=hs.length ∧
      (gather eval hs).accesses+7*hs.length≤18*(bs.map (fun p => p.2.leaves.length)).sum ∧
      (gather eval hs).allocations+hs.length=2*(bs.map (fun p => p.2.leaves.length)).sum := by
  induction hs generalizing bs with
  | nil => simp [gather] at hb; subst bs; simp [gather]
  | cons h hs ih =>
    cases htree : (eval (branchHead h)).tree with
    | none => simp [gather,htree] at hb
    | some t =>
      cases htail : (gather eval hs).branches with
      | none => simp [gather,htree,htail] at hb
      | some ts =>
        simp [gather,htree,htail] at hb
        subst bs
        have hh := hc h List.mem_cons_self t htree
        have ht := ih (fun k hk => hc k (List.mem_cons_of_mem _ hk)) ts htail
        simp only [gather,List.length_cons,List.map_cons,List.sum_cons]
        omega

lemma attach_leaf_length {n : ℕ} (root : Fin n) (bs : List (Bool × LabeledCographTree (Fin n))) :
    (attach (.leaf root) bs).leaves.length=1+(bs.map (fun p => p.2.leaves.length)).sum := by
  rw [attach_leaves]
  simp [leaves,List.length_flatMap,Nat.add_comm]

/-- Successful execution is linear in its actual output leaves, independent of
any graph assumption. Graph correctness later proves those leaves are precisely
the original distinct input vertices. -/
theorem run_resources {n : ℕ} (fuel : ℕ) (data : HeadData n) (root : Fin n)
    (t : LabeledCographTree (Fin n)) (ht : (run fuel data root).tree=some t) :
    (run fuel data root).accesses+13≤18*t.leaves.length ∧
      (run fuel data root).allocations+1=2*t.leaves.length := by
  induction fuel generalizing root t with
  | zero => simp [run] at ht
  | succ fuel ih =>
    let w := weaveCount data.choice[root.val] data.normal[root.val] data.complement[root.val]
    let g := gather (run fuel data) w.1
    have hrun : run (fuel+1) data root = match g.branches with
        | none => ⟨none,w.2+g.accesses+4,g.allocations⟩
        | some bs => ⟨some (attachCount (.leaf root) bs).1,
            w.2+g.accesses+(attachCount (.leaf root) bs).2.1+5,
            g.allocations+(attachCount (.leaf root) bs).2.2+1⟩ := rfl
    cases hg : g.branches with
    | none => rw [hrun,hg] at ht; contradiction
    | some bs =>
      rw [hrun,hg] at ht ⊢
      have ht' : (attachCount (.leaf root) bs).1=t := Option.some.inj ht
      have hc := gather_resources (run fuel data) w.1
        (fun h hh u hu => ih (branchHead h) u hu) bs hg
      have hw := weaveCount_accesses data.choice[root.val] data.normal[root.val] data.complement[root.val]
      have hwl : w.1.length=data.normal[root.val].length+data.complement[root.val].length := by simp [w]
      have ha := attachCount_resources (.leaf root) bs
      have hl := attach_leaf_length root bs
      rw [←attachCount_tree] at hl
      rw [ht'] at hl
      change (w.2+g.accesses+(attachCount (.leaf root) bs).2.1+5)+13≤18*t.leaves.length ∧
        (g.allocations+(attachCount (.leaf root) bs).2.2+1)+1=2*t.leaves.length
      change w.2≤4*(data.normal[root.val].length+data.complement[root.val].length) at hw
      change bs.length=w.1.length ∧ g.accesses+7*w.1.length≤18*(bs.map (fun p => p.2.leaves.length)).sum ∧
        g.allocations+w.1.length=2*(bs.map (fun p => p.2.leaves.length)).sum at hc
      omega

end HiddenCircuits.DH.CographProgram
