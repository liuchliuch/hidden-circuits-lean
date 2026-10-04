import HiddenCircuits.Complexity.CNFQueryEncoding

/-! Scalar clone-vertex addresses and adjacency classification. These identities
connect the operational unary quotient/remainder decoder to the actual query. -/
namespace HiddenCircuits.Complexity.CNFCloneEmitter
open CNF

def bitIndex (b : Bool) : ℕ := if b then 1 else 0

lemma variable_address {n m a b : ℕ} (i : Fin n) (s : Bool) (k : Fin a) :
    (cloneVertexFinEquiv (n:=n) (m:=m) a b ⟨Sum.inl (i,s),k⟩).val =
      (2*i.val+bitIndex s)*a+k.val := by
  cases s <;> simp [cloneVertexFinEquiv,cloneVertexSplit,finProdFinEquiv,bitIndex,finTwoEquiv] <;> ring

lemma clause_address {n m a b : ℕ} (j : Fin m) (k : Fin b) :
    (cloneVertexFinEquiv (n:=n) (m:=m) a b ⟨Sum.inr j,k⟩).val = n*2*a+j.val*b+k.val := by
  simp [cloneVertexFinEquiv,cloneVertexSplit,finProdFinEquiv]
  ring

lemma variable_address_lt {n m a b : ℕ} (i : Fin n) (s : Bool) (k : Fin a) :
    (cloneVertexFinEquiv (n:=n) (m:=m) a b ⟨Sum.inl (i,s),k⟩).val<n*2*a := by
  rw [variable_address]
  have hi := i.isLt
  have hk := k.isLt
  cases s <;> simp only [bitIndex,Bool.false_eq_true,↓reduceIte] <;> nlinarith

lemma variable_division (i : ℕ) (s : Bool) {a : ℕ} (k : Fin a) :
    ((2*i+bitIndex s)*a+k.val)/a=2*i+bitIndex s := by
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by have := k.isLt;omega),Nat.div_eq_of_lt k.isLt,Nat.zero_add]

lemma variable_index (i : ℕ) (s : Bool) {a : ℕ} (k : Fin a) :
    (((2*i+bitIndex s)*a+k.val)/a)/2=i := by
  rw [variable_division]
  cases s <;> simp [bitIndex] <;> omega

lemma variable_sign (i : ℕ) (s : Bool) {a : ℕ} (k : Fin a) :
    decide ((((2*i+bitIndex s)*a+k.val)/a)%2=1)=s := by
  rw [variable_division]
  cases s <;> simp [bitIndex]

lemma clause_division (d j : ℕ) {b : ℕ} (k : Fin b) :
    ((d+j*b+k.val)-d)/b=j := by
  rw [show d+j*b+k.val-d=k.val+j*b by omega,
    Nat.add_mul_div_right _ _ (by have := k.isLt;omega),Nat.div_eq_of_lt k.isLt,Nat.zero_add]

inductive Descriptor
  | variable (index : ℕ) (sign : Bool)
  | clause (index : ℕ)
  deriving DecidableEq

def decodeVertex (cut a b index : ℕ) : Descriptor :=
  if index<cut then .variable ((index/a)/2) (decide ((index/a)%2=1)) else .clause ((index-cut)/b)

def baseDescriptor {n m : ℕ} : CNF.Vertex (n:=n) (m:=m) → Descriptor
  | .inl (i,s) => .variable i.val s
  | .inr j => .clause j.val

theorem decodeVertex_correct {n m a b : ℕ}
    (u : Cloning.Vertex (cloneMultiplicity (n:=n) (m:=m) a b)) :
    decodeVertex (n*2*a) a b (cloneVertexFinEquiv (n:=n) (m:=m) a b u).val = baseDescriptor u.1 := by
  rcases u with ⟨u,k⟩
  cases u with
  | inl v =>
    rcases v with ⟨i,s⟩
    rw [decodeVertex,if_pos (variable_address_lt (n:=n) (m:=m) (a:=a) (b:=b) i s k),variable_address]
    rw [variable_index,variable_sign]
    rfl
  | inr j =>
    rw [clause_address,decodeVertex,if_neg (by omega),clause_division]
    rfl

lemma variable_clone_adj {n m a b : ℕ} (F : CNF n m) (i j : Fin n) (s t : Bool) (k l : Fin a) :
    (F.cloneGraph a b).Adj ⟨Sum.inl (i,s),k⟩ ⟨Sum.inl (j,t),l⟩ ↔
      i=j ∧ (cloneVertexFinEquiv (n:=n) (m:=m) a b ⟨Sum.inl (i,s),k⟩).val≠(cloneVertexFinEquiv (n:=n) (m:=m) a b ⟨Sum.inl (j,t),l⟩).val := by
  have hne : (cloneVertexFinEquiv (n:=n) (m:=m) a b ⟨Sum.inl (i,s),k⟩).val≠
      (cloneVertexFinEquiv (n:=n) (m:=m) a b ⟨Sum.inl (j,t),l⟩).val ↔
      (⟨Sum.inl (i,s),k⟩ : Cloning.Vertex (cloneMultiplicity (n:=n) (m:=m) a b))≠⟨Sum.inl (j,t),l⟩ := by
    rw [ne_eq,ne_eq]
    exact not_congr (Fin.val_inj.trans (cloneVertexFinEquiv (n:=n) (m:=m) a b).injective.eq_iff)
  rw [hne]
  change (((Sum.inl (i,s) : CNF.Vertex (n:=n) (m:=m))=Sum.inl (j,t) ∧ _) ∨ (i=j ∧ s≠t)) ↔ _
  simp only [Sum.inl.injEq,Prod.mk.injEq]
  constructor
  · rintro (⟨⟨hi,hs⟩,hne⟩ | ⟨hi,hs⟩)
    · exact ⟨hi,hne⟩
    · refine ⟨hi,?_⟩
      intro he
      have hb := congrArg (fun u : Cloning.Vertex (cloneMultiplicity (n:=n) (m:=m) a b) => u.1) he
      exact hs (Prod.mk.inj (Sum.inl.inj hb)).2
  · rintro ⟨hi,hne⟩
    by_cases hs : s=t
    · exact Or.inl ⟨⟨hi,hs⟩,hne⟩
    · exact Or.inr ⟨hi,hs⟩

lemma clause_clone_adj {n m a b : ℕ} (F : CNF n m) (i j : Fin m) (k l : Fin b) :
    (F.cloneGraph a b).Adj ⟨Sum.inr i,k⟩ ⟨Sum.inr j,l⟩ ↔
      i=j ∧ (cloneVertexFinEquiv (n:=n) (m:=m) a b ⟨Sum.inr i,k⟩).val≠(cloneVertexFinEquiv (n:=n) (m:=m) a b ⟨Sum.inr j,l⟩).val := by
  change ((_ ∧ _) ∨ False) ↔ _
  simp only [or_false,Sum.inr.injEq]
  apply and_congr_right
  intro h
  rw [ne_eq,ne_eq]
  exact not_congr ((cloneVertexFinEquiv (n:=n) (m:=m) a b).injective.eq_iff.symm.trans Fin.val_inj.symm)

lemma cross_clone_adj {n m a b : ℕ} (F : CNF n m) (i : Fin n) (s : Bool) (j : Fin m) (k : Fin a) (l : Fin b) :
    (F.cloneGraph a b).Adj ⟨Sum.inl (i,s),k⟩ ⟨Sum.inr j,l⟩ ↔ (i,s)∈F.clause j := by
  change ((_ ∧ _) ∨ (i,s)∈F.clause j) ↔ _
  simp

end HiddenCircuits.Complexity.CNFCloneEmitter
