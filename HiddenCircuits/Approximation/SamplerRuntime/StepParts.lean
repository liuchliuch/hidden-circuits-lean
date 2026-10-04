import HiddenCircuits.Approximation.SamplerRuntime.Proposal
import HiddenCircuits.Approximation.SamplerRuntime.SwitchSemantics
import HiddenCircuits.Approximation.SamplerRuntime.RuntimeBounds

/-! Physical holding-bit, two fixed-width indices, and one-shot range rejection. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Step
open Complexity Complexity.OracleBlock

abbrev unary (n : ℕ) : BitString := List.replicate n true
def first (n : ℕ) (tape : BitString) : ℕ := Proposal.index (Nat.size n) tape.tail
def second (n : ℕ) (tape : BitString) : ℕ := Proposal.index (Nat.size n) (tape.tail.drop (Nat.size n))
def width (n : ℕ) : ℕ := 1+(Nat.size n+Nat.size n)

def state (ls hs data : BitString) (n : ℕ) (tape : BitString) (i j : ℕ)
    (hold validI validJ : BitString) : Store 23 := fun r =>
  if r.val=0 then ls else if r.val=1 then hs else if r.val=2 then data else if r.val=3 then unary n
  else if r.val=4 then unary (Nat.size n) else if r.val=5 then tape else if r.val=6 then unary i
  else if r.val=7 then unary j else if r.val=8 then hold else if r.val=9 then validI else if r.val=10 then validJ else []
def firstMap : Fin 6 ↪ Fin 24 where
  toFun i := ![5,4,6,11,12,13] i
  inj' := by decide +kernel
def secondMap : Fin 6 ↪ Fin 24 where
  toFun i := ![5,4,7,11,12,13] i
  inj' := by decide +kernel
def rangeFirst : Fin 6 ↪ Fin 24 where
  toFun i := ![6,3,9,11,12,13] i
  inj' := by decide +kernel
def rangeSecond : Fin 6 ↪ Fin 24 where
  toFun i := ![7,3,10,11,12,13] i
  inj' := by decide +kernel
noncomputable def holdBlock : OracleBlock 23 := branchPop 5 (push 8 false) (push 8 false) (push 8 true)
noncomputable def prepare : OracleBlock 23 := seq holdBlock (seq (Proposal.on firstMap)
  (seq (Proposal.on secondMap) (seq (LengthLess.readLessOn rangeFirst) (LengthLess.readLessOn rangeSecond))))

lemma hold_executes (g : BitString → ℕ) (L H D : BitString) (n : ℕ) (tape : BitString) :
    holdBlock.Executes g (state L H D n tape 0 0 [] [] [])
      (state L H D n tape.tail 0 0 [tape.headD false] [] []) 3 := by
  cases tape with
  | nil =>
    apply branchPop_empty _ _ _ _ g rfl
    convert push_executes g (8:Fin 24) false _ using 1
    funext r;fin_cases r <;> rfl
  | cons b tape =>
    have hp : (push (8:Fin 24) b).Executes g
        (Function.update (state L H D n (b::tape) 0 0 [] [] []) 5 tape)
        (state L H D n tape 0 0 [b] [] []) 1 := by
      convert push_executes g (8:Fin 24) b (state L H D n tape 0 0 [] [] []) using 1
      · funext r;fin_cases r <;> rfl
      · funext r;fin_cases r <;> rfl
    cases b
    · exact branchPop_false _ _ _ _ g rfl hp
    · exact branchPop_true _ _ _ _ g rfl hp

lemma pow_size_bound (n : ℕ) : 2^Nat.size n≤2*(n+1) := by
  by_cases hz : Nat.size n=0
  · simp [hz];omega
  · have hp : 0<Nat.size n := Nat.pos_of_ne_zero hz
    have hh : 2^(Nat.size n-1)≤n := Nat.lt_size.mp (by omega)
    have he : Nat.size n=(Nat.size n-1)+1 := by omega
    rw [he,pow_succ]
    omega

theorem prepare_executes (g : BitString → ℕ) (L H D : BitString) (n : ℕ) (tape : BitString) :
    ∃t,prepare.Executes g (state L H D n tape 0 0 [] [] [])
      (state L H D n (tape.drop (width n)) (first n tape) (second n tape)
        [tape.headD false] [decide (first n tape<n)] [decide (second n tape<n)]) t ∧
      t≤1000*(n+1)^2 := by
  let m := Nat.size n
  let i := first n tape
  let j := second n tape
  let a := tape.tail.drop m
  let b := a.drop m
  let h := tape.headD false
  obtain ⟨c1,h1,b1⟩ := Proposal.on_executes firstMap g
    (state L H D n tape.tail 0 0 [h] [] []) (state L H D n a i 0 [h] [] []) tape.tail (unary m)
    (by funext r;fin_cases r <;> rfl)
    (by funext r;fin_cases r <;> simp [state,firstMap,Proposal.state,first,i,a,m])
    (by intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 0 rfl) | exact False.elim (hr 2 rfl))
  obtain ⟨c2,h2,b2⟩ := Proposal.on_executes secondMap g
    (state L H D n a i 0 [h] [] []) (state L H D n b i j [h] [] []) a (unary m)
    (by funext r;fin_cases r <;> rfl)
    (by funext r;fin_cases r <;> simp [state,secondMap,Proposal.state,second,j,b,a,m,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc])
    (by intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 0 rfl) | exact False.elim (hr 2 rfl))
  obtain ⟨c3,h3,b3⟩ := LengthLess.readLessOn_executes rangeFirst g (state L H D n b i j [h] [] []) (unary i) (unary n)
    (by funext r;fin_cases r <;> rfl)
  have e3 : Function.update (state L H D n b i j [h] [] []) (rangeFirst 2)
      [decide ((unary i).length<(unary n).length)]=state L H D n b i j [h] [decide (i<n)] [] := by
    funext r;fin_cases r <;> simp [state,rangeFirst]
  rw [e3] at h3
  obtain ⟨c4,h4,b4⟩ := LengthLess.readLessOn_executes rangeSecond g
    (state L H D n b i j [h] [decide (i<n)] []) (unary j) (unary n)
    (by funext r;fin_cases r <;> rfl)
  have e4 : Function.update (state L H D n b i j [h] [decide (i<n)] []) (rangeSecond 2)
      [decide ((unary j).length<(unary n).length)]=state L H D n b i j [h] [decide (i<n)] [decide (j<n)] := by
    funext r;fin_cases r <;> simp [state,rangeSecond]
  rw [e4] at h4
  have hb : b=tape.drop (width n) := by simp [b,a,m,width,List.drop_drop,TapeRead.tail_drop,Nat.add_assoc,Nat.add_comm]
  have hc := seq_executes _ _ g (hold_executes g L H D n tape)
    (seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)))
  refine ⟨3+(c1+(c2+(c3+c4+2)+2)+2)+2,?_,?_⟩
  · simpa only [hb] using hc
  · have hi : i<2^m := Proposal.index_lt _ _
    have hj : j<2^m := Proposal.index_lt _ _
    have hm : m≤n := Nat.size_le.mpr Nat.lt_two_pow_self
    have hp := pow_size_bound n
    have hmul := Nat.mul_le_mul (show m+1≤n+1 by omega) hp
    simp only [List.length_replicate] at b1 b2 b3 b4
    dsimp [m] at hmul
    nlinarith

lemma prepare_queryFree : prepare.QueryFree := seq_queryFree _ _
  (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) (push_queryFree _ _))
  (seq_queryFree _ _ (Proposal.on_queryFree _) (seq_queryFree _ _ (Proposal.on_queryFree _)
    (seq_queryFree _ _ (LengthLess.readLessOn_queryFree _) (LengthLess.readLessOn_queryFree _))))

end HiddenCircuits.Approximation.SamplerRuntime.Step
