import HiddenCircuits.Approximation.SamplerRuntime.Identity
import HiddenCircuits.Approximation.Initialization.MaskEnumerationSemantics
import HiddenCircuits.Approximation.SamplerRuntime.Output
import HiddenCircuits.Complexity.UnaryArithmetic

/-! Graph-only initialization of the fixed 52-stack
matching machine. The identity is only a partial-partner accumulator; it is
never returned as a matching without the subsequent residual search. -/
namespace HiddenCircuits.Approximation.Initialization.Startup
open Complexity Complexity.OracleBlock SamplerRuntime
set_option maxHeartbeats 2000000
abbrev unary (n : ℕ) : BitString := List.replicate n true

def work (N : ℕ) (payload mask source : BitString) (B : ℕ) (data : BitString)
    (L counter fuel : ℕ) : Store 51 := fun r =>
  if r.val=0 then unary N else if r.val=1 then payload else if r.val=2 then mask
  else if r.val=3 then source else if r.val=4 then unary B else if r.val=5 then data
  else if r.val=6 then unary L else if r.val=8 then unary counter
  else if r.val=51 then unary fuel else []

def entry (N : ℕ) (payload source : BitString) (k : ℕ) : Store 51 :=
  work N payload [] source k [] 0 0 0

def target (N : ℕ) (payload source : BitString) (k : ℕ) : Store 51 :=
  work N payload (unary N) source (2*N+k) (Output.witness (Equiv.refl (Fin N)))
    (N*N*(2*N+k)) 0 N

def identityPorts : Fin 6 ↪ Fin 52 where
  toFun i := ![5,8,9,10,11,12] i
  inj' := by decide +kernel

noncomputable def program : OracleBlock 51 :=
  seq (copyOn 0 2 9 (by decide) (by decide) (by decide))
  (seq (copyOn 0 51 9 (by decide) (by decide) (by decide))
  (seq (copyOn 0 5 9 (by decide) (by decide) (by decide))
  (seq (rename Identity.program identityPorts)
  (seq (copyOn 0 4 9 (by decide) (by decide) (by decide))
  (seq (copyOn 0 4 9 (by decide) (by decide) (by decide))
  (seq (copyOn 0 8 9 (by decide) (by decide) (by decide))
  (seq (repeatCopy 8 0 6 9 (by decide) (by decide) (by decide))
  (seq (copyOn 6 8 9 (by decide) (by decide) (by decide))
  (seq (clear 6) (repeatCopy 8 4 6 9 (by decide) (by decide) (by decide)))))))))))

lemma identity_eq (N : ℕ) : Identity.evaluate (unary N)=Output.witness (Equiv.refl (Fin N)) := by
  rw [Identity.evaluate_unary]
  rfl

lemma program_executes (g : BitString → ℕ) (N : ℕ) (payload source : BitString) (k : ℕ) :
    ∃ t,program.Executes g (entry N payload source k) (target N payload source k) t ∧
      t≤1000*(N+k+1)^4 := by
  let out := Output.witness (Equiv.refl (Fin N))
  let s0 := entry N payload source k
  let s1 := work N payload (unary N) source k [] 0 0 0
  let s2 := work N payload (unary N) source k [] 0 0 N
  let s3 := work N payload (unary N) source k (unary N) 0 0 N
  let s4 := work N payload (unary N) source k out 0 0 N
  let s5 := work N payload (unary N) source (N+k) out 0 0 N
  let s6 := work N payload (unary N) source (2*N+k) out 0 0 N
  let s7 := work N payload (unary N) source (2*N+k) out 0 N N
  let s8 := work N payload (unary N) source (2*N+k) out (N*N) 0 N
  let s9 := work N payload (unary N) source (2*N+k) out (N*N) (N*N) N
  let s10 := work N payload (unary N) source (2*N+k) out 0 (N*N) N
  have h1 : (copyOn (0:Fin 52) 2 9 (by decide) (by decide) (by decide)).Executes g s0 s1 (5*N+2) := by
    convert copyOn_executes g (0:Fin 52) 2 9 (by decide) (by decide) (by decide) s0 rfl using 1
    · funext i;fin_cases i <;> simp [s0,s1,entry,work]
    · simp [s0,entry,work]
  have h2 : (copyOn (0:Fin 52) 51 9 (by decide) (by decide) (by decide)).Executes g s1 s2 (5*N+2) := by
    convert copyOn_executes g (0:Fin 52) 51 9 (by decide) (by decide) (by decide) s1 rfl using 1
    · funext i;fin_cases i <;> simp [s1,s2,work]
    · simp [s1,work]
  have h3 : (copyOn (0:Fin 52) 5 9 (by decide) (by decide) (by decide)).Executes g s2 s3 (5*N+2) := by
    convert copyOn_executes g (0:Fin 52) 5 9 (by decide) (by decide) (by decide) s2 rfl using 1
    · funext i;fin_cases i <;> simp [s2,s3,work]
    · simp [s2,work]
  obtain ⟨a,ha,hab⟩ := Identity.program_executes g (unary N)
  rw [identity_eq] at ha
  have h4 : (rename Identity.program identityPorts).Executes g s3 s4 a := by
    apply rename_executes_to Identity.program identityPorts g ha
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl)
  have h5 : (copyOn (0:Fin 52) 4 9 (by decide) (by decide) (by decide)).Executes g s4 s5 (5*N+2) := by
    convert copyOn_executes g (0:Fin 52) 4 9 (by decide) (by decide) (by decide) s4 rfl using 1
    · funext i;fin_cases i <;> simp [s4,s5,work]
    · simp [s4,work]
  have h6 : (copyOn (0:Fin 52) 4 9 (by decide) (by decide) (by decide)).Executes g s5 s6 (5*N+2) := by
    convert copyOn_executes g (0:Fin 52) 4 9 (by decide) (by decide) (by decide) s5 rfl using 1
    · funext i;fin_cases i <;> simp [s5,s6,work,show 2*N+k=N+(N+k) by omega]
    · simp [s5,work]
  have h7 : (copyOn (0:Fin 52) 8 9 (by decide) (by decide) (by decide)).Executes g s6 s7 (5*N+2) := by
    convert copyOn_executes g (0:Fin 52) 8 9 (by decide) (by decide) (by decide) s6 rfl using 1
    · funext i;fin_cases i <;> simp [s6,s7,work]
    · simp [s6,work]
  have h8 : (repeatCopy (8:Fin 52) 0 6 9 (by decide) (by decide) (by decide)).Executes g s7 s8 ((5*N+4)*N+1) := by
    convert unaryMultiply_executes g (8:Fin 52) 0 6 9 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s7 N N rfl rfl rfl using 1
    funext i;fin_cases i <;> simp [s7,s8,work,workStore]
  have h9 : (copyOn (6:Fin 52) 8 9 (by decide) (by decide) (by decide)).Executes g s8 s9 (5*(N*N)+2) := by
    convert copyOn_executes g (6:Fin 52) 8 9 (by decide) (by decide) (by decide) s8 rfl using 1
    · funext i;fin_cases i <;> simp [s8,s9,work]
    · simp [s8,work]
  have h10 : (clear (6:Fin 52)).Executes g s9 s10 (N*N+1) := by
    convert clear_executes g (6:Fin 52) s9 using 1
    · funext i;fin_cases i <;> simp [s9,s10,work]
    · simp [s9,work]
  have h11 : (repeatCopy (8:Fin 52) 4 6 9 (by decide) (by decide) (by decide)).Executes g s10
      (target N payload source k) ((5*(2*N+k)+4)*(N*N)+1) := by
    convert unaryMultiply_executes g (8:Fin 52) 4 6 9 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s10 (N*N) (2*N+k) rfl rfl rfl using 1
    funext i;fin_cases i <;> simp [s10,target,out,work,workStore]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 (seq_executes _ _ g h6
    (seq_executes _ _ g h7 (seq_executes _ _ g h8 (seq_executes _ _ g h9
    (seq_executes _ _ g h10 h11))))))))),?_⟩
  simp only [List.length_replicate] at hab
  let S := N+k+1
  have hS : 1≤S := by dsimp [S];omega
  have hN : N≤S := by dsimp [S];omega
  have hN1 : N+1≤S := by dsimp [S];omega
  have ha' : a≤40*S^2 := hab.trans (Nat.mul_le_mul_left 40 (Nat.pow_le_pow_left hN1 2))
  have hn2 : N*N≤S^2 := by simpa [pow_two] using Nat.mul_le_mul hN hN
  have hw : 5*(2*N+k)+4≤14*S := by dsimp [S];omega
  have hbig : (5*(2*N+k)+4)*(N*N)≤14*S^3 := by
    calc
      _≤(14*S)*S^2 := Nat.mul_le_mul hw hn2
      _=14*S^3 := by ring
  have h1 : 1≤S^4 := Nat.one_le_pow 4 S hS
  have hs1 : S≤S^4 := by simpa using (Nat.pow_le_pow_right hS (show 1≤4 by omega))
  have hs2 : S^2≤S^4 := Nat.pow_le_pow_right hS (by omega)
  have hs3 : S^3≤S^4 := Nat.pow_le_pow_right hS (by omega)
  change _≤1000*S^4
  nlinarith

lemma program_queryFree : program.QueryFree := by
  unfold program
  repeat first | apply seq_queryFree | exact copyOn_queryFree _ _ _ _ _ _ |
    exact repeatCopy_queryFree _ _ _ _ _ _ _ | exact clear_queryFree _ |
    exact rename_queryFree _ _ Identity.program_queryFree

end HiddenCircuits.Approximation.Initialization.Startup
