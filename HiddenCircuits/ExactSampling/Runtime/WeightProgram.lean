import HiddenCircuits.ExactSampling.Runtime.WeightLoop

/-! Complete canonical graph-input compiler to the array of residual weights.
Both boundary stacks are preserved/produced exactly and all scratch is empty. -/
namespace HiddenCircuits.ExactSampling.Runtime.WeightCompiler
open Complexity OracleBlock BinaryArithmetic GraphVerifier GraphVerifier.Runtime
open Approximation.SelfReduction.Runtime
set_option maxHeartbeats 1800000

def parsePorts : Fin 4 ↪ Fin 60 := ⟨fun i => ![5,3,7,8] i,by decide +kernel⟩
noncomputable def parseGraph : OracleBlock 59 := unpairOn parsePorts
noncomputable def prepare : OracleBlock 59 := seq copyGraph
  (seq parseGraph (seq (clear 8) (moveOn 5 4 7 (by decide) (by decide) (by decide))))
noncomputable def finish : OracleBlock 59 := seq (clear 2)
  (seq (clear 4) (reverseOn 6 1 (by decide)))
noncomputable def program : OracleBlock 59 := seq prepare (seq loop finish)

def output (G : GraphInput) : BitString := match G with
  | ⟨0,_⟩ => []
  | ⟨N+1,G⟩ => encodeBitList (List.ofFn (weightWord G))

lemma prepare_executes (g : BitString→ℕ) {n : ℕ} (G : MatrixGraph n) :
    ∃t,prepare.Executes g (store (GraphInput.encode ⟨n,G⟩) [])
      (state (GraphInput.encode ⟨n,G⟩) [] [] (unary n) G.bits [] []) t ∧
      t≤20*((GraphInput.encode ⟨n,G⟩).length+1)^2 := by
  let raw := GraphInput.encode ⟨n,G⟩
  let parsed := state raw [] [] (unary n) [] G.bits []
  let flagged := Function.update parsed (8:Fin 60) [true]
  have hp : parseGraph.Executes g (state raw [] [] [] [] raw []) flagged
      (parseCost raw+2*n+1) := by
    have hh := unpairOn_executes parsePorts g (state raw [] [] [] [] raw []) flagged raw
    simp only [raw,GraphInput.encode,parse_pair,List.length_replicate] at hh ⊢
    apply hh
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have h3 : i.val≠3 := by intro h;apply hi 1;apply Fin.ext;exact h.symm
      have h5 : i.val≠5 := by intro h;apply hi 0;apply Fin.ext;exact h.symm
      have h8 : i≠(8:Fin 60) := by intro h;apply hi 3;exact h.symm
      simp [flagged,parsed,state,h3,h5,h8,raw,GraphInput.encode]
  have hc : (clear (8:Fin 60)).Executes g flagged parsed 2 := by
    convert clear_executes g (8:Fin 60) flagged using 1
    · funext i;fin_cases i <;> simp [flagged,parsed,state]
  have hm : (moveOn (5:Fin 60) 4 7 (by decide) (by decide) (by decide)).Executes g
      parsed (state raw [] [] (unary n) G.bits [] []) (6*(n*n)+5) := by
    convert moveOn_executes g (5:Fin 60) 4 7 (by decide) (by decide) (by decide) parsed rfl using 1
    · funext i;fin_cases i <;> simp [parsed,state]
    · simp [parsed,state]
  refine ⟨_,seq_executes _ _ g (copyGraph_executes g raw [] [] [] [] [])
    (seq_executes _ _ g hp (seq_executes _ _ g hc hm)),?_⟩
  have hu := unpair_cost_bound raw
  have hl : raw.length=2*n+n*n+1 := by simp [raw,GraphInput.encode]
  simp only [raw,GraphInput.encode,parse_pair,List.length_replicate] at hu
  change parseCost raw+2*n+1≤3*raw.length+4 at hu
  change 5*raw.length+2+((parseCost raw+2*n+1)+(2+(6*(n*n)+5)+2)+2)+2≤20*(raw.length+1)^2
  nlinarith

lemma finish_executes (g : BitString→ℕ) (raw index data acc : BitString) :
    finish.Executes g (state raw [] index [] data [] acc)
      (store raw acc.reverse) (index.length+data.length+2*acc.length+7) := by
  have h1 : (clear (2:Fin 60)).Executes g (state raw [] index [] data [] acc)
      (state raw [] [] [] data [] acc) (index.length+1) := by
    convert clear_executes g (2:Fin 60) (state raw [] index [] data [] acc) using 1
    funext i;fin_cases i <;> simp [state]
  have h2 : (clear (4:Fin 60)).Executes g (state raw [] [] [] data [] acc)
      (state raw [] [] [] [] [] acc) (data.length+1) := by
    convert clear_executes g (4:Fin 60) (state raw [] [] [] data [] acc) using 1
    funext i;fin_cases i <;> simp [state]
  have h3 : (reverseOn (6:Fin 60) 1 (by decide)).Executes g (state raw [] [] [] [] [] acc)
      (store raw acc.reverse) (2*acc.length+1) := by
    convert reverseOn_executes g (6:Fin 60) 1 (by decide) (state raw [] [] [] [] [] acc) using 1
    funext i;fin_cases i <;> simp [state,store]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1 <;> omega

noncomputable def programBound (L : ℕ) : ℕ :=
  20*(L+1)^2+L*(bodyBound L+2)+1+2*(L+L*(bodyBound L+2)+1)+2*L+11

lemma program_executes_positive (g : BitString→ℕ) {N : ℕ} (G : MatrixGraph (N+1)) :
    ∃t,program.Executes g (store (GraphInput.encode ⟨N+1,G⟩) [])
      (store (GraphInput.encode ⟨N+1,G⟩) (encodeBitList (List.ofFn (weightWord G)))) t ∧
      t≤programBound (GraphInput.encode ⟨N+1,G⟩).length := by
  obtain ⟨a,ha,hab⟩ := prepare_executes g G
  obtain ⟨b,hb,hbb⟩ := loop_executes g G []
  have hc := finish_executes g (GraphInput.encode ⟨N+1,G⟩) (unary (N+1))
    (G.bits.drop (N+1)) (encodeBitList (List.ofFn (weightWord G))).reverse
  simp only [List.reverse_reverse] at hc
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb hc),?_⟩
  have hn := GraphInput.vertices_le_length ⟨N+1,G⟩
  have hd : (G.bits.drop (N+1)).length≤(GraphInput.encode ⟨N+1,G⟩).length := by
    simp [GraphInput.encode];omega
  have hi : ∀q : Fin 60,(state (GraphInput.encode ⟨N+1,G⟩) [] [] (unary (N+1)) G.bits [] [] q).length≤
      (GraphInput.encode ⟨N+1,G⟩).length := by
    intro q;fin_cases q <;> simp [state,GraphInput.encode] <;> omega
  have hs := hb.stack_bound hi (6:Fin 60)
  change (encodeBitList (List.ofFn (weightWord G))).reverse.length≤(GraphInput.encode ⟨N+1,G⟩).length+b at hs
  have hm := Nat.mul_le_mul_right (bodyBound (GraphInput.encode ⟨N+1,G⟩).length+2) hn
  dsimp only at hm hn
  simp only [List.length_replicate] at *
  unfold programBound
  omega

lemma program_executes_zero (g : BitString→ℕ) (G : MatrixGraph 0) :
    ∃t,program.Executes g (store (GraphInput.encode ⟨0,G⟩) [])
      (store (GraphInput.encode ⟨0,G⟩) []) t ∧
      t≤programBound (GraphInput.encode ⟨0,G⟩).length := by
  obtain ⟨a,ha,hab⟩ := prepare_executes g G
  have hg : G.bits=[] := List.eq_nil_of_length_eq_zero (by simp)
  rw [hg] at ha
  have hb := whilePop_executes (3:Fin 60) body body g
    (WhileExecution.empty (state (GraphInput.encode ⟨0,G⟩) [] [] [] [] [] []) rfl)
  have hc := finish_executes g (GraphInput.encode ⟨0,G⟩) [] [] []
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb hc),?_⟩
  unfold programBound
  simp only [List.length_nil] at *
  omega

theorem program_executes (g : BitString→ℕ) (G : GraphInput) :
    ∃t,program.Executes g (store G.encode []) (store G.encode (output G)) t ∧
      t≤programBound G.encode.length := by
  obtain ⟨n,G⟩ := G
  cases n with
  | zero => exact program_executes_zero g G
  | succ N => exact program_executes_positive g G

lemma prepare_queryFree : prepare.QueryFree := seq_queryFree _ _ copyGraph_queryFree
  (seq_queryFree _ _ (unpairOn_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (moveOn_queryFree _ _ _ _ _ _)))
lemma finish_queryFree : finish.QueryFree := seq_queryFree _ _ (clear_queryFree _)
  (seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _))
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ prepare_queryFree
  (seq_queryFree _ _ loop_queryFree finish_queryFree)

open Polynomial
noncomputable def countPolynomial : Polynomial ℕ := 5*X+GraphResidual.timePolynomial+DH.BinaryRuntime.time+6
noncomputable def bodyPolynomial : Polynomial ℕ := countPolynomial+6*(X+DH.BinaryRuntime.time)+15
noncomputable def timePolynomial : Polynomial ℕ :=
  20*(X+1)^2+X*(bodyPolynomial+2)+1+2*(X+X*(bodyPolynomial+2)+1)+2*X+11

@[simp] lemma countPolynomial_eval (L : ℕ) : countPolynomial.eval L=countBound L := by
  simp [countPolynomial,countBound]
@[simp] lemma bodyPolynomial_eval (L : ℕ) : bodyPolynomial.eval L=bodyBound L := by
  simp [bodyPolynomial,bodyBound]
@[simp] lemma timePolynomial_eval (L : ℕ) : timePolynomial.eval L=programBound L := by
  simp [timePolynomial,programBound]

/-- Uniform polynomial bit time in the original canonical graph encoding. -/
theorem program_inputLengthBound (g : BitString→ℕ) (G : GraphInput) :
    ∃t,program.Executes g (store G.encode []) (store G.encode (output G)) t ∧
      t≤timePolynomial.eval G.encode.length := by
  simpa only [timePolynomial_eval] using program_executes g G

end HiddenCircuits.ExactSampling.Runtime.WeightCompiler
