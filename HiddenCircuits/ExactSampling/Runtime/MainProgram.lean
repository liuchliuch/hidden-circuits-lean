import HiddenCircuits.ExactSampling.Runtime.WeightCountWidth
import HiddenCircuits.ExactSampling.Runtime.FairDrawTraces
import HiddenCircuits.ExactSampling.Runtime.UnrankLoop

/-! The complete exact DH sampler: physical binary counting and width setup,
unbounded fair-bit rejection, and the fixed binary self-reduction program.
The program itself has no hereditary/count/runtime certificate parameters. -/
namespace HiddenCircuits.ExactSampling.Runtime.Main
open Complexity OracleBlock BinaryArithmetic Approximation Approximation.FiniteChains
open DH DHWeights Rejection
open Polynomial
set_option maxHeartbeats 1800000

 def preparePorts : Fin 61↪Fin 66 := ⟨fun i => ⟨i.val,by omega⟩,by intro i j h;exact Fin.ext (congrArg (fun a : Fin 66 => a.val) h)⟩
 noncomputable def prepare : OracleBlock 65 := CountWidth.programOn preparePorts
 noncomputable def nonzero : FairCode 65 := .seq (.block (push 3 true))
   (.seq FairDraw.loop (.block Unrank.program))
 noncomputable def restore (b : Bool) : FairCode 65 := .seq (.block (push 4 b)) nonzero
 noncomputable def dispatch : FairCode 65 := .branchPop 4 (.block (clear 0)) (restore false) (restore true)
 noncomputable def program : FairCode 65 := .seq (.block prepare) dispatch

 def input (raw : BitString) : Store 65 := Function.update (fun _=>[]) 0 raw
 def output (bits : BitString) : Store 65 := Function.update (fun _=>[]) 0 bits

 noncomputable def sampledWord {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (x : Fin (count ⟨n,G⟩)) : BitString := true::DHPaths.encode (DHPaths.choices n G hG x)

 theorem prepare_executes (g : BitString→ℕ) (raw : BitString) :
    ∃t,prepare.Executes g (input raw) (FairDraw.ready raw (CountWidth.count raw) [] [] []) t ∧
      t≤CountWidth.timePolynomial.eval raw.length := by
  obtain ⟨t,ht,hb⟩ := CountWidth.programOn_executes preparePorts g (input raw) raw
    (by funext i;fin_cases i <;> rfl)
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext i;fin_cases i <;> simp [input,FairDraw.ready,FairDraw.state,preparePorts,CountWidth.width,
    Rejection.width,CountWidth.count_canonical]

 theorem nonzero_runs {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (hc : 0<count ⟨n,G⟩) (t : ℕ) (r : Trace (count ⟨n,G⟩) t) (x : Fin (count ⟨n,G⟩)) :
    ∃c,FairCode.Runs nonzero (FairDraw.ready (GraphInput.encode ⟨n,G⟩) (count ⟨n,G⟩) [] [] [])
      (output (sampledWord G hG x)) (FairDraw.fairReads hc t r x) c ∧
      c≤(t+1)*120*(Nat.size (count ⟨n,G⟩)+1)+Unrank.time.eval (GraphInput.encode ⟨n,G⟩).length+5 := by
  let raw := GraphInput.encode ⟨n,G⟩
  have hp : (push (3:Fin 66) true).Executes (fun _=>0)
      (FairDraw.ready raw (count ⟨n,G⟩) [] [] []) (FairDraw.ready raw (count ⟨n,G⟩) [] [true] []) 1 := by
    convert push_executes (fun _=>0) (3:Fin 66) true _ using 1
    funext i;fin_cases i <;> simp [FairDraw.ready,FairDraw.state]
  obtain ⟨a,ha,hab⟩ := FairDraw.loop_runs hc raw t r x
  obtain ⟨b,hb,hbb⟩ := Unrank.program_executes (fun _=>0) G hG x
  have hi : Unrank.store raw (Computability.encodeNat x.val) [] []=FairDraw.result raw x.val := by
    funext i;fin_cases i <;> rfl
  have ho : Unrank.store (sampledWord G hG x) [] [] []=output (sampledWord G hG x) := by
    funext i;fin_cases i <;> rfl
  change Unrank.program.Executes (fun _=>0) (Unrank.store raw (Computability.encodeNat x.val) [] [])
    (Unrank.store (sampledWord G hG x) [] [] []) b at hb
  rw [hi,ho] at hb
  have hh := FairCode.Runs.seq (FairCode.Runs.block hp) (FairCode.Runs.seq ha (FairCode.Runs.block hb))
  refine ⟨1+(a+b+2)+2,?_,?_⟩
  · simpa only [List.nil_append,List.append_nil] using hh
  · omega

 noncomputable def fixedTime : Polynomial ℕ := CountWidth.timePolynomial+Unrank.time+30

 theorem positive_runs {n : ℕ} (G : MatrixGraph n) (hG : DistanceHereditaryGraph G.graph)
    (hc : 0<count ⟨n,G⟩) (t : ℕ) (r : Trace (count ⟨n,G⟩) t) (x : Fin (count ⟨n,G⟩)) :
    ∃c,FairCode.Runs program (input (GraphInput.encode ⟨n,G⟩)) (output (sampledWord G hG x))
      (FairDraw.fairReads hc t r x) c ∧
      c≤fixedTime.eval (GraphInput.encode ⟨n,G⟩).length+(t+1)*120*(Nat.size (count ⟨n,G⟩)+1) := by
  let raw := GraphInput.encode ⟨n,G⟩
  obtain ⟨a,ha,hab⟩ := prepare_executes (fun _=>0) raw
  change prepare.Executes (fun _=>0) (input raw) (FairDraw.ready raw (count ⟨n,G⟩) [] [] []) a at ha
  obtain ⟨b,hb,hbb⟩ := nonzero_runs G hG hc t r x
  have hn : Computability.encodeNat (count ⟨n,G⟩)≠[] := by
    intro h
    have hh := congrArg BinaryArithmetic.value h
    simp only [value_encodeNat,value_nil] at hh
    omega
  cases hw : Computability.encodeNat (count ⟨n,G⟩) with
  | nil => exact (hn hw).elim
  | cons bit bits =>
    have hp : (push (4:Fin 66) bit).Executes (fun _=>0)
        (Function.update (FairDraw.ready raw (count ⟨n,G⟩) [] [] []) 4 bits)
        (FairDraw.ready raw (count ⟨n,G⟩) [] [] []) 1 := by
      convert push_executes (fun _=>0) (4:Fin 66) bit _ using 1
      funext i;fin_cases i <;> simp [FairDraw.ready,FairDraw.state,hw]
    have hr := FairCode.Runs.seq (FairCode.Runs.block hp) hb
    have hd : FairCode.Runs dispatch (FairDraw.ready raw (count ⟨n,G⟩) [] [] [])
        (output (sampledWord G hG x)) (FairDraw.fairReads hc t r x) (1+b+2+2) := by
      cases bit
      · exact FairCode.Runs.branchFalse (q:=(4:Fin 66)) (E:=.block (clear 0))
          (B:=restore false) (C:=restore true) (by exact hw) (by simpa using hr)
      · exact FairCode.Runs.branchTrue (q:=(4:Fin 66)) (E:=.block (clear 0))
          (B:=restore false) (C:=restore true) (by exact hw) (by simpa using hr)
    have hh := FairCode.Runs.seq (FairCode.Runs.block ha) hd
    refine ⟨a+(1+b+2+2)+2,?_,?_⟩
    · simpa using hh
    · simp only [fixedTime,eval_add,eval_ofNat]
      dsimp only [raw] at *
      omega

 theorem zero_runs (raw : BitString) (hz : CountWidth.count raw=0) :
    ∃c,FairCode.Runs program (input raw) (output []) [] c ∧
      c≤CountWidth.timePolynomial.eval raw.length+raw.length+5 := by
  obtain ⟨a,ha,hab⟩ := prepare_executes (fun _=>0) raw
  have he : FairDraw.ready raw (CountWidth.count raw) [] [] []=input raw := by
    funext i;fin_cases i <;> simp [FairDraw.ready,FairDraw.state,input,hz,width,Computability.encodeNat,Computability.encodeNum]
  rw [he] at ha
  have hc : (clear (0:Fin 66)).Executes (fun _=>0) (input raw) (output []) (raw.length+1) := by
    convert clear_executes (fun _=>0) (0:Fin 66) (input raw) using 1
    · funext i;fin_cases i <;> simp [input,output]
  have hd : FairCode.Runs dispatch (input raw) (output []) [] (raw.length+1+2) :=
    FairCode.Runs.branchEmpty (q:=(4:Fin 66)) (B:=restore false) (C:=restore true) rfl (FairCode.Runs.block hc)
  exact ⟨_,FairCode.Runs.seq (FairCode.Runs.block ha) hd,by omega⟩

 theorem malformed_runs (raw : BitString) (h : GraphInput.decode raw=none) :
    ∃c,FairCode.Runs program (input raw) (output []) [] c ∧
      c≤CountWidth.timePolynomial.eval raw.length+raw.length+5 := by
  apply zero_runs raw
  simp [CountWidth.count,DH.BinaryRuntime.malformed h,Computability.decodeNat,Computability.decodeNum]

 theorem queryFree : program.QueryFree := by
  have hu := Unrank.program_queryFree
  have hn : nonzero.QueryFree := ⟨push_queryFree _ _,FairDraw.loop_queryFree,hu⟩
  have hr (b : Bool) : (restore b).QueryFree := ⟨push_queryFree _ _,hn⟩
  exact ⟨CountWidth.programOn_queryFree _,clear_queryFree _,hr false,hr true⟩

end HiddenCircuits.ExactSampling.Runtime.Main
