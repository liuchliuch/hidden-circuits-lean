import HiddenCircuits.Complexity.GraphVerifier.MatchingPullback
import HiddenCircuits.Complexity.OracleRepeat

/-! A literal preserve-or-reject graph compiler.  The recognizer is an actual
finite query-free bit-stack block with a separately proved polynomial execution
bound.  The wrapper physically saves the original input before running that
block; acceptance copies those exact bytes back, and rejection emits the fixed
one-vertex graph.  No graph operation is a machine primitive. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionGate
open Complexity OracleBlock Polynomial
variable {k : ℕ}

/-- A fixed odd graph, used to make every rejected instance count zero. -/
def rejectedGraph : GraphInput := ⟨1,⟨fun _ _ => false,by intros;rfl,by intros;rfl⟩⟩

lemma rejectedGraph_bits : rejectedGraph.encode = [true,true,false,false] := by decide

lemma rejectedGraph_count : perfectMatchingCount rejectedGraph.2.graph = 0 := by
  letI : IsEmpty (PerfectMatching rejectedGraph.2.graph) := ⟨fun M => by
    obtain ⟨v,hv,_⟩ := M.property.1 (M.property.2 (0 : Fin 1))
    exact Bool.false_ne_true (M.val.adj_sub hv)⟩
  exact Fintype.card_eq_zero

/-- Preserve the exact raw input on acceptance, including its labels and byte
order; emit the fixed odd graph on rejection. -/
def graphGate (accept : BitString → Bool) (xs : BitString) : BitString :=
  if accept xs then xs else rejectedGraph.encode

lemma graphGate_count (accept : BitString → Bool) (xs : BitString) :
    GraphInput.perfectMatchingProblem (graphGate accept xs) =
      if accept xs then GraphInput.perfectMatchingProblem xs else 0 := by
  cases h : accept xs <;>
    simp [graphGate,h,GraphInput.perfectMatchingProblem,rejectedGraph_count]

noncomputable def size : Polynomial ℕ := X+4

lemma graphGate_size (accept : BitString → Bool) (xs : BitString) :
    (graphGate accept xs).length ≤ size.eval xs.length := by
  cases h : accept xs <;> simp [graphGate,h,size,rejectedGraph_bits]

def saved : Fin (k+2+1) := ⟨k+1,by omega⟩
def temporary : Fin (k+2+1) := ⟨k+2,by omega⟩

lemma saved_ne_zero : saved (k:=k) ≠ 0 := by intro h;have := congrArg Fin.val h;simp [saved] at this
lemma temporary_ne_zero : temporary (k:=k) ≠ 0 := by intro h;have := congrArg Fin.val h;simp [temporary] at this
lemma saved_ne_temporary : saved (k:=k) ≠ temporary := by intro h;have := congrArg Fin.val h;simp [saved,temporary] at this

noncomputable def preserve : OracleBlock (k+2) :=
  copyOn 0 saved temporary (Ne.symm saved_ne_zero) (Ne.symm temporary_ne_zero) saved_ne_temporary
noncomputable def restore : OracleBlock (k+2) :=
  copyOn saved 0 temporary saved_ne_zero saved_ne_temporary (Ne.symm temporary_ne_zero)
noncomputable def reject : OracleBlock (k+2) := prepend 0 rejectedGraph.encode
noncomputable def finish : OracleBlock (k+2) := branchPop 0 reject reject restore

/-- The concrete wrapper introduces only two fresh stacks, performs a real input
copy, executes the supplied program through instruction renaming, then branches
on its singleton Boolean output. -/
noncomputable def program (B : OracleBlock k) : OracleBlock (k+2) :=
  seq preserve (seq (resize B (by omega)) finish)

noncomputable def time (p : Polynomial ℕ) : Polynomial ℕ := p+10*X+25

lemma program_queryFree (B : OracleBlock k) (hB : B.QueryFree) : (program B).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ hB)
      (branchPop_queryFree _ _ _ _ (prepend_queryFree _ _) (prepend_queryFree _ _)
        (copyOn_queryFree _ _ _ _ _ _)))

lemma embedding_ne_saved (i : Fin (k+1)) :
    resizeEmbedding (show k≤k+2 by omega) i ≠ saved := by
  intro h
  have he := congrArg Fin.val h
  change i.val=k+1 at he
  omega

lemma embedding_ne_temporary (i : Fin (k+1)) :
    resizeEmbedding (show k≤k+2 by omega) i ≠ temporary := by
  intro h
  have he := congrArg Fin.val h
  change i.val=k+2 at he
  omega

/-- Exact operational compilation from an actual Boolean recognizer.  Its work
tapes may be dirty, and the bound is in the original input length. -/
theorem program_executes (B : OracleBlock k) (accept : BitString → Bool)
    (p : Polynomial ℕ) (g : BitString → ℕ)
    (hrun : ∀ xs, ∃ s c,
      B.Executes g (Function.update (fun _=>[]) 0 xs) s c ∧
      s 0=Computability.encodeBool (accept xs) ∧ c≤p.eval xs.length)
    (xs : BitString) :
    ∃ s c, (program B).Executes g (Function.update (fun _=>[]) 0 xs) s c ∧
      s 0=graphGate accept xs ∧ c≤(time p).eval xs.length := by
  let initial : Store (k+2) := Function.update (fun _=>[]) 0 xs
  let copied : Store (k+2) := Function.update initial saved xs
  let φ := resizeEmbedding (show k≤k+2 by omega)
  have hs0 : saved (k:=k) ≠ 0 := saved_ne_zero
  have ht0 : temporary (k:=k) ≠ 0 := temporary_ne_zero
  have hst : saved (k:=k) ≠ temporary := saved_ne_temporary
  have hcopy : (preserve (k:=k)).Executes g initial copied (5*xs.length+2) := by
    simpa [preserve,initial,copied,hs0,ht0] using
      copyOn_executes g (0 : Fin (k+2+1)) saved temporary hs0.symm ht0.symm hst initial
        (by simp [initial,ht0])
  have hrestrict : copied ∘ φ = Function.update (fun _ : Fin (k+1)=>[]) 0 xs := by
    funext i
    have hsaved := embedding_ne_saved i
    have hi : φ i=0 ↔ i=0 := by
      change resizeEmbedding (show k≤k+2 by omega) i=0 ↔ i=0
      rw [←resizeEmbedding_zero (show k≤k+2 by omega)]
      exact φ.injective.eq_iff
    simp [copied,initial,Function.comp_def,φ,hsaved,Function.update_apply,hi]
  obtain ⟨s,c,hc,ho,hbound⟩ := hrun xs
  let recognized := install φ copied s
  have hrecognize : (resize B (show k≤k+2 by omega)).Executes g copied recognized c :=
    rename_executes B φ g copied (by rw [hrestrict];exact hc)
  have houtput : recognized 0=[accept xs] := by
    have hi := install_image φ copied s 0
    simpa [φ,Computability.encodeBool,ho] using hi
  have hsaved : recognized saved=xs := by
    rw [show recognized saved=install φ copied s saved from rfl,
      install_off φ copied s saved embedding_ne_saved]
    simp [copied]
  have htemp : recognized temporary=[] := by
    rw [show recognized temporary=install φ copied s temporary from rfl,
      install_off φ copied s temporary embedding_ne_temporary]
    simp [copied,initial,hst.symm,ht0]
  let consumed := Function.update recognized 0 []
  have hfinish : ∃ t d,(finish (k:=k)).Executes g recognized t d ∧
      t 0=graphGate accept xs ∧ d≤5*xs.length+15 := by
    cases ha : accept xs with
    | false =>
      have hp := prepend_executes g (0 : Fin (k+2+1)) rejectedGraph.encode consumed
      have hb := branchPop_false (0 : Fin (k+2+1)) reject reject restore g
        (rest:=[]) (by simpa [ha] using houtput) hp
      refine ⟨_,3*rejectedGraph.encode.length+1+2,hb,?_,?_⟩
      · simp [consumed,graphGate,ha]
      · simp [rejectedGraph_bits]
    | true =>
      have hp := copyOn_executes g saved (0 : Fin (k+2+1)) temporary hs0 hst ht0.symm consumed
        (by simp [consumed,ht0,htemp])
      have hb := branchPop_true (0 : Fin (k+2+1)) reject reject restore g
        (rest:=[]) (by simpa [ha] using houtput) hp
      refine ⟨_,5*(consumed saved).length+2+2,hb,?_,?_⟩
      · simp [consumed,hs0,hsaved,graphGate,ha]
      · simp [consumed,hs0,hsaved]
  obtain ⟨t,d,hd,hto,hdt⟩ := hfinish
  refine ⟨t,5*xs.length+2+(c+d+2)+2,
    seq_executes _ _ g hcopy (seq_executes _ _ g hrecognize hd),hto,?_⟩
  simp only [time,eval_add,eval_mul,eval_ofNat,eval_X]
  omega

/-- The physical gate feeds the existing certified perfect-matching verifier,
so the zero-on-reject count is #P whenever the recognizer has a concrete charged
polynomial-time block. -/
theorem sharpP_of_recognizer (B : OracleBlock k) (hB : B.QueryFree)
    (accept : BitString → Bool) (p : Polynomial ℕ)
    (hrun : ∀ xs, ∃ s c,
      B.Executes (fun _=>0) (Function.update (fun _=>[]) 0 xs) s c ∧
      s 0=Computability.encodeBool (accept xs) ∧ c≤p.eval xs.length) :
    SharpP (fun xs => if accept xs then GraphInput.perfectMatchingProblem xs else 0) := by
  have h := GraphVerifier.MatchingPullback.sharpP_of_graph_compiler (program B)
    (program_queryFree B hB) (graphGate accept) (time p) size
    (program_executes B accept p (fun _=>0) hrun) (graphGate_size accept)
  have he : GraphInput.perfectMatchingProblem ∘ graphGate accept =
      (fun xs => if accept xs then GraphInput.perfectMatchingProblem xs else 0) := by
    funext xs
    exact graphGate_count accept xs
  rwa [he] at h

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionGate
