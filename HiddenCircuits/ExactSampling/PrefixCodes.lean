import HiddenCircuits.ExactSampling.Runtime.FairDrawTraces

/-! Prefix-freeness and injectivity of the actual fair-bit words consumed by
complete rejection experiments. This justifies adding their cylinder weights. -/
namespace HiddenCircuits.ExactSampling
open Complexity Approximation Approximation.FiniteChains Rejection

 theorem flatten_prefix_fixed (w : ℕ) (hw : 0<w) {xs ys : List BitString}
    (hx : ∀x∈xs,x.length=w) (hy : ∀y∈ys,y.length=w)
    (hp : xs.flatten.IsPrefix ys.flatten) : xs.IsPrefix ys := by
  induction xs generalizing ys with
  | nil => exact List.nil_prefix
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hl := hp.length_le
      have hxl := hx x (by simp)
      simp only [List.flatten_cons,List.length_append,List.flatten_nil,List.length_nil] at hl
      omega
    | cons y ys =>
      have hxl := hx x (by simp)
      have hyl := hy y (by simp)
      obtain ⟨tail,he⟩ := hp
      simp only [List.flatten_cons,List.append_assoc] at he
      have ht := congrArg (List.take w) he
      have hxt : (x++(xs.flatten++tail)).take w=x := by
        simpa only [hxl] using (List.take_left (l₁:=x) (l₂:=xs.flatten++tail))
      have hyt : (y++ys.flatten).take w=y := by
        simpa only [hyl] using (List.take_left (l₁:=y) (l₂:=ys.flatten))
      have hexy : x=y := by rw [hxt,hyt] at ht;exact ht
      subst y
      have he' : xs.flatten++tail=ys.flatten := List.append_cancel_left he
      exact List.cons_prefix_cons.mpr ⟨rfl,ih
        (fun z hz => hx z (List.mem_cons_of_mem _ hz))
        (fun z hz => hy z (List.mem_cons_of_mem _ hz)) ⟨tail,he'⟩⟩

 theorem map_prefix_injective {α β : Type*} (f : α→β) (hf : Function.Injective f)
    {xs ys : List α} (hp : (xs.map f).IsPrefix (ys.map f)) : xs.IsPrefix ys := by
  induction xs generalizing ys with
  | nil => exact List.nil_prefix
  | cons x xs ih =>
    cases ys with
    | nil => simpa using hp
    | cons y ys =>
      obtain ⟨h,ht⟩ := List.cons_prefix_cons.mp hp
      have he := hf h
      subst y
      exact List.cons_prefix_cons.mpr ⟨rfl,ih ht⟩

 def blockWord {n : ℕ} (r : CoinTape n) : BitString := (List.ofFn r).reverse

 theorem blockWord_injective (n : ℕ) : Function.Injective (blockWord (n:=n)) := by
  intro x y h
  exact List.ofFn_injective (List.reverse_injective h)

 theorem fairReads_blocks {n : ℕ} (hn : 0<n) (t : ℕ) (r : Trace n t) (i : Fin n) :
    Runtime.FairDraw.fairReads hn t r i=((traceBlocks hn t r i).map blockWord).flatten := by
  simp [Runtime.FairDraw.fairReads,traceBlocks,List.map_ofFn,Function.comp_def,blockWord]

 theorem trace_zero_of_width_zero {n : ℕ} (hn : 0<n) (hw : width n=0) (t : ℕ) (r : Trace n t) : t=0 := by
  have hn1 : n=1 := by have hh := covered hn;simp [capacity,hw] at hh;omega
  subst n
  cases t with
  | zero => rfl
  | succ t =>
    have h := (r 0).property
    rw [attempt_one] at h
    contradiction

 theorem fairReads_prefix {n : ℕ} (hn : 0<n) (t s : ℕ) (r : Trace n t) (q : Trace n s) (i j : Fin n)
    (hp : (Runtime.FairDraw.fairReads hn t r i).IsPrefix (Runtime.FairDraw.fairReads hn s q j)) :
    t=s ∧i=j ∧traceBlocks hn t r i=traceBlocks hn s q j := by
  by_cases hw : width n=0
  · have ht := trace_zero_of_width_zero hn hw t r
    have hs := trace_zero_of_width_zero hn hw s q
    subst t;subst s
    have hn1 : n=1 := by have hh := covered hn;simp [capacity,hw] at hh;omega
    have hij : i=j := by apply Fin.ext;have hi:=i.isLt;have hj:=j.isLt;omega
    subst j
    exact ⟨rfl,rfl,by simp [traceBlocks]⟩
  · rw [fairReads_blocks,fairReads_blocks] at hp
    have hlen (xs : List (CoinTape (width n))) : ∀w∈xs.map blockWord,w.length=width n := by
      intro w hw
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
      simp [blockWord]
    have hp' := flatten_prefix_fixed (width n) (by omega) (hlen _) (hlen _) hp
    have hp'' := map_prefix_injective blockWord (blockWord_injective _) hp'
    obtain ⟨he,hij⟩ := (traceBlocks_run hn t r i).prefix_free (traceBlocks_run hn s q j) hp''
    have hl := congrArg List.length he
    simp only [traceBlocks_length] at hl
    exact ⟨by omega,hij,he⟩

/-- A countable family of complete experiments, encoded as actual consumed
fair-bit prefixes. There is exactly one word for each experiment. -/
def CodedExperiment (n : ℕ) := Σt : ℕ,Trace n t × Fin n

 def experimentWord {n : ℕ} (hn : 0<n) (r : CodedExperiment n) : BitString :=
  Runtime.FairDraw.fairReads hn r.1 r.2.1 r.2.2

 theorem experimentWord_injective {n : ℕ} (hn : 0<n) : Function.Injective (experimentWord hn) := by
  rintro ⟨t,r,i⟩ ⟨s,q,j⟩ h
  obtain ⟨ht,hij,hb⟩ := fairReads_prefix hn t s r q i j (by rw [show Runtime.FairDraw.fairReads hn t r i=Runtime.FairDraw.fairReads hn s q j from h])
  subst s;subst j
  have hr := traceBlocks_injective hn t i hb
  subst q
  rfl

 theorem experimentWord_prefix_free {n : ℕ} (hn : 0<n) (r q : CodedExperiment n)
    (hp : (experimentWord hn r).IsPrefix (experimentWord hn q)) : r=q := by
  rcases r with ⟨t,r,i⟩
  rcases q with ⟨s,q,j⟩
  obtain ⟨ht,hij,hb⟩ := fairReads_prefix hn t s r q i j hp
  subst s;subst j
  have hr := traceBlocks_injective hn t i hb
  subst q
  rfl

end HiddenCircuits.ExactSampling
