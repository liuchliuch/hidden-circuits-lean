import HiddenCircuits.Complexity.InitialRowWitness

namespace HiddenCircuits.Complexity.InitialRowEmitter
open OracleBlock TM2BooleanEncoding InitialSourceClassifier Polynomial
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

noncomputable def setup : OracleBlock 11 :=
  seq (copyOn 6 1 11 (by decide) (by decide) (by decide))
    (seq (copyOn 7 9 11 (by decide) (by decide) (by decide))
      (seq (copyOn 6 10 11 (by decide) (by decide) (by decide))
        (copyOn 5 8 11 (by decide) (by decide) (by decide))))

theorem setup_executes (g : BitString → ℕ) (x : BitString) (m H : ℕ) (stream : BitString) :
    setup.Executes g (state 0 0 x m H [] 0 0 stream) (state 0 m x m H x H m stream)
      (5*x.length+10*m+5*H+14) := by
  have h1 : (copyOn (6 : Fin 12) 1 11 (by decide) (by decide) (by decide)).Executes g
      (state 0 0 x m H [] 0 0 stream) (state 0 m x m H [] 0 0 stream) (5*m+2) := by
    convert copyOn_executes g (6 : Fin 12) 1 11 (by decide) (by decide) (by decide)
      (state 0 0 x m H [] 0 0 stream) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h2 : (copyOn (7 : Fin 12) 9 11 (by decide) (by decide) (by decide)).Executes g
      (state 0 m x m H [] 0 0 stream) (state 0 m x m H [] H 0 stream) (5*H+2) := by
    convert copyOn_executes g (7 : Fin 12) 9 11 (by decide) (by decide) (by decide)
      (state 0 m x m H [] 0 0 stream) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h3 : (copyOn (6 : Fin 12) 10 11 (by decide) (by decide) (by decide)).Executes g
      (state 0 m x m H [] H 0 stream) (state 0 m x m H [] H m stream) (5*m+2) := by
    convert copyOn_executes g (6 : Fin 12) 10 11 (by decide) (by decide) (by decide)
      (state 0 m x m H [] H 0 stream) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h4 : (copyOn (5 : Fin 12) 8 11 (by decide) (by decide) (by decide)).Executes g
      (state 0 m x m H [] H m stream) (state 0 m x m H x H m stream) (5*x.length+2) := by
    convert copyOn_executes g (5 : Fin 12) 8 11 (by decide) (by decide) (by decide)
      (state 0 m x m H [] H m stream) rfl using 1
    funext i;fin_cases i <;> simp [state]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)) using 1 <;> omega

noncomputable def program : OracleBlock 11 :=
  seq setup (seq (controls M) (seq (prefixLoop M)
    (seq (slot M (.value false)) (seq (witnessLoop M) (paddingLoop M)))))

noncomputable def bits (x : BitString) (m H : ℕ) : BitString :=
  let t := m+controlBits M.tm
  let u := t+2*x.length*symbolBits M.tm
  let w := u+symbolBits M.tm
  InitialRowFamily.controlBits M m ++ prefixBits M 0 t x ++
    InitialRowFamily.symbolBits M (.value false) 0 u ++ witnessBits M 0 w m ++
    paddingBits M m (w+m*symbolBits M.tm) (H-(2*x.length+m+1))

/-- All three variable-size traversals are actual finite loops. Only source and
target counters remain as explicitly specified metadata; every other work port
is empty and all three masters are restored. -/
theorem program_executes (g : BitString → ℕ) (x : BitString) (m H : ℕ)
    (hH : 2*x.length+m+1≤H) (stream : BitString) :
    ∃ cost, (program M).Executes g (state 0 0 x m H [] 0 0 stream)
      (state m (m+bitCount M.tm H) x m H [] 0 0 ((bits M x m H).reverse++stream)) cost ∧
      cost ≤ 5*x.length+10*m+5*H+34+
        familyBound m (m+bitCount M.tm H) (controlBits M.tm)+
        H*(familyBound m (m+bitCount M.tm H) (symbolBits M.tm)+8) := by
  let S := symbolBits M.tm
  let C := controlBits M.tm
  let pad := H-(2*x.length+m+1)
  let t := m+C
  let u := t+2*x.length*S
  let w := u+S
  let e := m+bitCount M.tm H
  have hpad : 2*x.length+(m+pad+1)=H := by dsimp [pad]; omega
  have he : w+m*S+pad*S=e := by
    dsimp [w,u,t,e,bitCount,C,S]
    nlinarith [hpad]
  have ht : t+2*x.length*S≤e := by dsimp [t,e,bitCount,C,S]; nlinarith
  have hu : u≤e := ht
  have hw : w+m*S≤e := by omega
  have h0 := setup_executes g x m H stream
  obtain ⟨cc,hc,hbc⟩ := controls_executes M g 0 m x m H x H m stream
  let a := (InitialRowFamily.controlBits M m).reverse++stream
  obtain ⟨cp,hp,hbp⟩ := prefixLoop_executes M g 0 t x m H x (m+pad+1) m a
  rw [hpad] at hp
  let b := (prefixBits M 0 t x).reverse++a
  obtain ⟨cd,hd,hbd⟩ := slot_executes M g (.value false) 0 u x m H [] (m+pad) m b
  let c := (InitialRowFamily.symbolBits M (.value false) 0 u).reverse++b
  obtain ⟨cw,hwc,hbw⟩ := witnessLoop_executes M g 0 w x m H m pad c
  simp only [Nat.zero_add] at hwc
  let d := (witnessBits M 0 w m).reverse++c
  obtain ⟨ce,hec,hbe⟩ := paddingLoop_executes M g m (w+m*S) x m H pad d
  have hr := seq_executes _ _ g h0 (seq_executes _ _ g hc
    (seq_executes _ _ g hp (seq_executes _ _ g hd (seq_executes _ _ g hwc hec))))
  refine ⟨5*x.length+10*m+5*H+14+(cc+(cp+(cd+(cw+ce+2)+2)+2)+2)+2,?_,?_⟩
  · have hf : state m (w+m*S+pad*S) x m H [] 0 0
        ((paddingBits M m (w+m*S) pad).reverse++d) =
        state m (m+bitCount M.tm H) x m H [] 0 0 ((bits M x m H).reverse++stream) := by
      rw [he]
      congr 1
      simp only [bits,a,b,c,d,t,u,w,S,C,pad,List.reverse_append,List.append_assoc]
    exact hf ▸ hr
  · have hmC := familyBound_mono C (a:=0) (c:=m) (b:=m) (d:=e) (by omega) (by dsimp [e];omega)
    have hmP := familyBound_mono S (a:=0) (c:=m) (b:=t+2*x.length*S) (d:=e) (by omega) ht
    have hmD := familyBound_mono S (a:=0) (c:=m) (b:=u) (d:=e) (by omega) hu
    have hmW := familyBound_mono S (a:=0+m) (c:=m) (b:=w+m*S) (d:=e) (by omega) hw
    have hmE := familyBound_mono S (a:=m) (c:=m) (b:=w+m*S+pad*S) (d:=e) le_rfl he.le
    change cc ≤ familyBound 0 m C at hbc
    change cp ≤ x.length*(2*familyBound 0 (t+2*x.length*S) S+8)+1 at hbp
    change cd ≤ familyBound 0 u S+2 at hbd
    change cw ≤ m*(familyBound (0+m) (w+m*S) S+7)+1 at hbw
    change ce ≤ pad*(familyBound m (w+m*S+pad*S) S+2)+1 at hbe
    have hp' := Nat.mul_le_mul_left x.length (show 2*familyBound 0 (t+2*x.length*S) S+8≤2*familyBound m e S+8 by omega)
    have hw' := Nat.mul_le_mul_left m (show familyBound (0+m) (w+m*S) S+7≤familyBound m e S+7 by omega)
    have he' := Nat.mul_le_mul_left pad (show familyBound m (w+m*S+pad*S) S+2≤familyBound m e S+2 by omega)
    change _ ≤ 5*x.length+10*m+5*H+34+familyBound m e C+H*(familyBound m e S+8)
    nlinarith [hpad]

lemma setup_queryFree : setup.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _)))
lemma program_queryFree : (program M).QueryFree :=
  seq_queryFree _ _ setup_queryFree (seq_queryFree _ _ (controls_queryFree M)
    (seq_queryFree _ _ (prefixLoop_queryFree M) (seq_queryFree _ _ (slot_queryFree M _)
      (seq_queryFree _ _ (witnessLoop_queryFree M) (paddingLoop_queryFree M)))))

end HiddenCircuits.Complexity.InitialRowEmitter
