import HiddenCircuits.Compression
import HiddenCircuits.LocalFilter
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def states0 : Fin 1 → State 4 0 := ![⟨∅, by decide⟩]

theorem states0_bijective : Function.Bijective states0 := by decide +kernel

noncomputable def enum0 : Fin 1 ≃ State 4 0 := Equiv.ofBijective states0 states0_bijective

def complementIndex0 : Fin 1 → Fin 1 := ![0]



def states1 : Fin 4 → State 4 1 := ![⟨{0}, by decide⟩, ⟨{1}, by decide⟩, ⟨{2}, by decide⟩, ⟨{3}, by decide⟩]

theorem states1_bijective : Function.Bijective states1 := by decide +kernel

noncomputable def enum1 : Fin 4 ≃ State 4 1 := Equiv.ofBijective states1 states1_bijective

def complementIndex1 : Fin 4 → Fin 4 := ![3, 2, 1, 0]



def states2 : Fin 6 → State 4 2 := ![⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{0, 3}, by decide⟩, ⟨{1, 2}, by decide⟩, ⟨{1, 3}, by decide⟩, ⟨{2, 3}, by decide⟩]

theorem states2_bijective : Function.Bijective states2 := by decide +kernel

noncomputable def enum2 : Fin 6 ≃ State 4 2 := Equiv.ofBijective states2 states2_bijective

def complementIndex2 : Fin 6 → Fin 6 := ![5, 4, 3, 2, 1, 0]



def states3 : Fin 4 → State 4 3 := ![⟨{0, 1, 2}, by decide⟩, ⟨{0, 1, 3}, by decide⟩, ⟨{0, 2, 3}, by decide⟩, ⟨{1, 2, 3}, by decide⟩]

theorem states3_bijective : Function.Bijective states3 := by decide +kernel

noncomputable def enum3 : Fin 4 ≃ State 4 3 := Equiv.ofBijective states3 states3_bijective

def complementIndex3 : Fin 4 → Fin 4 := ![3, 2, 1, 0]



def states4 : Fin 1 → State 4 4 := ![⟨{0, 1, 2, 3}, by decide⟩]

theorem states4_bijective : Function.Bijective states4 := by decide +kernel

noncomputable def enum4 : Fin 1 ≃ State 4 4 := Equiv.ofBijective states4 states4_bijective

def complementIndex4 : Fin 1 → Fin 1 := ![0]



def tracks0 : Fin 1 → Fin 0 → Fin 4 := ![![]]

theorem tracks0_mem : ∀ a b, tracks0 a b ∈ (states0 a).val := by decide +kernel

theorem tracks0_mono : ∀ a, StrictMono (tracks0 a) := by decide +kernel

theorem enum0_track (a : Fin 1) (b : Fin 0) : (enum0 a).track b = tracks0 a b := by
  exact (congrFun (Finset.orderEmbOfFin_unique (states0 a).property (tracks0_mem a) (tracks0_mono a)) b).symm

def tracks1 : Fin 4 → Fin 1 → Fin 4 := ![![0], ![1], ![2], ![3]]

theorem tracks1_mem : ∀ a b, tracks1 a b ∈ (states1 a).val := by decide +kernel

theorem tracks1_mono : ∀ a, StrictMono (tracks1 a) := by decide +kernel

theorem enum1_track (a : Fin 4) (b : Fin 1) : (enum1 a).track b = tracks1 a b := by
  exact (congrFun (Finset.orderEmbOfFin_unique (states1 a).property (tracks1_mem a) (tracks1_mono a)) b).symm

def tracks2 : Fin 6 → Fin 2 → Fin 4 := ![![0, 1], ![0, 2], ![0, 3], ![1, 2], ![1, 3], ![2, 3]]

theorem tracks2_mem : ∀ a b, tracks2 a b ∈ (states2 a).val := by decide +kernel

theorem tracks2_mono : ∀ a, StrictMono (tracks2 a) := by decide +kernel

theorem enum2_track (a : Fin 6) (b : Fin 2) : (enum2 a).track b = tracks2 a b := by
  exact (congrFun (Finset.orderEmbOfFin_unique (states2 a).property (tracks2_mem a) (tracks2_mono a)) b).symm

def tracks3 : Fin 4 → Fin 3 → Fin 4 := ![![0, 1, 2], ![0, 1, 3], ![0, 2, 3], ![1, 2, 3]]

theorem tracks3_mem : ∀ a b, tracks3 a b ∈ (states3 a).val := by decide +kernel

theorem tracks3_mono : ∀ a, StrictMono (tracks3 a) := by decide +kernel

theorem enum3_track (a : Fin 4) (b : Fin 3) : (enum3 a).track b = tracks3 a b := by
  exact (congrFun (Finset.orderEmbOfFin_unique (states3 a).property (tracks3_mem a) (tracks3_mono a)) b).symm

def tracks4 : Fin 1 → Fin 4 → Fin 4 := ![![0, 1, 2, 3]]

theorem tracks4_mem : ∀ a b, tracks4 a b ∈ (states4 a).val := by decide +kernel

theorem tracks4_mono : ∀ a, StrictMono (tracks4 a) := by decide +kernel

theorem enum4_track (a : Fin 1) (b : Fin 4) : (enum4 a).track b = tracks4 a b := by
  exact (congrFun (Finset.orderEmbOfFin_unique (states4 a).property (tracks4_mem a) (tracks4_mono a)) b).symm

theorem states0_complement : ∀ j, (states0 j).complement = states4 (complementIndex0 j) := by decide +kernel

theorem states1_complement : ∀ j, (states1 j).complement = states3 (complementIndex1 j) := by decide +kernel

theorem states2_complement : ∀ j, (states2 j).complement = states2 (complementIndex2 j) := by decide +kernel

theorem states3_complement : ∀ j, (states3 j).complement = states1 (complementIndex3 j) := by decide +kernel

theorem states4_complement : ∀ j, (states4 j).complement = states0 (complementIndex4 j) := by decide +kernel


end HiddenCircuits.Small
