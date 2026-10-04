import HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitterLoop
import HiddenCircuits.Complexity.PairSerialization

namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
open Complexity OracleBlock

def pairMap : Fin 3 ↪ Fin 16 := ⟨fun i=>![15,10,12] i,by decide +kernel⟩
noncomputable def pairLeft : OracleBlock 15 := PairSerialization.on pairMap
noncomputable def zeroPair : OracleBlock 15 := seq (copyOn 3 9 14 (by decide) (by decide) (by decide))
  (seq (repeatPrepend 9 10 [false]) pairLeft)
noncomputable def finish : OracleBlock 15 := seq (reverseOn 4 15 (by decide))
  (seq (copyOn 3 10 14 (by decide) (by decide) (by decide))
    (seq pairLeft (seq zeroPair (seq zeroPair (clear 3)))))

lemma pairLeft_executes (g : BitString→ℕ) (circuit : BitString) (r s n : ℕ) (mask raw : BitString) :
    pairLeft.Executes g (store circuit r s n [] [] [] [] [] mask [] raw)
      (store circuit r s n [] [] [] [] [] [] [] (pairBits mask raw)) (10*mask.length+9) := by
  convert PairSerialization.on_executes pairMap g (store circuit r s n [] [] [] [] [] mask [] raw)
    mask raw (by funext i;fin_cases i <;> rfl) using 1
  funext i;fin_cases i <;> rfl

lemma zeroPair_executes (g : BitString→ℕ) (circuit : BitString) (r s n : ℕ) (raw : BitString) :
    zeroPair.Executes g (store circuit r s n [] [] [] [] [] [] [] raw)
      (store circuit r s n [] [] [] [] [] [] [] (pairBits (List.replicate n false) raw)) (21*n+16) := by
  have hc : (copyOn (3:Fin 16) 9 14 (by decide) (by decide) (by decide)).Executes g
      (store circuit r s n [] [] [] [] [] [] [] raw)
      (store circuit r s n [] [] [] [] (List.replicate n true) [] [] raw) (5*n+2) := by
    convert copyOn_executes g (3:Fin 16) 9 14 (by decide) (by decide) (by decide)
      (store circuit r s n [] [] [] [] [] [] [] raw) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have hr : (repeatPrepend (9:Fin 16) 10 [false]).Executes g
      (store circuit r s n [] [] [] [] (List.replicate n true) [] [] raw)
      (store circuit r s n [] [] [] [] [] (List.replicate n false) [] raw) (6*n+1) := by
    convert repeatPrepend_executes g (9:Fin 16) 10 (by decide) [false]
      (store circuit r s n [] [] [] [] (List.replicate n true) [] [] raw) using 1
    · funext i;fin_cases i <;> simp [store,List.flatten_replicate_replicate]
    · simp [store]
  have hp := pairLeft_executes g circuit r s n (List.replicate n false) raw
  simp only [List.length_replicate] at hp
  convert seq_executes _ _ g hc (seq_executes _ _ g hr hp) using 1 <;> omega

lemma finish_executes (g : BitString→ℕ) {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) :
    finish.Executes g (store (circuitBits n w) r s n (output w r s).reverse [] [] [] [] [] [] [])
      (store (circuitBits n w) r s 0 [] [] [] [] [] [] [] (query w r s).encode)
      (2*(output w r s).length+58*n+55) := by
  let raw:=output w r s
  let circuit:=circuitBits n w
  have hrev : (reverseOn (4:Fin 16) 15 (by decide)).Executes g
      (store circuit r s n raw.reverse [] [] [] [] [] [] [])
      (store circuit r s n [] [] [] [] [] [] [] raw) (2*raw.length+1) := by
    convert reverseOn_executes g (4:Fin 16) 15 (by decide)
      (store circuit r s n raw.reverse [] [] [] [] [] [] []) using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have hc : (copyOn (3:Fin 16) 10 14 (by decide) (by decide) (by decide)).Executes g
      (store circuit r s n [] [] [] [] [] [] [] raw)
      (store circuit r s n [] [] [] [] [] (List.replicate n true) [] raw) (5*n+2) := by
    convert copyOn_executes g (3:Fin 16) 10 14 (by decide) (by decide) (by decide)
      (store circuit r s n [] [] [] [] [] [] [] raw) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have hp:=pairLeft_executes g circuit r s n (List.replicate n true) raw
  simp only [List.length_replicate] at hp
  have hz₁:=zeroPair_executes g circuit r s n (pairBits (List.replicate n true) raw)
  have hz₂:=zeroPair_executes g circuit r s n (pairBits (List.replicate n false) (pairBits (List.replicate n true) raw))
  rw [←query_encode] at hz₂
  have hclear : (clear (3:Fin 16)).Executes g
      (store circuit r s n [] [] [] [] [] [] [] (query w r s).encode)
      (store circuit r s 0 [] [] [] [] [] [] [] (query w r s).encode) (n+1) := by
    convert clear_executes g (3:Fin 16) (store circuit r s n [] [] [] [] [] [] [] (query w r s).encode) using 1
    · funext i;fin_cases i <;> rfl
    · simp [store]
  convert seq_executes _ _ g hrev (seq_executes _ _ g hc (seq_executes _ _ g hp
    (seq_executes _ _ g hz₁ (seq_executes _ _ g hz₂ hclear)))) using 1 <;> dsimp only [raw] <;> omega
end HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
