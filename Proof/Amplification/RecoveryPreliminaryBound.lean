import Proof.Amplification.RecoveryPreliminary

/-! Coarse uniform budget for the actual two-input preparation, together
with exact retention of each native bank. This is still preparation for the
same enclosing all-code verifier, not a replacement NP-language premise. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdPreliminary
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_le (bits word : List Bool) :
    budget bits word ≤ 33554432*(bits.length+1)^2+8*word.length+32 := by
  have hb := RecoveryColdHeader.budget_le bits
  have hn : max 1 bits.length ≤ bits.length+1 := by omega
  unfold budget RecoveryColdHeaderCap.budget
  nlinarith only [hb,hn]

theorem slots_disjoint : ∀ (j : Fin 22) (k : Fin 4),witnessSlots k ≠ headerSlots j := by decide

theorem header_retained (bits word : List Bool) (cap scratch : Nat) (j : Fin 22) :
    output bits word cap scratch (headerSlots j)=RecoveryColdHeaderCap.output bits cap scratch j := by
  rw [output,install_other witnessSlots _ _ _ (by intro k; exact slots_disjoint j k)]
  exact install_slot headerSlots headerSlots_injective _ _ j

theorem witness_retained (bits word : List Bool) (cap scratch : Nat) (j : Fin 4) :
    output bits word cap scratch (witnessSlots j)=RecoveryColdWitnessCopy.output word j :=
  install_slot witnessSlots witnessSlots_injective _ _ j

def prefixLimit (width cap : Nat) (word : List Bool) := max word.length (cap*(width+2)+1)
theorem prefix_bound (width cap : Nat) (word : List Bool) :
    cap*(width+2)+1 ≤ prefixLimit width cap word := Nat.le_max_right _ _
theorem prefix_take (width cap : Nat) (word : List Bool) :
    word.take (prefixLimit width cap word)=word := List.take_of_length_le (Nat.le_max_left _ _)

end NearCubicWires.RepairOrdinary.RecoveryColdPreliminary
