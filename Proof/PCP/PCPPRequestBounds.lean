import Proof.PCP.PCPPRequestBoundary

/-! Fixed explicit polynomial bounds for the exact source-request bytes. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestBoundary
open RepairRepresentation ExecutableInterfaces CanonicalBinary RecoveryWitnessPolicy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_nat_bound (p : ℕ) : canonicalNatCodeBitBound p ≤ 5*(p+1)^5 := by
  have hone : 1 ≤ (p+1)^5 := Nat.one_le_pow _ _ (by omega)
  unfold canonicalNatCodeBitBound encodeNatBitsBound
  nlinarith [show 0 ≤ (p+1)^4*p from Nat.zero_le _]

theorem canonical_node_bound (p : ℕ) : canonicalBooleanNodeCodeBitBound p ≤ 512*(p+1)^5 := by
  have hn := canonical_nat_bound p
  have hone : 1 ≤ (p+1)^5 := Nat.one_le_pow _ _ (by omega)
  simp only [canonicalBooleanNodeCodeBitBound,taggedListBitBound]
  omega

theorem canonical_circuit_bound (p : ℕ) : canonicalBooleanCircuitCodeBitBound p ≤ 8192*(p+1)^10 := by
  have hn := canonical_nat_bound p
  have hnode := canonical_node_bound p
  have hone : 1 ≤ (p+1)^10 := Nat.one_le_pow _ _ (by omega)
  have hpower : (p+1)^5 ≤ (p+1)^10 := Nat.pow_le_pow_right (by omega) (by omega)
  have hp4 : p^4 ≤ (p+1)^4 := Nat.pow_le_pow_left (by omega) 4
  have hterm : p^4*(p*canonicalBooleanNodeCodeBitBound p+1) ≤ 513*(p+1)^10 := by
    have h5 : 1 ≤ (p+1)^5 := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ (p+1)^4*((p+1)*(512*(p+1)^5)+1) := by gcongr; omega
      _ ≤ (p+1)^4*((p+1)*(513*(p+1)^5)) := by gcongr; nlinarith
      _ = 513*(p+1)^10 := by ring
  simp only [canonicalBooleanCircuitCodeBitBound,canonicalBalancedCodeBitBound,taggedListBitBound]
  nlinarith

end NearCubicWires.RepairOrdinary.PCPPRequestBoundary
