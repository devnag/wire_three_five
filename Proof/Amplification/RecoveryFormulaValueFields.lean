import Proof.Amplification.RecoveryFormulaPayload

/-! Intermediate clause words may retain high zero bits. The already
executed balanced serializer interprets their exact original natural codes;
canonical output is produced only once at the final payload boundary. -/
namespace NearCubicWires.RepairSource.RecoveryFormulaPayload
open LocalBitMultitape RepairOrdinary RadixSemantics CanonicalBinary BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem value_code (formula : EncodedCNF) (words : List (List Bool))
    (hv : words.map value=formula.map Encodable.encode) :
    PCPTraversal.code words=balancedCNFPayload formula := by
  unfold PCPTraversal.code PCPSerializerMass.values
  rw [hv]
  rfl

end NearCubicWires.RepairSource.RecoveryFormulaPayload
