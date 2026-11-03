import Proof.Packets.ArithmeticPacketLookup

/-! One executed substitution product: fetch the actual atom from the resident
packet table, then multiply it on the left of the running product. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionAtom
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def multiply := TapeEmbedding.machine 3
  (ReusableArithmetic.machine NormalizedMultiply.machine)
noncomputable def machine := Composition.machine ArithmeticLookup.machine multiply

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionAtom
