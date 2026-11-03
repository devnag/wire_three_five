import Proof.Packets.PhysicalParityScan
import Proof.PCP.ProjectionNormalizationSuffixRestore

/-! A paid, reusable polynomial coefficient scanner. Both the candidate and
original polynomial source cursors return exactly to their original positions.
The returned coefficient is the GF(2) parity of all matching monomials. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace PhysicalParityRestore

noncomputable def machine := CursorRestore.machine PhysicalParityScan.machine 1


end PhysicalParityRestore
end NearCubicWires.RepairSource.ProjectionNormalization
