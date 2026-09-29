import Proof.MachineModel.BankFields

/-! The actual incidence table and two copies of its last row index are the
only row-dependent native inputs. Common false backing erases the dependence
of the two scratch extents on the number of monomial occurrences. -/
namespace NearCubicWires.ExtIncidence.BankMetadata
open LocalBitMultitape RepairOrdinary
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.ExtIncidence.BankMetadata
