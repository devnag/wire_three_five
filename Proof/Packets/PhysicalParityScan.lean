import Proof.Packets.PhysicalParityReuse
import Proof.PCP.VerifierDecodingRepeatBody
import Proof.Packets.PhysicalCoefficientAlgebra

namespace NearCubicWires.RepairSource.ProjectionNormalization.PhysicalParityScan
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Clause := Fin 3 → List Bool
noncomputable def machine := RepeatMachine.machine PhysicalParityProbe.machine (fun _ _ => true)



/-- One normalized monomial support as an existing variable-length framed
record; empty auxiliary fields make the encoding independent of its width. -/
def supportRecord (support : List Bool) : Clause := ![support, [], []]

end NearCubicWires.RepairSource.ProjectionNormalization.PhysicalParityScan
