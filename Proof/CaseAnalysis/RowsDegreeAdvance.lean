import Proof.Supplier.RowCoordinateIncrement
import Proof.Amplification.RecoveryEraseWidth
import Proof.Amplification.RecoveryTseitinRawIncrement

/-! The retained degree template advances using the existing unary scan.
The two head moves are actual transitions, so the source template returns
to the head-zero ABI required by the six metadata copies. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeAdvance
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def first := Composition.machine (RowCoordinateIncrement.shift .right) RecoveryEraseWidth.incrementMachine
def templateMachine := Composition.machine first (RowCoordinateIncrement.shift .left)

end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeAdvance
