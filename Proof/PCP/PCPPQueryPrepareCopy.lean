import Proof.PCP.PCPPQueryNatural
import Proof.PCP.PCPPQuerySupport

/-! The cold query prefix physically isolates the source constructor input,
then loads a separate raw copy for the arity reader. The original isolated
frame remains at head zero for the source call. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryPrepareCopy
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (bits tail : List Bool) := PCPPQueryInput.budget bits tail+4*bits.length+3

end NearCubicWires.RepairOrdinary.PCPPQueryPrepareCopy
