import Proof.Packets.PhysicalParity

namespace NearCubicWires.RepairSource.ProjectionNormalization.PhysicalParityReuse
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev rawSize := 2+((ClauseEquality.size+(ClauseEquality.size+ClauseEquality.size))+2)
abbrev size := rawSize+2

end NearCubicWires.RepairSource.ProjectionNormalization.PhysicalParityReuse
