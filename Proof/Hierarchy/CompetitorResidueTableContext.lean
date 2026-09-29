import Proof.Hierarchy.CompetitorResidueTableDock
import Proof.Hierarchy.CompetitorMatrixPlaneTable

/-! Literal docking to the existing native TableContext. The source bank
contains cross-bucket P/N contributions; residue execution itself makes no
claim that missing same-bucket contributions have already been included. -/
namespace NearCubicWires.RepairOrdinary.CompetitorResidueTableDock
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
open CompetitorPlaneStream (Cell oldWords countWords countWord)
open CompetitorResidueTable
open CompetitorPlaneTable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CompetitorResidueTableDock
