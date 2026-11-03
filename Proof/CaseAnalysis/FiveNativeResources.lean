import Proof.CaseAnalysis.FiveLiveSetCaps
import Proof.Assembly.RowProduction
import Proof.CaseAnalysis.RowsEstimatorScanRun
import Proof.Hierarchy.CompetitorRecordRewind
import Proof.PCP.ProjectionRawFrame
import Proof.Rows.Plan

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace RCFive.NativeResources
open NearCubicWires LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open SupplierPipeline SupplierEstimator CanonicalFourfoldRowProgram
open SourceInterfaces P1Closure RepairSource RepairSource.CloseoutFinal
open CloseoutRowsEstimator CompetitorSelectedCount RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

variable {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g)
  (r : Packets.Row F.occurrences L) (hr : r ∈ F.rows) (facts : Packets.PacketFacts a F g r)

def beta := CompactBounds.radix a (Packets.live F) F.occurrences
def degree := min layout.degree (Packets.pool a F g).length
def precision := beta a F * (degree a F g layout * ((Packets.live F).card+1)) + ((Packets.live F).card+1)
def cutsCap := 2^(2*((Packets.live F).card+layout.w*((Packets.live F).card+2)))
def streamCap := cutsCap a F g layout * (Packets.residual F+2) * (2*precision a F g layout+3)

def driverCap (printer : WilliamsAlgorithm) := Driver.value printer ((Packets.residual F+1)/2)
  (precision a F g layout) (cutsCap a F g layout) layout.C


end
end RCFive.NativeResources
