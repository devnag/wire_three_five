import Proof.CaseAnalysis.FiveNativeResources
import Proof.CaseAnalysis.RowsCapacityDriver
import Proof.CaseAnalysis.RowsPolynomial
import Proof.CaseAnalysis.RowsPreparationInput
import Proof.MachineModel.ClosureCompactFamily
import Proof.MachineModel.ClosureCompactMetadata
import Proof.MachineModel.ClosureRadixNative
import Proof.MachineModel.NativeFamily

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace RCFive.RowCaps
open NearCubicWires LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open ExtIncidence
open SourceInterfaces P1Closure RepairSource RepairSource.CloseoutFinal CloseoutRowsEstimator
open RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section
variable {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g)

def rawCap := 2^layout.w*(layout.degree*((Packets.pool a F g).length+1)+2)+1

def envelope : Nat :=
  letI := Packets.radix a F g layout
  (Packets.residual F+1)/2+Packets.residual F/2+(Packets.pool a F g).length+
  (exactListWord (Packets.pool a F g)).length+P1Radix.bits (Packets.pool a F g)+
  P1CompactNativeWidth.width (Packets.pool a F g) ((Packets.live F).card+1)+
  ((Packets.live F).card+1)+layout.w+rawCap a F g layout+2^(Packets.live F).card

def headerCap := 2^119*(envelope a F g layout+1)^22*2^(layout.w*((Packets.live F).card+2))

def chosen (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
    (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) :
    PCJd4d1d9d7d1fa4313_Production.RowCaps :=
  let D := NativeResources.driverCap a (r.family a) (geometryOf selector a r) layout printer
  { headerFuel := headerCap a (r.family a) (geometryOf selector a r) layout
    copyCap := 2*D+1
    descriptorReserve := (r.family a).rows.length*P1TopDownPaidPayload.tapes printer*(2*D+1)
    rawReserve := (r.raw selector a).length }

end
end RCFive.RowCaps
