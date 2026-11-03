import Proof.SourceAssembly.SourceRequestSelKeptS
import Proof.SourceAssembly.SourceRequestSelDistinct
import Proof.SourceAssembly.SourceSkelKeptW2

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
namespace NearCubicWires.SourceRequest.SelKeptSite
noncomputable section

section site
variable (selector : CyclicChoice.Laws) (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔡" => NearCubicWires.SourceSkeleton.FirstW.dSite selector xtra mask packets rows sources gamma hg hh p

end site

end
end NearCubicWires.SourceRequest.SelKeptSite
end

