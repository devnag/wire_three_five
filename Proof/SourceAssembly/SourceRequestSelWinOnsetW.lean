import Proof.SourceAssembly.SourceRequestSelWinLoop
import Proof.SourceAssembly.SourceSkelKBound

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
open NearCubicWires.SourceFactorSel.Words NearCubicWires.SourceFactorSel.WordsHost
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
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
namespace NearCubicWires.SourceRequest.SelWinOnsetW
open NearCubicWires.SourceFactorSel NearCubicWires.SourceFactorSel.AtS
open NearCubicWires.SourceRequest.SelWinCore NearCubicWires.SourceRequest.SelWinSite NearCubicWires.SourceRequest.SelWinLoop
open NearCubicWires.SourceRequest.SelG7Spec (g7costW)
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes P1TopDown.WorkspaceSelectedAdmission.originalTapes
  P1TopDown.WorkspaceSelectedEntry.size RepairSource.SelectedRecoveryIntegration.outer

/-! ## 1. The onset over `kW` and `rBsel` -/

section w
variable (selector : CyclicChoice.Laws) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

theorem hkW (dL : Nat) (hdL : dL ≤ 58) : max 25 dL + 1 ≤ NearCubicWires.SourceSkeleton.ParamsV4.kW selector mask packets rows sources gamma hg hh p + 2 := by
  have h := NearCubicWires.SourceSkeleton.KBound.kW_ge selector mask packets rows sources gamma hg hh p
  have h2 : max 25 dL ≤ 58 := max_le (by decide) hdL
  omega

def g7OnsetW (L target tg cL dL wCs wEs : Nat) (hk : max 25 dL + 1 ≤ NearCubicWires.SourceSkeleton.ParamsV4.kW selector mask packets rows sources gamma hg hh p + 2) : Nat :=
  Classical.choose (onset_exists selector sources p packets (NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p) (NearCubicWires.SourceSteps.rBsel sources p) L target p.clauseDegree tg (NearCubicWires.SourceSkeleton.ParamsV4.kW selector mask packets rows sources gamma hg hh p) cL dL
    (WordsCost.wC (decompositionOf sources) mask + wCs) (max (WordsCost.wE (decompositionOf sources) mask) wEs) hk)

end w

section v5
variable (selector : CyclicChoice.Laws) (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔨" => NearCubicWires.SourceSkeleton.FirstW.kSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯" => NearCubicWires.SourceSkeleton.FirstW.rSite selector xtra mask packets rows sources gamma hg hh p

end v5

end
end NearCubicWires.SourceRequest.SelWinOnsetW
end
