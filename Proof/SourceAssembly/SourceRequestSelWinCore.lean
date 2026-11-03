import Proof.SourceAssembly.SourceRequestSelG7Spec
import Proof.CaseAnalysis.WitnessRationalMeaning
import Proof.Circuits.DecompositionSourceBounds
import Proof.SourceAssembly.SourceRequestSelLocalMach
import Proof.SourceAssembly.SourceRequestSelSymMach
import Proof.SourceAssembly.SourceFactorSelWordsCostSB
import Proof.CaseAnalysis.RowsOriginalClause
import Proof.CaseAnalysis.RowsOriginalPair
import Proof.PCP.PCPPQueryBounds
import Proof.PCP.PCPPQueryCachedBounds
import Proof.PCP.PCPPQueryIndexPadding

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
namespace NearCubicWires.SourceRequest.SelWinCore
open NearCubicWires.SourceFactorSel NearCubicWires.SourceFactorSel.AtS
open NearCubicWires.SourceRequest.SelG7Spec (g7costW)
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

/-! ## 1. Arithmetic -/

/-! ## 2. The call's shape counts are below the cache capacity -/

/-! ## 3. The window bundle -/

/-! ## 4. The per-mode pieces of `g7costW` -/

/-! ## 5. The two table parts -/

/-- The `n`-part plus the `q`-part. -/
def Ebd (n Sq cL dL wC wE : Nat) : Nat := 2 ^ 200 * (n + 1) ^ 25 + cL * (n + 1) ^ dL + 2 ^ 200 * (Sq + 1) ^ 25 + wC * (Sq + 1) ^ wE

theorem Ebd_le (n Sq cL dL wC wE T : Nat) (hN : 2 * (2 ^ 200 * (n + 1) ^ 25 + cL * (n + 1) ^ dL) ≤ T)
    (hS : 2 * (2 ^ 200 * (Sq + 1) ^ 25 + wC * (Sq + 1) ^ wE) ≤ T) : Ebd n Sq cL dL wC wE ≤ T := by
  unfold Ebd; omega

/-! ## 6. The windows, one at a time -/

section win

end win

/-! ## 7. The header block, the cost, and the core -/

section win2

end win2

end
end NearCubicWires.SourceRequest.SelWinCore
end
