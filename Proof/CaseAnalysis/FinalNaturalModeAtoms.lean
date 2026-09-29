import Proof.CaseAnalysis.FinalSiteWireEnvelope
import Proof.CaseAnalysis.RowsEstimatorParityThreshold

/-!
C10 selects one carried circuit class for a whole witness. Systematic parity
is compiled into that same class (paper.tex:611-626,1427-1434,4292-4306).
This module proves actual site-call mode provenance and exact native maps.
It does not select a supplier, claim a physical run, or alter resource caps.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires NearCubicWires.SupplierPipeline
open NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairSource NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10SiteWireEnvelope
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
open NearCubicWires.RepairSource.SelectedRecoveryIntegration

namespace NearCubicWires.RepairSource.CloseoutFinal.C10NaturalModeAtoms
noncomputable section


end
end NearCubicWires.RepairSource.CloseoutFinal.C10NaturalModeAtoms
