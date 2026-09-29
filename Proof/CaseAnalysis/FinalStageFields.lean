import Proof.CaseAnalysis.FinalExactFraction
import Proof.CaseAnalysis.FinalStageFuelBound
import Proof.CaseAnalysis.FinalSumFamilyTransport
import Proof.CaseAnalysis.FinalUnionSupplier

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness (CoordinateExpands phasePolynomial)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (CoefficientsFit siteCalls)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierAccuracyChain
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth
open NearCubicWires.RepairSource.CloseoutFinal.C10StageFuelBound
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdWidths (thresholdWidth)
open NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier
open NearCubicWires.RepairSource.CloseoutLanguage (selectedPCPP)
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.RepairSource.SelectedRecoveryIntegration (outer)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## §2 The frozen limits, and the two witnesses of the accuracy ledger -/

/-! ## §3 The three record-shape-independent semantic fields

These are SUMFAM's, at the field's verbatim type.  They are restated here (as
terms, not reproofs) so the assembly has one module to `refine` from. -/

/-! ## §4 The width and accuracy fields -- all four unconditional -/

/-! ## §5 The SCALAR-denominator supplier fields -- `StageBlock` as it stands -/

/-! ## §6 The EXACT-FRACTION supplier fields -- the four shapes EXACTFRAC pinned -/

/-! ## §7 `hfuel` -- the criterion, and the call cap that feeds it -/

end


end NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
