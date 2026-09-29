import Proof.CaseAnalysis.FinalModeNativeStageFields
import Proof.CaseAnalysis.FinalThresholdNaturalRowPrint

open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter NearCubicWires.SupplierPrime
open NearCubicWires.SupplierRadix NearCubicWires.SourceInterfaces
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.RepairSource.CloseoutRawRows
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.ComponentwisePolynomial (CircuitMonomial)
open NearCubicWires.RepairSource (EightSources)
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdEstimateRowJoin

open C10ThresholdParityRow C10ThresholdNaturalSum C10ThresholdNaturalRowPrint
open C10SupplierCall (bank)
open C10TailComposeUniform (Atoms pcppOf)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (siteCalls)

noncomputable section

/-! ## §1 A.13.10's four-fold sum, as the LIST the summation engine eats -/

/-! ## §2 The width the record must pay -/

/-! ## §3 The payload words, and the word the engine reads -/

/-! ## §4 A.13.10's numerator on the C.10 band, in binary at width `w` -/

/-! ## §5 The crossing no name search can make -/

/-! ## §6 The route's own estimate, printed by an existing machine -/


end
end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdEstimateRowJoin
