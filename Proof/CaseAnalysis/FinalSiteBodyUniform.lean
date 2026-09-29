import Proof.CaseAnalysis.FinalEnvelopeCounter
import Proof.CaseAnalysis.FinalMonomialPrinter

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SiteBodyUniform

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 Two frame readings of the loop bank -/

/-! ## §2 Threading one round's choice into a family -/

/-! ## §3 The round bank, and the residual -/

/-! ## §4 The residual IS `hbody`, both ranges -/

/-! ## §5 The consumer: `CallsReady`, from the prologue and the emitter -/

/-! ## §6 What one round charges the body with, tape by tape -/

end NearCubicWires.RepairSource.CloseoutFinal.C10SiteBodyUniform
