import Proof.CaseAnalysis.FinalFuelRepin
import Proof.CaseAnalysis.FinalRoundEmitter
import Proof.CaseAnalysis.FinalSeedEngine

namespace NearCubicWires.RepairSource.CloseoutFinal.C10EngineFuelSeam

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.SelectedRecoveryIntegration
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## Section 1  Two envelopes: polylogarithmic, and quasi-linear -/

/-! ## Section 2  The two number-theoretic bridges -/

/-! ## Section 4  Every other stage sees only `q(N)`, and is polylogarithmic -/

/-! ## Section 5  The prologue's fuel, split into its quasi-linear and polylog halves -/

/-! ## Section 6  The fit: degree TWO -/

/-! ## Section 7  The composition: the real call loop at the RE-PINNED field -/


end NearCubicWires.RepairSource.CloseoutFinal.C10EngineFuelSeam
