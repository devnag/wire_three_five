import Proof.CaseAnalysis.FinalRoundEmitter
import Proof.CaseAnalysis.FinalDividerDock
import Proof.CaseAnalysis.FinalSupplierWidth

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutFinalC10DividerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.CloseoutFinal.C10SiteBodyUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The model fact: no `Step` ever blanks a tape -/

/-! ## §2 The bank on its scratch band -/

/-! ## §3 Why `Appends`'s `∀ s` forecloses the whole docked-engine library -/

/-! ## §4 The bank lift: a docked stage on the band IS a round step -/

/-! ## §4b The discipline itself: a blank band above a moving line -/

/-! ## §5 The answer channel, on the bank

`answer` (`Proof/CaseAnalysis/FinalSupplierWidth.lean`) is
`rowAnswer rows arity factors * denominator arity scale / rowDenominator rows arity factors`
-- A.13.9's ratio (`paper.tex:3158-3166`) carried to the uniform denominator. -/

/-! ## §6 The residual that composes -/


end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage
