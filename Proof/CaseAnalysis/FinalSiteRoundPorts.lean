import Proof.CaseAnalysis.FinalExactRecordLoop
import Proof.CaseAnalysis.FinalRoundBudget

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10SiteRoundPorts

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
  (widthAt widthPower entryWidthSchedule)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank bankAt words_append)
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The two record ports, and the exact delta one site round owes them -/

/-! ## §2 The append offset, in closed form -/

/-! ## §3 The bound that does not mention the round index -/

/-! ## §4 The round count is polynomial in `q` -/

/-! ## §5 The stage `roundFuel` omits, and the corrected round total -/


end NearCubicWires.RepairOrdinary.CloseoutFinalC10SiteRoundPorts
