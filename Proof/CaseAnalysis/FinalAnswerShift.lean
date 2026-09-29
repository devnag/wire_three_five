import Proof.CaseAnalysis.FinalCostAtTable
import Proof.CaseAnalysis.FinalSupplierCountStage

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10AnswerShift

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
  (rowAnswer rowDenominator)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth
  (answer denominator seedExponent rowCount_eq_two_pow rowAnswer_le_rowDenominator)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
  (widthAt widthPower one_le_widthPower widthPower_le_logScale widthConst thresholdFloor
    entryWidthSchedule partsOnset width_ge_floor)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierWalk

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 A.13.9's rescaling IS a left shift

`answer` is a floor quotient by definition.  Under the fit condition
`seedExponent <= scale` both parts of the quotient are powers of two, and the
quotient is exact: the whole answer channel is `rowAnswer` shifted left by
`scale - seedExponent` places. -/

/-! ## §2 The ROUTE-SIDE width floor

`entryWidth_floor_answer` (`Proof/CaseAnalysis/FinalSupplierWidth.lean`) is a
fact about `C10SupplierWidth.entryWidth`.  The live route's record width is
`entryWidthSchedule` (`Proof/CaseAnalysis/FinalPartsSchedule.lean`), a
DIFFERENT width, so that lemma is off-route.  These are the on-route versions,
and they carry the `+ 2` that §1's `answer_hfit` actually consumes. -/

/-! ## §4 The answer channel, on the C.10 bank, in BINARY

`round_step_of_dock` (`Proof/CaseAnalysis/FinalSupplierCountStage.lean`) lifts
any docked stage whose slots lie on the scratch band to a `Step` between two
banks.  `answer_bank_dock` (`Proof/CaseAnalysis/FinalSupplierCountStage.lean`)
is that at the UNARY `answer_dock`; this is that at the binary multiplier. -/


end NearCubicWires.RepairOrdinary.CloseoutFinalC10AnswerShift
