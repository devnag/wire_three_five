import Proof.CaseAnalysis.FinalSources
import Proof.CaseAnalysis.FinalSupplierSelect
import Proof.CaseAnalysis.FinalSupplierTable
import Proof.CaseAnalysis.FinalSupplierWidth
import Proof.CaseAnalysis.RowsEstimatorDriverBounds
import Proof.CaseAnalysis.RowsEstimatorWholeRetained

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.MatrixScoreBatch
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
open NearCubicWires.RepairOrdinary.CompetitorSelectedCount
open NearCubicWires.RepairOrdinary.CompetitorCountMask
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierExternalRow

noncomputable section

/-! ## 1. The per-row cost, and the hot bucket -/

end

/-! ## 2. The external row: `WholeRetained.run` at the C10 supplier request -/

noncomputable section

end

noncomputable section

end


end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierExternalRow
