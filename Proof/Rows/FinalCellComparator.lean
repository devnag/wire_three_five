import Proof.Rows.FinalDominanceEncoder

set_option autoImplicit false

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.ExtDecompositionBatch (Step)
open NearCubicWires.RepairOrdinary.CompetitorCountMask (mask)
open NearCubicWires.RepairSource.CloseoutFinal

namespace NearCubicWires.RepairSource.CloseoutFinal.C10CellComparator

set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The per-cell verdict is an EQUALITY of two words -/

/-! ## §2 The body machine: a streaming word comparator -/

/-! ## §3 The two words of one cell, and the tapes that stream them -/

section Words

noncomputable section

/-! ## §4 The streamed tapes and the loop driver's per-round source -/

/-! ## §5 The scan, realised -/

end

end Words


end NearCubicWires.RepairSource.CloseoutFinal.C10CellComparator
