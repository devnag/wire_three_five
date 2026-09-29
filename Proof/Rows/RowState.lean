import Proof.Rows.Plan

/-!
# Retained, padded row states

The Header bank is common to every row, including the exhausted state. Its raw
source is the full family word and only the source head advances. Every Header
port has an explicit retained reserve. The work bank depends on the row index,
so the physical completion must establish the next key rather than reuse an
unchanging key by definition. An initially empty family retains its public pool
word without constructing unused unary metadata. No execution is asserted by
these bank definitions; `RowReady.ready_body` retains the actual completion Step.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_RowState
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

/-! ## 1. The three port blocks -/

/-! ## 2. The three blocks of one row -/

/-! ## 3. The state -/

/-! ## 4. The obligations the state alone discharges -/

/-! ### The descriptor port -/

/-! ### The Frame block at every other port -/

/-! ### The two cleanup ports -/

/-! ## 5. The cleanup slot map

`Core.mutableTapes` is the whole payload block, so `Plan.ClearBank`'s `Fin (m+1+1)` is
`Fin (tapes printer + 1 + 1)`: the payload ports, then the TRUE unary cap driver, then the
FALSE log.  The nesting is literally that of `Plan.clearInput`, so its three branches meet
these three port families without any re-indexing. -/

/-! ### Port arithmetic -/

/-! ### `Core.injective` -/

/-! ## 6. Two whole `Core` fields -/

end
end PCJ45bee56da9f34d5a_RowState

