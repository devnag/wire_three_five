import Proof.Wire_3_5.Primitive.Writers.ThrDataTabs
import Proof.Wire_3_5.Primitive.Writers.DataBlank

/-! # PA (d): the THR data stage, part 2: the stage as one run (`thrData_step`)

P3:3049-3050 and P3:3068-3084 (see `ThrDataIface`): the THR stage is `Data`'s stage with the SYM tables replaced by
the tuple's ONE table: C6's fill and the cell, PA's verified `setupW` (the request split, mode `true`), `thrTableM a` docked on the SYM slots (`thrT`) and `carTableM` on the carrier slots (`carT`), the collection of the
counts `thrCounts` (the carriers' sizes, then `|tupleG Cs|`), the masked reset.

* `thrTabsM` / **`thrTabs_step`**; `collectT` / **`collectT_spec`**; `coreT`, **`thrDataM`**, `thrCoreCost`;
* **`thrData_step`**: the run from the framed THR request (the `ThrDataStage.run` shape).

Paper quantities of the main type: the tuple's table, the carriers' tables and the THR pool's slice lengths. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrData
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-! ## The three table stages -/

section Tabs

end Tabs

/-! ## The collection -/

def thrC : List (Fin (DS + 1) × Fin (DS + 1)) := [(sSym 0 0, sSym 0 5)]

section Col

end Col

/-! ## The stage as one run -/

section Run

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.ThrData
