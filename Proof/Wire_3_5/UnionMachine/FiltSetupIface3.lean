import Proof.Wire_3_5.Primitive.Writers.FiltSetupIface2

/-! # The FILTER-setup interface, v3: the capacity need counts the seeds, the bound is in the capacity

`FiltSetupSpec2` bounds the setup's cost by a polynomial in the eight values, without the seed index `g`
and without the capacity. It cannot be met: `g` sits in the unary register `fsSeed`, a register program learns about
a register only through `inc`, `dec` and zero tests, and `FiltReady.hin` needs the seed's index word, while
`|GapSeed P| = 2^{seedBits}` (**`seedCount_eq`**) grows like `2^{80·errExp}`. The own first stage
(`GapNums.gapNums_spec`) needs `2^{seedBits+1} ≤ cap` and costs `110·(sq cap)`. v3:

* **`FiltSetupSpec3 W`**: `FiltSetupSpec2`'s fields, with the capacity need taking the seed count
  `S = |GapSeed P|` as its last argument (`PolyBounded` in the values' sum `+ S`) and the cost bound a function of the
  capacity (`PolyBounded` in `cap`); the run from `FsIn2` (the request's head at `0`) as in v2.

Paper quantities of the main type: as `FiltSetupSpec` (the regular filter's parameters and seed, the row's labels),
with the seeds' count `|GapSeed P|` (filt:gap, P3:2029-2030). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.UnitReady NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.Emit

/-- **The seeds' count** is `2^{seedBits}` (the value `GapNums` leaves in `K 21`). -/
theorem seedCount_eq (P : GapParams) : Fintype.card (GapSeed P) = 2 ^ P.seedBits := card_gapSeed P

end NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup
