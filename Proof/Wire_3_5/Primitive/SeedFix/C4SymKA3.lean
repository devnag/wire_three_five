import Proof.Wire_3_5.Primitive.SeedFix.C4SymKA2

/-! # C4.K SYM, the stage at a call, v3 (ruling: the degree field `d` a separate number `dg`)

"`alg:compiler`" (P3:1886-1906) keeps the coefficient bits and the degree bound `d` of a request separate: the pool's
coefficient width `h` is `poly(n)` bits (carrier and gate weights are description-bounded, P3:1596-1615), so `d := h`
(`sym_call_run2`) breaks the gate budget (the finding 4). Here the child requests carry ANY degree
`dg`; `d` is in no compiler field (`C3ReqIface.preW_irrel`, `postW_irrel`), so the machine is the same uniform SYM stage.

* **`sym_call_run3`**: `sym_call_run2` at `d := dg` (same proof).

Paper quantity of the main type: the call's `seedWord` (the fixed SYM seed's samples). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapM wrapCost)

end NearCubicWires.WireExponent3_5.PrimT.C4SymW
