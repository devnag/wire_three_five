import Proof.Wire_3_5.Primitive.SeedFix.C4SymKA

/-! # C4.K SYM, the stage at a call, v2 (amendment: the degree field `d := fr 3`)

"For each candidate child prefix, print its signed equation expression" (P3:3034-3035) through `alg:compiler`
(P3:1886-1906), whose precondition bounds every monomial's degree by the request's `d` (`C3Req.Pre`). `C4SymW.sym_call_run`
set `d := 0`, which the SYM batch's monomials exceed (the finding). Here the child requests carry
`d := fr 3` (the free number `h`, in the formulas `κ·β²`, above the batch's degree `O(β)`); `d` is in no compiler
field (`C3ReqIface.preW_irrel`, `postW_irrel`), so the C3 writer's fields and the machine are unchanged.

* **`sym_call_run2`**: `sym_call_run` at `d := fr 3` (same proof).

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
