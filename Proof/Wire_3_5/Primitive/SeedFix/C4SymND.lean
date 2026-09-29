import Proof.Wire_3_5.Primitive.SeedFix.C4SymNC

/-! # C4.K SYM items (c)+(i): the SYM stage from the numbers machine's run at the unary capacity

P3:2929-2941 (`ℓ = max(1, 2kh, ⌈log₂(Q+1)⌉)`, the seed `8ℓ` bits), P3:3011-3016 (the SYM tape's `n_T` states, the
counter `n_T·2^{8+8ℓ+8kh}`), P3:1200 (`dRow`): the uniform SYM stage (`sym_call_run2`) docks on `SymBig` (the numbers
machine's run of `sym_bigS`) through the links `ℓ = symSP.ell` (at `kh ≥ 1`), `kh`, `Q`, the counter and `2^{dRow}·2^{dRow}`;
its setup cost is monotone in the numbers machine's steps.

* `wrap_mono`, **`sym_stage_of_big`**.

Paper quantity of the main type: the SYM stage's run to the call's seed word within the budget `Bd`. -/

set_option autoImplicit false

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
