import Proof.Wire_3_5.Primitive.Writers.ThrCap3Base

/-! # PA2 c4 THR block, piece 3 part 4: the THR numbers machine and the hash bits' program at the capacity v2

P3:2929-2941, 3011-3016 (the THR stage's thirty-nine words at the call's `Q`, `ℓ`, `n_T`, `dRow` and the free numbers),
P3:2331-2333 (the fixed hash's bits, read off the THR input), (the capacity `2·2^{⌊n/8⌋ + C} + 2`): from the fits
(`ThrFitAt`), the THR numbers machine's run `ThrBig` (`bigT_spec` at the call's own numbers, through `thrX_eq`,
`thrQ_link`, `thrNT_link`, `dRow_link`) and the hash bits' program's run (`hbX_spec`, its steps kept); at every THR call
of the gate once `C ≥ C₀` (`thr_fits2`).

* `thrBigCost`, **`thr_big_at`**, **`thr_hxe_at`**, **`thr_bigS2`**.

Paper quantities of the main types: the THR stage's words at the call's numbers; the framed hash bits `hbF`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrCap
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.PrimT.C4Set NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.ThrFam NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.PrimT

/-- The THR numbers machine's step bound (`bigT_spec`'s). -/
def thrBigCost (cap n a nc Kb fc : ℕ) : ℕ :=
  ThrNums.numsTCost cap n a nc Kb + 1 + (400 * UnaryPow.sq cap + 1 + (fc + 1 + (200 * UnaryPow.sq cap + 1 +
    400 * UnaryPow.sq cap)))

section At

end At

end NearCubicWires.WireExponent3_5.PrimAsm.ThrCap
