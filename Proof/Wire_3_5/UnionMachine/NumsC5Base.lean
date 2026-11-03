import Proof.Wire_3_5.UnionMachine.NumsC4
import Proof.Wire_3_5.Primitive.Writers.CopyNat

/-! # NW phase (c), part 5: the front's run and `cProg`'s run at a request

At a request `r` of the family, from the writer's entry: `readNatM` reads `n` (the input is `frame (natWord n ++ …)`,
`NumsX.frame_split`), one step and a test read the mode bit (`mode_bit`), and `rest_run` finishes. The result: `n`,
`mOf r`, `eOf r`, `Sd.R.Tf r` in `rN`, `rM`, `rE`, `rT`, every other register as at the entry, the heads at `0`, the
streams and the cell kept.

* `fpIn_split`, `frontCost`, **`cProg_run`**.

Paper quantities of the main type: `n`, the mode, `n − k`, `T_f` at a request (P3:3044-3048). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsC
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-- The front's steps. -/
def frontCost (n : ℕ) : ℕ := (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) + 1 + (1 + 1 + (3 + 1))

section Req

end Req

end NearCubicWires.WireExponent3_5.UnionMachine.NumsC
