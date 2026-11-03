import Lean
import Proof.Wire_3_5.Primitive.SeedFix.SWt3Base
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SymFront3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.UnionMachine.NumsC7
import Proof.Wire_3_5.UnionMachine.NumsPh3
import Proof.Wire_3_5.Primitive.SeedFix.SWt4Base


noncomputable section
set_option maxRecDepth 120000


/-! # T3 SWt, part 4: **the top tables' writer** `swT x hx l : SWParts.SWtT l`

At a SYM request: the SYM front (`front_runA`: every filled slot's scan word
`natWord bottomCount ++ (frame (ofFn top) ++ tabSeg)` on `sS j`, the empty slots blank, the region past the data
blank), then `tW` (every register cleared, `topW` at each slot): `sO j = frame (topJ k j)` (**`slot_step`**,
**`tops_run`**), every head `0`, every register `0`, the residue the front's. The capacity `K_t·X^{D_t}`, the steps
and residue `C_t·X^{D_t'}` (**`tRun`**), and **`swT`**.

Paper quantity of the main type: the SYM call's framed top tables (the `symWords`, kind `1`; P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.SWt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.WireExponent3_5.UnionMachine.NumsA NearCubicWires.SupplierPipeline
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound

section Gate
variable (x : ℕ) (hx : DataDock.DT + 7 ≤ x)

variable (l : Literals)

/-- **The top tables' machine** at a gate: the SYM front, then `tW`. -/
noncomputable def tM (F : GateFree l) :=
  Composition.machine (FinalPass.SymFront.frontM x (hx3 x hx) l F) (tW x hx).toProg.compile

/-- The capacity's coefficient and exponent. -/
noncomputable def KcT (F : GateFree l) : ℕ := FinalPass.SymFront.KF l F + FinalPass.SymFront.CF l F + 10
noncomputable def DkT (fe : ℕ) : ℕ := FinalPass.SymFront.DF l fe + FinalPass.SymFront.DFs l fe
/-- The steps' and residue's coefficient and exponent. -/
noncomputable def CsT (F : GateFree l) : ℕ := FinalPass.SymFront.CF l F + 10000000 * (KcT l F + 2) ^ 2
noncomputable def DsT (fe : ℕ) : ℕ := FinalPass.SymFront.DFs l fe + 2 * DkT l fe

end Gate

end NearCubicWires.WireExponent3_5.PrimT.SWt

end
