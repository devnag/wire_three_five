import Lean
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Transfer.LiteralSources
import Proof.Wire_3_5.Primitive.Writers.C3WBudgetA
import Proof.Wire_3_5.Primitive.Writers.C3WCall
import Proof.Wire_3_5.Primitive.Writers.C3WCostCall
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.GeoIface2
import Proof.Wire_3_5.Assembly.Split
import W3.Proof.Foundations.SourceRegistry
import Proof.Wire_3_5.Primitive.Writers.C3WBudgetABase
import Proof.Wire_3_5.Compiler.MachinePoolContract2
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceJBase
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface
import Proof.Wire_3_5.Primitive.SeedFix.C4Geo
import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymB
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrB
import Proof.Wire_3_5.Primitive.SeedFix.GeoPack


noncomputable section
set_option maxRecDepth 4096


/-! # C3 request writer, part 24: **`C3ReqLeaf2`**

The writer at every call family (`c3At`): the gate-field writers (`gateSymAt`, `gateThrAt thrDataStage2`), the
geometry writers (`sideAt`, `widthAt`, `colsAt`), the flips machine, C3a′, at the floors `EW l` and `C_D ≥ 1`.

Paper quantities of the main type: the compiler's fixed fields `preW`/`postW` of the call's request within the
preprocessing class `2^{O(Ψ)}` (P3:1886-1906, 3108). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Leaf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.PrimAsm.C3Mach NearCubicWires.WireExponent3_5.PrimAsm.C3Field
open NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.CompilerMachine

section At
variable (l : Literals) (F : GateFree l) (cN kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The halves writer. -/
noncomputable def sAt := PrimT.GeoPack.sideAt l F EGs (cGs (gate0 l F).row.cr) kclk coef A a ha le_rfl le_rfl
/-- The width writer. -/
noncomputable def wAt := PrimT.GeoPack.widthAt l F EGs (cGs (gate0 l F).row.cr) kclk coef A a ha le_rfl le_rfl
/-- The columns writer. -/
noncomputable def cAt := PrimT.GeoPack.colsAt l F EGs (cGs (gate0 l F).row.cr) kclk coef A a ha le_rfl le_rfl
/-- The SYM gate-field writer. -/
noncomputable def gsAt :=
  PrimT.C4GateSym.gateSymAt l F (EGp PrimT.C4GateSym.gsD) cGg kclk coef A a ha le_rfl le_rfl
/-- The THR gate-field writer. -/
noncomputable def gtAt :=
  PrimT.C4GateSym.gateThrAt l F (EGp (PrimT.C4GateSym.gtD PrimAsm.ThrData.thrDataStage2)) cGt kclk coef A a ha
    PrimAsm.ThrData.thrDataStage2 rfl le_rfl le_rfl

end At

end NearCubicWires.WireExponent3_5.PrimAsm.C3Leaf

end
