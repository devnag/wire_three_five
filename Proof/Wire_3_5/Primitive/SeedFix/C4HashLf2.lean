import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf
import Proof.Wire_3_5.Primitive.Writers.C3W3BudgetBase
import Proof.Wire_3_5.Primitive.Writers.C3WBudgetABase
import Proof.Wire_3_5.Primitive.Writers.ThrB7Base
import Proof.Wire_3_5.Primitive.Writers.ThrBud2Base
import Proof.Wire_3_5.Primitive.Writers.ThrDataH
import Proof.Wire_3_5.Primitive.Writers.ThrK7Base
import Proof.Wire_3_5.Primitive.Writers.ThrStrip7
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface
import Proof.Wire_3_5.Primitive.SeedFix.C4SymLfCBase
import Proof.Wire_3_5.Primitive.SeedFix.TS4WBase
import Proof.Wire_3_5.FinalPass.HashFreeBuild
import Proof.Wire_3_5.Assembly.C4ThrClosed
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.HashFree2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.C3ReqIface3
import Proof.Wire_3_5.Primitive.Writers.C3W3Leaf
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.HashLeaf
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.ThrLf1
import Proof.Wire_3_5.Primitive.SeedFix.C4KIface
import Proof.Wire_3_5.Primitive.SeedFix.C4LeafA
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypes
import Proof.Wire_3_5.Primitive.SeedFix.TS4O
import Proof.Wire_3_5.Primitive.SeedFix.TS4W
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf2Base


noncomputable section
set_option maxRecDepth 4096


/-! # The HASH part of C4Leaf (#196, (A)): `hashLeafC4_of`

The HASH twin of the `thrLeafC4_of` (P3:3105-3115: `E₄` before `F`, `c₄` after): from the HASH free numbers
(`hashFreeOk2`), PA's C3 request writers (`C3ReqLeaf3` at `c_N = K3`, `D_N = D3`), the v4 data stage (`stage4At`),
the front end `topFront3` and the numbers machine `numsW6`, the kept words writer `Wk` and three stage contracts, and
the per-family obligations (`HashSideAt`, and **(C)** `HashStepsAt` at `E₄`, `c₄`): after `fe`,
`E₄ = emax E_W (symFloor Dp)`, `CD₄ = max(CD_s, CD_W, 1)`; for every admissible `F`, `c₄`, and at every call family
the HASH stage `hashStageH` running at every THR call (`hash_at_call`).
* **`HashObl`** (the deliverable at an admissible `F`), **`hashLeafC4_of : C4K.HashLeafC4 l`**.

Paper quantity of the main type: the HASH part of the C4 leaf (the fixed hash's bits within `c₄·seedClasses E₄`). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4HL
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.HashSetH
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimT.C4Hk

/-- The HASH stage's unary degree (the THR leaf's). -/
noncomputable def hDl (l : Literals) (Dnw : ℕ) : ℕ := Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + PrimT.TS4.NDeg l

/-- The HASH stage's second unary coefficient (the THR leaf's). -/
noncomputable def hCd (l : Literals) (F : GateFree l) (Cnw : ℕ) : ℕ :=
  Cnw + 1 + 16 * (HashLeaf.tnK (PrimT.W6.thrNumsPoly l) (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F + 1) +
    PrimT.TS4.NCoef l F.cr

end NearCubicWires.WireExponent3_5.PrimT.C4HL

end
