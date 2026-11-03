import Lean
import Proof.Wire_3_5.UnionMachine.NumsC5
import Proof.Wire_3_5.FinalPass.FpInLen
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR12
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.NumsPh2
import Proof.Wire_3_5.UnionMachine.NumsC6Base


noncomputable section
set_option maxRecDepth 4096


/-! # NW phase (c), part 6: **`phC x l : NumsPh2.PhC x l`** (the deliverable)

`cProg` per gate (`c_r`, `KT`, `ZT` of `F`), compiled; capacity need `(KT + 2c_r + 60)·2^{ZT+2}·(|fpIn|+1)^{ZT+2}`
(the width `T_f`, the star numbers' and the reader's needs, `n ≤ |fpIn|`); steps
`2000·(KT + c_r + ZT + 10)²·2^{ZT+2}·(|fpIn|+1)^{ZT+2}`; the exponent `ZT = ZTe l fe` reads `(l, fe)` only.

* `rsC_length`, **`cCost_le`**, `KnC`, `DnC`, `CsC`, `DsC`, **`phC`**.

Paper quantities of the main type: `n`, the mode, `e = n − k`, `T_f` (P3:3044-3048, P3:1188-1189). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsC
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP

section Gate
variable (x : ℕ) (l : Literals)

/-- The capacity need's coefficient. -/
noncomputable def KnC (F : GateFree l) : ℕ :=
  (FinalPass.Sd.R.KT l F + 2 * F.cr + 60) * 2 ^ (FinalPass.Sd.R.ZT l F + 2)

/-- The capacity need's degree (on `fe`). -/
noncomputable def DnC (fe : ℕ) : ℕ := FinalPass.Sd.R.ZTe l fe + 2

/-- The steps' coefficient. -/
noncomputable def CsC (F : GateFree l) : ℕ :=
  2000 * (FinalPass.Sd.R.KT l F + F.cr + FinalPass.Sd.R.ZT l F + 10) ^ 2 * 2 ^ (FinalPass.Sd.R.ZT l F + 2)

/-- The steps' degree (on `fe`). -/
noncomputable def DsC (fe : ℕ) : ℕ := FinalPass.Sd.R.ZTe l fe + 2

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsC

end
