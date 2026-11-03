import Lean
import Proof.Wire_3_5.Primitive.Writers.SBRunBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.SBTypes


noncomputable section
set_option maxRecDepth 4096


/-! # SB, types addition: the field phase's cost target

SB's step bound (`SBAsm.sbCost`) has four parts: X6's pipeline (`(57600(DtC+1)+10^6)·cap²`, proved), P1
(`SBTypes.SBCostStmt`), the field phase (this statement), and the register clears (`112·(3·cap+2)`, proved).

* **`SBFieldCostStmt l`**: `fieldCost cap (ellOf n) (eraseL FsB)` is within `Cf·cap^Ef` whenever `sbNeed ≤ cap`
  (the constants existential; donors: `GF2.searchCost_le`, `PrimT.tauCost_le`, the bounds in
  `UnionMachineFiltPipeLe`).

Paper quantity of the main type: SB's budget (`prim:runtime`, P3:3105-3115), the field words' cost (P3:2053-2055). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.SBTypes

/-- **The field phase's cost target**. -/
def SBFieldCostStmt (l : Literals) : Prop :=
  ∃ Cf Ef : ℕ, ∀ (F : GateFree l) (P : Shared.StarParams) (m : Mode) (wl c0 c1 nc cap : ℕ),
    sbNeed l F.cr F.filterErrDeg P m wl c0 c1 nc ≤ cap →
      SBField.fieldCost cap (ellOf P.n) ((SBField.eraseL FsB).map fun i => i.val) ≤ Cf * cap ^ Ef

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm

end
